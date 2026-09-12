// backend/smt.js
//
// Guarded-transition IR -> SMT-LIB 2, and the property definitions the
// verifier can check.
//
// The proof shape is the standard one: to prove `guards => goal` for all
// inputs, assert the guards and the NEGATED goal and ask the solver for a
// model. `unsat` means no counterexample exists, so the implication holds
// universally. `sat` means the model IS a counterexample, and it is reported.
//
// Soundness of dropped guards, stated once because it is load-bearing:
// when a guard could not be translated (an `ensure` calling helpers outside
// the fragment), it is DROPPED and the drop is reported. Dropping an
// assumption can only make a universal property harder to prove, never
// easier - we prove the property over a SUPERSET of the reachable states. So
// a PROVED verdict survives untranslated guards; what is lost is
// completeness: a property that holds only because of the ensure clause will
// come back DISPROVED with a counterexample that the ensure would have
// excluded, and the report says which guards were dropped so a human can make
// that call.
//
// The numeric abstraction, restated from lfir.js: Daml Numeric 10 is modelled
// as exact Real. Sound for division-safety, sign and ordering; NOT sound for
// exact-value equalities on paths that round. Transitions carrying rounding
// builtins are refused for equality properties rather than proved wrongly.

import {
  hasUnsupported,
  unsupportedReasons,
  instantiateFolds,
  foldLists,
  DEFAULT_BOUND,
} from './lfir.js';

// ---------------------------------------------------------------- terms->smt

/** Quote an IR variable name as an SMT-LIB symbol. */
const sym = (name) => `|${name.replace(/[|\\]/g, '_')}|`;

const OPS = new Set(['+', '-', '*', '/', 'div', 'mod', '<', '<=', '>', '>=', '=', 'not', 'and', 'or']);

/**
 * Render a term. Throws on `unsupported` - callers must have checked
 * modellability first, so reaching one here is a bug, not a report.
 */
export function termToSmt(t) {
  switch (t.k) {
    case 'num': {
      // LF numeric literals arrive as decimal strings ("0.0000000000"),
      // which SMT-LIB accepts as Real literals. Negatives need wrapping.
      const v = String(t.v);
      return v.startsWith('-') ? `(- ${v.slice(1)})` : v;
    }
    case 'str': {
      // Daml Text is modelled with the SMT-LIB THEORY OF STRINGS (cvc5 and z3
      // both implement it): text variables get sort String and text literals
      // render as string literals, so EQUAL on Text is real equality, with
      // distinct literals distinct for free. Only equality/inequality is
      // emitted; text manipulation builtins stay outside the fragment.
      // SMT-LIB escapes a double quote by doubling it.
      return `"${String(t.v).replace(/"/g, '""')}"`;
    }
    case 'bool':
      return t.v ? 'true' : 'false';
    case 'var':
      return sym(t.name);
    case 'app': {
      if (!OPS.has(t.op)) throw new Error(`smt: unknown operator ${t.op}`);
      return `(${t.op} ${t.args.map(termToSmt).join(' ')})`;
    }
    case 'ite':
      return `(ite ${termToSmt(t.c)} ${termToSmt(t.a)} ${termToSmt(t.b)})`;
    case 'record':
      throw new Error('smt: a whole record reached the emitter');
    case 'fold':
      // A fold denotes a different term at every list length, so there is
      // nothing to emit until one is fixed. Reaching here means a property
      // built a query without instantiating (instantiateFolds) - a bug in the
      // property, and one that must fail loudly rather than pick a length.
      throw new Error(
        `smt: an uninstantiated ${t.op} over \`${t.listName}\` reached the emitter`
      );
    case 'unsupported':
      throw new Error(`smt: unsupported term reached the emitter: ${t.why}`);
    default:
      throw new Error(`smt: unknown term kind ${t.k}`);
  }
}

/**
 * Infer variable sorts by position: a var used as an ite condition or as a
 * bare guard is Bool; anything under arithmetic or comparison is Real. A var
 * used both ways is a conflict and makes the query non-modellable.
 */
export function inferSorts(terms) {
  /** @type {Map<string, string>} */
  const sorts = new Map();
  const conflicts = [];

  const mark = (t, sort) => {
    if (!t || typeof t !== 'object') return;
    if (t.k === 'var') {
      const prev = sorts.get(t.name);
      if (prev && prev !== sort) conflicts.push(`${t.name} used as both ${prev} and ${sort}`);
      else sorts.set(t.name, sort);
      return;
    }
    if (t.k === 'app') {
      if (t.op === 'not' || t.op === 'and' || t.op === 'or') t.args.forEach((a) => mark(a, 'Bool'));
      else if (t.op === '=') {
        // Equality is polymorphic. A string literal on either side makes it a
        // String equality; otherwise treat both sides as Real unless a side is
        // already known Bool. Good enough for this fragment.
        const isString = t.args.some((a) => a && a.k === 'str');
        t.args.forEach((a) =>
          mark(a, isString ? 'String' : sorts.get(a.name) === 'Bool' ? 'Bool' : 'Real')
        );
      } else t.args.forEach((a) => mark(a, 'Real'));
      return;
    }
    if (t.k === 'ite') {
      mark(t.c, 'Bool');
      mark(t.a, sort);
      mark(t.b, sort);
    }
  };

  for (const { term, sort } of terms) mark(term, sort);
  return { sorts, conflicts };
}

/**
 * Build one SMT-LIB query proving `guards => goal`.
 *
 * @param {Object[]} guards  Bool terms assumed
 * @param {Object} goal      Bool term to prove
 * @returns {{script: string, vars: string[]}}
 */
export function buildQuery(guards, goal) {
  const { sorts, conflicts } = inferSorts([
    ...guards.map((g) => ({ term: g, sort: 'Bool' })),
    { term: goal, sort: 'Bool' },
  ]);
  if (conflicts.length) throw new Error(`smt: sort conflicts: ${conflicts.join('; ')}`);

  const lines = [];
  lines.push('(set-logic ALL)');
  lines.push('(set-option :produce-models true)');
  for (const [name, sort] of [...sorts.entries()].sort()) {
    lines.push(`(declare-const ${sym(name)} ${sort})`);
  }
  for (const g of guards) lines.push(`(assert ${termToSmt(g)})`);
  lines.push(`(assert (not ${termToSmt(goal)}))`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return { script: lines.join('\n') + '\n', vars: [...sorts.keys()] };
}

// ---------------------------------------------------------------- properties

/**
 * Split a transition's guards into usable and dropped. A guard containing an
 * unsupported node cannot be asserted; see the soundness note at the top.
 */
export function usableGuards(transition) {
  const used = [];
  const dropped = [];
  for (const g of [...transition.guards, ...(transition.pathConditions || [])]) {
    if (hasUnsupported(g)) dropped.push(unsupportedReasons(g).map((u) => u.why));
    else used.push(g);
  }
  return { used, dropped };
}

/**
 * Split a transition's guards into usable and dropped AT ONE LIST LENGTH.
 * Guards are instantiated first so that a guard mentioning a fold contributes
 * at that length instead of being dropped wholesale.
 */
function usableGuardsAt(transition, k) {
  const used = [];
  const dropped = [];
  for (const g of [...transition.guards, ...(transition.pathConditions || [])]) {
    const at = instantiateFolds(g, k);
    if (hasUnsupported(at)) dropped.push(unsupportedReasons(at).map((u) => u.why));
    else used.push(at);
  }
  return { used, dropped };
}

/**
 * AMOUNT CONSERVATION for a consuming choice.
 *
 * With no archived inputs the statement is the exact one it has always been -
 * archiving this contract and creating its successors preserves `amount`:
 *
 *     sum(created.amount) = this.amount
 *
 * A choice that ALSO consumes other contracts (a merge) conserves something
 * different, and answering the equation above for it would be answering a
 * question nobody asked:
 *
 *     sum(created.amount) = this.amount + sum(archived.amount)
 *
 * The second form is only stated when the archived contracts can be named the
 * SAME WAY the created amounts name them. lfir.js keys list-element symbols to
 * the list they range over, so a fold over `arg.holdings` produces
 * `arg.holdings$i.amount` and an archive loop over `arg.holdings` contributes
 * exactly those symbols. That identity is the whole content of the check: if
 * the archived inputs were modelled as a fresh family B0..Bk, the goal would
 * read `this + sum(A) = this + sum(B)`, the solver would satisfy it by making
 * them differ, and the report would carry a DISPROVED about a correct merge.
 * Hence the two guards below: an archived list must be one the created amounts
 * actually fold over, and a transition mixing two distinct lists is refused
 * rather than given a single shared length.
 *
 * Because a fold is only unrolled to a bound, the second form is checked at
 * each list length 0..bound and the verdict is PROVED-BOUNDED, not PROVED - a
 * distinct status that says nothing about longer lists (see verify.js).
 *
 * Applicability: the transition is consuming, and every create resolves an
 * `amount` field (directly, or by inheriting it from `this`).
 *
 * `notModellable` marks a refusal (the property makes sense here but the
 * translated fragment or the numeric abstraction cannot express it), as
 * opposed to plain non-applicability; verify.js reports the two differently.
 *
 * @returns {{applicable: boolean, notModellable?: boolean, why?: string,
 *   guards?: Object[], goal?: Object, dropped?: string[][],
 *   bounded?: boolean, bound?: number, listName?: string,
 *   instances?: Array<{k: number, guards: Object[], goal: Object}>}}
 */
export function amountConservation(transition) {
  if (!transition.consuming) return { applicable: false, why: 'nonconsuming choice' };

  // A choice that consumes contracts BESIDES `this` does not satisfy
  // `sum(created) = this.amount`; the true statement adds the consumed
  // contracts' amounts. When the consumed contracts are the elements of a list
  // we can name, that statement IS available (archivedInputs, below). When
  // they are not, naming them would mean inventing symbols unrelated to
  // anything the created amounts mention, which yields a spurious
  // counterexample - so refuse instead.
  if ((transition.consumesOthers || []).length) {
    const kinds = [...new Set(transition.consumesOthers.map((c) => c.effect))];
    return {
      applicable: false,
      notModellable: true,
      why:
        `the choice consumes contracts besides \`this\` (${kinds.join(', ')}) whose list the ` +
        `translation could not identify, so plain conservation is the wrong statement: it ` +
        `would have to account for the consumed contracts' amounts, and there is no symbol ` +
        `for them that the created amounts also mention`,
    };
  }

  // A create inside a per-element loop means an unknown NUMBER of created
  // contracts; no total over them can be written down at all.
  if ((transition.unmodelledLoopEffects || []).length) {
    return {
      applicable: false,
      notModellable: true,
      why: transition.unmodelledLoopEffects.map((u) => u.why).join('; '),
    };
  }

  if (transition.creates.length === 0) {
    // No creates AND untranslated parts of the body is a refusal, not a pass:
    // the archive may well have successors the walker could not see.
    if ((transition.unsupported || []).length) {
      return {
        applicable: false,
        notModellable: true,
        why:
          'no creates were recovered, and parts of the body were not translated: ' +
          transition.unsupported.map((u) => u.why).join('; '),
      };
    }
    return { applicable: false, why: 'creates nothing (pure archive or effects outside the fragment)' };
  }

  const amounts = [];
  for (const c of transition.creates) {
    let amount = c.fields.amount;
    // `create this with ...` without touching amount inherits it.
    if (!amount && c.base === 'this') amount = { k: 'var', name: 'this.amount', sort: 'Real' };
    if (!amount) return { applicable: false, why: `create of ${c.template} has no amount field` };
    amounts.push({ template: c.template, term: amount });
  }

  if ((transition.rounding || []).length) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `path uses rounding builtins [${transition.rounding.join(', ')}]; the exact-Real ` +
        `abstraction cannot prove exact equalities there`,
    };
  }

  const archived = transition.archivedInputs || [];
  const folded = new Set();
  for (const a of amounts) foldLists(a.term, folded);

  // An archived list the created amounts never fold over cannot be related to
  // them. Adding `sum(L$i.amount)` anyway would invent a family of symbols
  // nothing else constrains (a spurious counterexample); leaving it out would
  // silently assume the archived contracts carry no amount (a spurious proof).
  for (const a of archived) {
    if (folded.has(a.listName)) continue;
    return {
      applicable: false,
      notModellable: true,
      why:
        `the choice archives every element of \`${a.listName}\` (${a.effect}), but no created ` +
        `amount is built from a fold over that list, so the archived contracts' amounts cannot ` +
        `be related to anything the translation can see: stating conservation would either ` +
        `invent unrelated symbols or assume the archived contracts carry no amount`,
    };
  }

  const lists = new Set([...folded, ...archived.map((a) => a.listName)]);

  if (lists.size === 0) {
    // The exact, unbounded statement: no list is involved, so nothing here is
    // bounded and today's verdicts are unaffected.
    for (const a of amounts) {
      if (!hasUnsupported(a.term)) continue;
      return {
        applicable: false,
        notModellable: true,
        why:
          `amount of created ${a.template} is outside the translated fragment: ` +
          unsupportedReasons(a.term).map((u) => u.why).join('; '),
      };
    }
    const terms = amounts.map((a) => a.term);
    const sum = terms.length === 1 ? terms[0] : { k: 'app', op: '+', args: terms };
    const goal = { k: 'app', op: '=', args: [sum, { k: 'var', name: 'this.amount', sort: 'Real' }] };
    const { used, dropped } = usableGuards(transition);
    return { applicable: true, guards: used, goal, dropped };
  }

  if (lists.size > 1) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `the transition folds over or archives ${lists.size} distinct lists ` +
        `(${[...lists].join(', ')}); the bounded instantiation fixes ONE length at a time, ` +
        `which would leave the combinations of differing lengths unchecked`,
    };
  }

  const listName = [...lists][0];
  const bound = Number.isInteger(transition.bound) ? transition.bound : DEFAULT_BOUND;
  const archivedHere = archived.filter((a) => a.listName === listName);

  const instances = [];
  let lastDropped = [];
  for (let k = 0; k <= bound; k++) {
    const created = amounts.map((a) => ({ template: a.template, term: instantiateFolds(a.term, k) }));
    for (const c of created) {
      if (!hasUnsupported(c.term)) continue;
      return {
        applicable: false,
        notModellable: true,
        why:
          `at list length ${k}, the amount of created ${c.template} is outside the translated ` +
          `fragment: ${unsupportedReasons(c.term).map((u) => u.why).join('; ')}`,
      };
    }
    const lhsTerms = created.map((c) => c.term);
    const lhs = lhsTerms.length === 1 ? lhsTerms[0] : { k: 'app', op: '+', args: lhsTerms };

    // The archived contracts, named the way the fold named them. Same list,
    // same index, same symbol - by construction, not by agreement.
    const rhsTerms = [{ k: 'var', name: 'this.amount', sort: 'Real' }];
    if (archivedHere.length) {
      for (let i = 0; i < k; i++) {
        rhsTerms.push({ k: 'var', name: `${listName}$${i}.amount`, sort: 'Real' });
      }
    }
    const rhs = rhsTerms.length === 1 ? rhsTerms[0] : { k: 'app', op: '+', args: rhsTerms };

    const { used, dropped } = usableGuardsAt(transition, k);
    lastDropped = dropped;
    instances.push({ k, guards: used, goal: { k: 'app', op: '=', args: [lhs, rhs] }, dropped });
  }

  return {
    applicable: true,
    bounded: true,
    bound,
    listName,
    archivedLists: archivedHere.map((a) => a.listName),
    instances,
    dropped: lastDropped,
    boundedNote:
      `bounded: \`${listName}\` instantiated at every length 0..${bound} ` +
      `(${instances.length} quer${instances.length === 1 ? 'y' : 'ies'})` +
      (archivedHere.length
        ? `; the archived inputs are the same \`${listName}$<i>.amount\` symbols the fold ` +
          `ranges over, so the two sides cannot drift apart`
        : ''),
  };
}

/**
 * DIVISION SAFETY: every division denominator on the transition is nonzero
 * under the usable guards.
 */
export function divisionSafety(transition) {
  if (!transition.divisions.length) return { applicable: false, why: 'no division on this transition' };

  // Adjudicate PER DENOMINATOR rather than refusing the whole transition.
  //
  // The all-or-nothing form of this check was hiding real results: on a
  // Canton perb calculation, 19 of 20 denominators translate cleanly and one
  // does not, and refusing the transition reported all 20 as unadjudicated.
  // Each denominator is an independent obligation, so the honest thing is to
  // prove the ones we can and name the ones we cannot. `coverage` carries
  // that split to the report, which never prints a bare PROVED when some
  // denominator went unchecked.
  const checkable = [];
  const skipped = [];
  for (const d of transition.divisions) {
    if (hasUnsupported(d.denominator)) {
      skipped.push(unsupportedReasons(d.denominator).map((u) => u.why).join('; '));
    } else {
      checkable.push(d);
    }
  }

  if (checkable.length === 0) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `all ${skipped.length} denominator(s) are outside the fragment: ` +
        `${[...new Set(skipped)].join('; ')}`,
    };
  }

  const goal = {
    k: 'app',
    op: 'and',
    args: checkable.map((d) => ({
      k: 'app',
      op: 'not',
      args: [{ k: 'app', op: '=', args: [d.denominator, { k: 'num', v: '0' }] }],
    })),
  };
  const { used, dropped } = usableGuards(transition);

  // Denominators recovered from an unrolled fold step exist only for the
  // element indices the unrolling reached. Proving those says nothing about
  // element `bound` of a longer list, so the verdict is bounded, not PROVED.
  // (The denominators of the enumerated indices are checked in ONE query:
  // unlike conservation, division safety is a conjunction of independent
  // obligations, not a statement whose shape depends on the list's length.)
  const fromFold = checkable.filter((d) => d.fold);
  const bounded = fromFold.length > 0;
  const bound = Number.isInteger(transition.bound) ? transition.bound : DEFAULT_BOUND;
  const foldedLists = [...new Set(fromFold.map((d) => d.fold))];

  return {
    applicable: true,
    guards: used,
    goal: goal.args.length === 1 ? goal.args[0] : goal,
    dropped,
    ...(bounded
      ? {
          bounded: true,
          bound,
          listName: foldedLists.join(', '),
          boundedNote:
            `bounded: ${fromFold.length} of ${checkable.length} checked denominator(s) come ` +
            `from fold steps over ${foldedLists.map((l) => `\`${l}\``).join(', ')} unrolled to ` +
            `length ${bound}; denominators at element indices >= ${bound} were never built, ` +
            `so nothing is claimed about longer lists`,
        }
      : {}),
    coverage: {
      checked: checkable.length,
      total: transition.divisions.length,
      skipped: [...new Set(skipped)],
    },
  };
}

export const PROPERTIES = {
  'amount-conservation': {
    fn: amountConservation,
    describe:
      'consuming choices preserve the amount field in total: sum(created) = this.amount, ' +
      'plus the amounts of the contracts they archive when those can be identified (bounded)',
  },
  'division-safety': {
    fn: divisionSafety,
    describe: 'no division on the transition can divide by zero under its guards',
  },
};
