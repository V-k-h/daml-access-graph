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
//
// ---------------------------------------------------------------------------
// UNINTERPRETED FUNCTIONS, and exactly what they cost. This one is asymmetric,
// unlike the dropped-guard argument above, so it is spelled out in full.
//
// Some operations on a guard's path are opaque to the translation: Daml Text
// manipulation (trim, explode, implode, append) has no counterpart in the
// arithmetic-plus-Strings fragment the emitter speaks. Rather than dropping
// the whole conjunct, such an operation is replaced by an UNINTERPRETED
// FUNCTION SYMBOL of the same arity: `isNonBlankText this.id` becomes
// `(|Shared:isNonBlankText@<pkg>| |this.id|)`, declared with `declare-fun` and
// otherwise unconstrained.
//
// WHAT THAT DOES TO THE MODEL CLASS. The real function f is ONE function of
// its signature. The uninterpreted symbol F ranges over ALL functions of that
// signature, f included. Every model of the original system therefore extends
// to a model of the abstracted one (interpret F as f), so the set of models
// GROWS. Two consequences, and they point in opposite directions:
//
//   * `unsat` on the abstracted query means NO function of that signature
//     admits a counterexample - in particular the real one does not. So an
//     unsat still PROVES the property. UFs are sound for PROVED, for exactly
//     the same reason dropping a guard is: we quantified over a superset.
//
//   * `sat` means SOME function of that signature admits a counterexample.
//     The witnessing interpretation may be one the real function never takes -
//     a "counterexample" in which `isNonBlankText` returns True for the empty
//     string. So a DISPROVED over a query that mentions a UF is NOT a proof of
//     a bug: it may be an artifact of the abstraction. Every such verdict must
//     carry that caveat, and verify.js attaches it from `buildQuery`'s
//     reported `ufs` list. Silence here would be the worst failure this
//     pipeline can have: a fabricated finding presented as a real one.
//
// IDENTITY MATTERS. Two different Daml functions must never share a UF symbol:
// equating them is a CONSTRAINT, not a relaxation, and constraints can make an
// unsat spurious - unsound for PROVED, the one direction we cannot lose. The
// translator therefore names a UF by its fully qualified value name PLUS the
// id of the package that defines it (see lfir.js: ufName), and a name used at
// two different signatures is a sort conflict that makes the whole query
// non-modellable rather than being reconciled.
//
// WHAT A UF IS NOT: it is not a fallback for "the translator did not look".
// Anything whose obstacle has not been identified stays `unsupported` with its
// reason, and the conjunct is dropped as before.
//
// THE RESULT SORT is usually inferred from the position the application is used
// in, because the translator reads compiled expressions and not their types.
// That is sound for the same reason the abstraction is: what must exist is ONE
// interpretation of the symbol reproducing the real function, and the Daml
// value domains an abstraction can hide - Text, lists of Text, code points,
// timestamps - are all countable, so each injects into the Real (or String)
// the position pins. A Bool position can only arise where the real expression
// was a Bool, since the position comes from the compiled code's own use of it.

import {
  T,
  hasUnsupported,
  unsupportedReasons,
  instantiateFolds,
  foldLists,
  rewriteVars,
  DEFAULT_BOUND,
} from './lfir.js';

// ---------------------------------------------------------------- terms->smt

/** Quote an IR variable name as an SMT-LIB symbol. */
const sym = (name) => `|${name.replace(/[|\\]/g, '_')}|`;

const OPS = new Set(['+', '-', '*', '/', 'div', 'mod', '<', '<=', '>', '>=', '=', 'not', 'and', 'or']);

/**
 * Render a term. Throws on `unsupported` - callers must have checked
 * modellability first, so reaching one here is a bug, not a report.
 *
 * `realNumerals` renders an integer-looking numeric literal as a REAL literal
 * (`0` -> `0.0`). SMT-LIB types a bare numeral as Int, and cvc5 coerces it in
 * arithmetic and equality contexts but NOT as an `ite` branch against a Real:
 * `(ite c |x.$value| 0)` - the shape the Optional encoding produces for
 * `fromOptional 0 x` - is rejected outright as "branches must have comparable
 * type". buildQuery passes true because every numeric position it emits is
 * Real (inferSorts has no rule that yields Int), and it is the only caller
 * that owns a whole script. The default stays off so that a caller rendering a
 * genuinely Int-sorted term - tests/differential.test.js generates div/mod
 * terms over Int variables - still gets numerals.
 */
export function termToSmt(t, realNumerals = false) {
  const rec = (x) => termToSmt(x, realNumerals);
  switch (t.k) {
    case 'num': {
      // LF numeric literals arrive as decimal strings ("0.0000000000"),
      // which SMT-LIB accepts as Real literals. Negatives need wrapping.
      let v = String(t.v);
      if (realNumerals && !v.includes('.')) v = `${v}.0`;
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
    case 'party':
      // An uninterpreted constant of the `Party` sort: a bare symbol, exactly
      // like a nullary declare-fun.
      return sym(t.name);
    case 'app': {
      if (!OPS.has(t.op)) throw new Error(`smt: unknown operator ${t.op}`);
      return `(${t.op} ${t.args.map(rec).join(' ')})`;
    }
    case 'uf':
      // An uninterpreted application. A nullary one is applied as a bare
      // symbol, which is what SMT-LIB does with a 0-arity declare-fun.
      return t.args.length
        ? `(${sym(t.name)} ${t.args.map(rec).join(' ')})`
        : sym(t.name);
    case 'ite':
      return `(ite ${rec(t.c)} ${rec(t.a)} ${rec(t.b)})`;
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
 * Infer sorts by UNIFICATION over positions.
 *
 * Every position that must share a sort is unified: a var occurrence with the
 * variable's sort class, the operands of an `=` with each other, the branches
 * of an `ite` with the ite's own sort, an uninterpreted application's argument
 * i with that symbol's i-th parameter class. Positions with a forced sort
 * (a Bool under `not`, a Real under arithmetic, a String literal, a UF's
 * declared result sort) pin their class to it. A class pinned to two different
 * sorts is a CONFLICT and makes the query non-modellable, which is the only
 * honest answer: the emitter would otherwise produce an ill-sorted script and
 * the solver's complaint would arrive as a mysterious SOLVER-ERROR.
 *
 * Unification replaced a single left-to-right pass whose `=` rule guessed
 * Real unless it saw a string literal. The guess was fine while Text appeared
 * only next to literals; an uninterpreted predicate over a text field pins
 * that field to String from a position the old pass reached AFTER it had
 * already committed, which is exactly the order dependence unification
 * removes.
 *
 * A class that ends up pinned to nothing defaults to Real, as before.
 *
 * @param {Array<{term: Object, sort: string}>} terms  `sort` may be a concrete
 *   sort name or any other string, which is then just a class identifier: a
 *   caller that wants a term's sort INFERRED rather than forced passes a fresh
 *   identifier per term (see nonNegativeFields).
 * @param {Array<[string, string]>} [seeds]  DECLARED sorts, `[varName, sort]`,
 *   read out of the compiled package's field types rather than inferred from a
 *   position. They are applied AFTER every term has been walked and only to
 *   variables the terms actually mention, which makes them unable to move an
 *   answer: a class a position already pinned stays pinned (unifying two
 *   concrete roots records a conflict and changes nothing), and a variable no
 *   term mentions is not declared, so the emitted variable list is unchanged.
 *   A declaration can therefore only type a class that nothing else typed -
 *   which is exactly the gap the emitter used to fill with its Real default.
 * @returns {{sorts: Map<string,string>, conflicts: string[],
 *   ufs: Map<string, {args: string[], ret: string}>, pinned: Set<string>}}
 */
export function inferSorts(terms, seeds = []) {
  // `Party` is an UNINTERPRETED sort: no literals, no arithmetic, nothing but
  // equality. Nothing else in the emitter produces a Party-sorted position, so
  // adding it here cannot move any position that used to resolve to Real.
  const CONCRETE = new Set(['Bool', 'Real', 'Int', 'String', 'Party']);
  /** union-find parent pointers; a concrete sort name is its own root */
  const parent = new Map();
  const conflicts = [];
  /** var names in encounter order, so the declaration list is stable */
  const varNames = [];
  const seenVar = new Set();
  /** uf name -> arity, to catch a symbol used at two different arities */
  const ufArity = new Map();
  const ufNames = [];

  const find = (x) => {
    let r = x;
    while (parent.has(r) && parent.get(r) !== r) r = parent.get(r);
    let c = x;
    while (parent.has(c) && parent.get(c) !== c) {
      const next = parent.get(c);
      parent.set(c, r);
      c = next;
    }
    return r;
  };
  const node = (id) => {
    if (!parent.has(id)) parent.set(id, id);
    return find(id);
  };
  const union = (a, b) => {
    const ra = node(a);
    const rb = node(b);
    if (ra === rb) return;
    const ca = CONCRETE.has(ra);
    const cb = CONCRETE.has(rb);
    if (ca && cb) {
      conflicts.push(`${describe(a)} used as both ${ra} and ${rb}`);
      return;
    }
    // a concrete sort always becomes the root, so a class carries its sort
    if (ca) parent.set(rb, ra);
    else parent.set(ra, rb);
  };
  const describe = (id) =>
    id.startsWith('v:') ? id.slice(2) : id.startsWith('u:') ? `\`${id.slice(2)}\`` : id;

  let fresh = 0;
  const walk = (t, id) => {
    if (!t || typeof t !== 'object') return;
    switch (t.k) {
      case 'var':
        if (!seenVar.has(t.name)) {
          seenVar.add(t.name);
          varNames.push(t.name);
        }
        union(id, `v:${t.name}`);
        return;
      case 'party':
        // Declared like any other constant, but PINNED to Party rather than
        // inferred: a party constant has no position that could type it, and
        // defaulting it to Real would let the solver do arithmetic on it.
        if (!seenVar.has(t.name)) {
          seenVar.add(t.name);
          varNames.push(t.name);
        }
        union(`v:${t.name}`, 'Party');
        union(id, `v:${t.name}`);
        return;
      case 'num':
        union(id, 'Real');
        return;
      case 'str':
        union(id, 'String');
        return;
      case 'bool':
        union(id, 'Bool');
        return;
      case 'uf': {
        const prev = ufArity.get(t.name);
        if (prev === undefined) {
          ufArity.set(t.name, t.args.length);
          ufNames.push(t.name);
        } else if (prev !== t.args.length) {
          conflicts.push(
            `uninterpreted symbol \`${t.name}\` applied to ${prev} and ${t.args.length} arguments`
          );
        }
        if (t.sort) union(`u:${t.name}`, t.sort);
        union(id, `u:${t.name}`);
        t.args.forEach((a, i) => {
          const slot = `u:${t.name}#${i}`;
          // A DECLARED parameter sort (a builtin whose LF type is fixed) pins
          // the class, so it propagates out to the argument rather than being
          // decided by whatever the argument happened to be used as elsewhere.
          if (t.argSorts && t.argSorts[i]) union(slot, t.argSorts[i]);
          walk(a, slot);
        });
        return;
      }
      case 'app': {
        if (t.op === 'not' || t.op === 'and' || t.op === 'or') {
          union(id, 'Bool');
          t.args.forEach((a) => walk(a, 'Bool'));
        } else if (t.op === '=') {
          // Equality is polymorphic: its operands share ONE sort, whatever it
          // turns out to be. A fresh class stands for it until something pins
          // it down; unpinned it defaults to Real, as it always did.
          union(id, 'Bool');
          const group = `=${fresh++}`;
          t.args.forEach((a) => walk(a, group));
        } else if (['<', '<=', '>', '>='].includes(t.op)) {
          union(id, 'Bool');
          t.args.forEach((a) => walk(a, 'Real'));
        } else {
          union(id, 'Real');
          t.args.forEach((a) => walk(a, 'Real'));
        }
        return;
      }
      case 'ite':
        walk(t.c, 'Bool');
        walk(t.a, id);
        walk(t.b, id);
        return;
      default:
        return;
    }
  };

  for (const { term, sort } of terms) walk(term, sort);

  // Declared sorts last, so a position always wins over a declaration. See the
  // seeds note above for why that ordering is what keeps seeding conservative.
  for (const [name, sort] of seeds) {
    if (!CONCRETE.has(sort) || !seenVar.has(name)) continue;
    union(`v:${name}`, sort);
  }

  const resolve = (id) => {
    const r = node(id);
    return CONCRETE.has(r) ? r : 'Real';
  };
  const sorts = new Map();
  /**
   * The variables whose sort came from a POSITION rather than from the default.
   *
   * `resolve` answers Real for a class nothing pinned, which is the right
   * default for the emitter but is NOT evidence: a party field, a contract id
   * and a date all reach an unconstrained class and all come back Real. A
   * property that needs to know whether a term really is numeric - asserting
   * `>= 0` of a Text field would be a fabricated obligation, not a check -
   * asks this set instead of reading `sorts`.
   */
  const pinned = new Set();
  for (const name of varNames) {
    sorts.set(name, resolve(`v:${name}`));
    if (CONCRETE.has(node(`v:${name}`))) pinned.add(name);
  }
  const ufs = new Map();
  for (const name of ufNames) {
    ufs.set(name, {
      args: Array.from({ length: ufArity.get(name) }, (_, i) => resolve(`u:${name}#${i}`)),
      ret: resolve(`u:${name}`),
    });
  }
  return { sorts, conflicts, ufs, pinned };
}

/**
 * Build one SMT-LIB query proving `guards => goal`.
 *
 * @param {Object[]} guards  Bool terms assumed
 * @param {Object} goal      Bool term to prove
 * @returns {{script: string, vars: string[]}}
 */
export function buildQuery(guards, goal) {
  const { sorts, conflicts, ufs } = inferSorts([
    ...guards.map((g) => ({ term: g, sort: 'Bool' })),
    { term: goal, sort: 'Bool' },
  ]);
  if (conflicts.length) throw new Error(`smt: sort conflicts: ${conflicts.join('; ')}`);

  const lines = [];
  lines.push('(set-logic ALL)');
  lines.push('(set-option :produce-models true)');
  // The uninterpreted sort, declared only when the query actually uses it, so
  // every script this pipeline used to emit is byte-for-byte what it was.
  if ([...sorts.values()].includes('Party')) lines.push('(declare-sort Party 0)');
  for (const [name, sort] of [...sorts.entries()].sort()) {
    lines.push(`(declare-const ${sym(name)} ${sort})`);
  }
  // Uninterpreted symbols: declared, never constrained. See the header for
  // why an unsat over these still proves the property and a sat does not
  // refute it.
  for (const [name, sig] of [...ufs.entries()].sort()) {
    lines.push(`(declare-fun ${sym(name)} (${sig.args.join(' ')}) ${sig.ret})`);
  }
  for (const g of guards) lines.push(`(assert ${termToSmt(g, true)})`);
  lines.push(`(assert (not ${termToSmt(goal, true)}))`);
  lines.push('(check-sat)');
  lines.push('(get-model)');
  return {
    script: lines.join('\n') + '\n',
    vars: [...sorts.keys()],
    // The names verify.js needs to decide whether a DISPROVED has to carry
    // the abstraction caveat.
    ufs: [...ufs.keys()],
  };
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

// --------------------------------------------------------- shape helpers

const TRUE = { k: 'bool', v: true };

/** Conjunction of a list of Bool terms, flattened to nothing when empty. */
function allOf(terms) {
  const real = terms.filter((t) => !(t && t.k === 'bool' && t.v === true));
  if (real.length === 0) return TRUE;
  return real.length === 1 ? real[0] : { k: 'app', op: 'and', args: real };
}

/** Disjunction of a list of Bool terms. */
function anyOf(terms) {
  if (terms.length === 0) return { k: 'bool', v: false };
  return terms.length === 1 ? terms[0] : { k: 'app', op: 'or', args: terms };
}

/**
 * `a => b`, written with the operators the emitter speaks (there is no `=>`
 * in OPS). An antecedent that is statically true disappears.
 *
 * This is how a PER-CREATE obligation is stated. Asserting the branch
 * conditions of every create as GUARDS instead would be unsound in the one
 * direction that matters: two creates on opposite sides of an `if` would
 * contribute `c` and `not c` to the same assumption set, the query would be
 * trivially unsat, and every such transition would come back PROVED without
 * anything having been checked.
 */
function implies(a, b) {
  if (a && a.k === 'bool' && a.v === true) return b;
  return { k: 'app', op: 'or', args: [{ k: 'app', op: 'not', args: [a] }, b] };
}

/**
 * Rounding builtins whose SMT-LIB counterpart is not sign-compatible with
 * Daml's, and therefore the only ones that make a SIGN property unsound.
 *
 * The argument, in full, because the refusal is narrower than the one
 * amount-conservation makes and the difference has to be defensible:
 *
 *   * ROUND_NUMERIC, CAST_NUMERIC, SHIFT_NUMERIC and NUMERIC_TO_INT64 have no
 *     term at all. None of them is in BINOP, EXACT_CONVERSION,
 *     IDENTITY_BUILTIN or TEXT_UF_BUILTIN, so translateBuiltinApp refuses them
 *     and the field that used one carries an `unsupported` node. Such a field
 *     is SKIPPED by this property and counted in coverage - it is never proved
 *     non-negative - so no composition of exact-Real arithmetic with a real
 *     rounding step can reach a checked obligation. That, and not a claim
 *     about rounding preserving signs, is what makes the narrower refusal
 *     sound: `round x - x` would indeed break a naive sign argument, and it is
 *     also exactly the shape that never survives translation.
 *
 *   * MOD_INT64 does have a term. SMT-LIB's `mod` is the Euclidean remainder,
 *     which is ALWAYS non-negative; Daml's `mod` takes the sign of the
 *     dividend, so `mod (-7) 2` is -1 where the model says 1. A model that
 *     proves `>= 0` there would be proving something false about the code.
 *
 *   * DIV_INT64 has a term too. SMT-LIB's `div` is Euclidean and Daml's
 *     truncates toward zero; they agree in sign on every input we could
 *     construct, but the two definitions are genuinely different functions and
 *     a sign proof resting on which of them the solver implements is not an
 *     argument we are prepared to write down. It is refused with MOD_INT64.
 *
 * The refusal is on the TRANSITION, not the field, because these two also
 * reach the GUARDS, where they are assumptions rather than obligations and a
 * wrong one is unsound in the same direction.
 */
const SIGN_UNSAFE_ROUNDING = new Set(['DIV_INT64', 'MOD_INT64']);

/** Operators whose result is a number by construction. */
const ARITHMETIC_OPS = new Set(['+', '-', '*', '/', 'div', 'mod']);

/**
 * Is this term KNOWN to denote a number?
 *
 * Not "does the emitter give it sort Real" - it gives everything it cannot
 * place sort Real, by design, because Real is the emitter's default and the
 * default has to be something. A party field, a contract id, a date and a
 * text all reach an unconstrained class and all come back Real, and asserting
 * `>= 0` of one of them would not be a weak check but a FABRICATED one: the
 * solver would answer about a symbol that stands for nothing numeric, and a
 * DISPROVED would name a "negative owner".
 *
 * So evidence is required, and there are exactly three kinds:
 *
 *   * a numeric literal, which the LF decoder read out of an INT64 or NUMERIC
 *     literal and nothing else;
 *   * an arithmetic operator, which only a numeric builtin produces;
 *   * a variable some OTHER position in the transition pinned to Real -
 *     compared with `<`, added to something, divided by. That is the compiled
 *     code using the field as a number, which is the same fact a type would
 *     have told us, read off the code instead.
 *
 * Anything else is skipped and SAID to be skipped.
 *
 * This is the FALLBACK path. The package's declared field types are now
 * decoded (dalf.js) and threaded onto the transition as `symbolTypes`, and a
 * field the declaration covers is decided from the declaration. Positional
 * evidence stays because the declaration does not reach everywhere: a created
 * field computed from a fetched contract, from a list element, or from a
 * struct has no projection path from `this` or `arg` to walk, and the way the
 * code uses it is then the only fact available. Neither path ever guesses from
 * the field's NAME.
 */
function numericEvidence(term, isRealVar) {
  if (!term || typeof term !== 'object') return false;
  switch (term.k) {
    case 'num':
      return true;
    case 'app':
      return ARITHMETIC_OPS.has(term.op);
    case 'var':
      return isRealVar(term.name);
    case 'uf':
      return term.sort === 'Real';
    case 'ite':
      // Both branches share one sort, so evidence from either types the whole.
      return numericEvidence(term.a, isRealVar) || numericEvidence(term.b, isRealVar);
    default:
      return false;
  }
}

/**
 * Sorts a field can have that make `>= 0` NOT A QUESTION ABOUT IT.
 *
 * The distinction this set draws is the point of decoding the field types at
 * all. Before them a Party field and a Numeric field the translation could not
 * read were indistinguishable: both came back "not known to be numeric", both
 * were counted as unchecked obligations, and a transition assigning six party
 * and text fields reported as a refusal over six unanswered questions. Five of
 * those six were never questions. A field the package declares to be a Party,
 * a Text, a Date, a ContractId, a Bool or a nested data type is not an
 * obligation of this property that went unchecked - it is not an obligation.
 *
 * `record` covers every nominal data type (records, variants, enums alike);
 * none of them is a number, and the field-type walk enters one only when it
 * has to go deeper, never to decide a leaf.
 *
 * The asymmetry to keep in mind: this set EXCLUDES work. Getting a sort wrong
 * here would silently drop a real obligation, so it is driven only by the
 * declared type and never by a heuristic - an unfollowable path yields no
 * entry at all and the field stays in the unknown class where it was before.
 */
const NON_NUMERIC_SORTS = new Set(['party', 'text', 'time', 'cid', 'bool', 'record']);

/**
 * The one thing excluding a field can hide, said on every verdict that excludes
 * one. See `nestedRecords`.
 */
const NESTED_RECORD_CAVEAT =
  'some of the excluded fields are nested RECORDS assigned whole; this property checks the ' +
  'fields a create assigns and does not descend into them, so numeric fields INSIDE those ' +
  'records are not examined here and this verdict says nothing about them';

/** Declared coarse sort -> the SMT sort it seeds inferSorts with. */
const DECLARED_SMT_SORT = new Map([
  ['numeric', 'Real'],
  ['text', 'String'],
  ['bool', 'Bool'],
  ['party', 'Party'],
]);

/**
 * The sort the compiled package DECLARES for a field term, or null.
 *
 * Only two shapes can carry a declaration: a symbol, which is a projection
 * path whose sort was read off the DefDataType records, and an `ite` whose
 * branches agree (both sides of a conditional assignment are the same field
 * type, and disagreeing branches say the walk got something wrong, so they
 * answer null rather than picking one). An arithmetic term is deliberately NOT
 * consulted here: that is positional evidence, and it is judged by
 * numericEvidence so the two sources stay distinguishable in the report.
 */
function declaredSort(term, types) {
  if (!types || types.size === 0 || !term || typeof term !== 'object') return null;
  switch (term.k) {
    case 'var':
      return types.get(term.name) || null;
    case 'ite': {
      const a = declaredSort(term.a, types);
      const b = declaredSort(term.b, types);
      if (a && b) return a === b ? a : null;
      return a || b;
    }
    default:
      return null;
  }
}

/**
 * NON-NEGATIVITY: every numeric field of every created contract is `>= 0`
 * under the guards that hold on the path that creates it.
 *
 * Per FIELD, the way division-safety is per denominator: one field the
 * translation could not read must not hide the ones it could, and the
 * coverage split is what keeps a partial answer from printing as a whole one.
 *
 * WHICH FIELDS ARE OBLIGATIONS. Three classes, and the three-way split is what
 * the decoded field types bought:
 *
 *   * DECLARED NUMERIC, or shown numeric by the way the transition uses it:
 *     an obligation, and checked.
 *   * DECLARED NON-NUMERIC: not an obligation at all. Excluded from the
 *     coverage denominator and reported separately, because counting a Party
 *     field as an unanswered question overstates the gap and turns whole
 *     transitions into refusals over nothing.
 *   * NEITHER: unknown. Skipped and said to be skipped, exactly as before.
 *     The sub-case worth naming is a field that IS declared numeric but whose
 *     value the translation could not read; it is still skipped, and it is
 *     counted apart from the unknowns because it is a real gap rather than a
 *     question that was never asked.
 *
 * WHAT IS STILL NOT AN OBLIGATION. Only fields the create ASSIGNS are checked.
 * A `create this with amount = ...` inherits every field it does not mention,
 * and an inherited field's value is the pre-state's, about which this
 * transition establishes nothing at all - `this.owner >= 0` is not a property
 * of the choice. Those fields are disclosed on the verdict rather than
 * counted: the declaration says what they ARE, not what this choice did to
 * them, and a property about the pre-state is a different property.
 *
 * AND WHAT IS STILL NOT ASSUMED. The CREATED template's own `ensure` clause is
 * not a guard here. The ledger enforces it at create time, so assuming it
 * would make every such obligation vacuously true - the check would be
 * "assuming the create succeeds, does the create succeed?". Not assuming it is
 * what lets a create that CAN abort show up as a finding. The EXERCISED
 * contract's ensure is a different matter and is assumed, because that
 * contract already exists on the ledger and its precondition already held.
 */
export function nonNegativeFields(transition) {
  const creates = transition.creates || [];
  if (!creates.length) {
    return { applicable: false, why: 'creates nothing (pure archive or effects outside the fragment)' };
  }

  const signUnsafe = (transition.rounding || []).filter((r) => SIGN_UNSAFE_ROUNDING.has(r));
  if (signUnsafe.length) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `the path uses [${signUnsafe.join(', ')}], whose SMT-LIB counterpart is Euclidean while ` +
        `Daml's truncates toward zero; the two disagree in sign on negative operands (SMT-LIB's ` +
        `\`mod\` is never negative, Daml's takes the sign of the dividend), so a sign proof over ` +
        `this transition would be a proof about a different function`,
    };
  }

  // SORT EVIDENCE, gathered from the transition ITSELF and never from the
  // goal: unifying a field with the `>= 0` obligation would pin it to Real and
  // make every field look numeric, which is the failure this whole function
  // exists to avoid. Each field term gets a FRESH class so the field terms are
  // not unified with each other either.
  const evidence = [];
  let fresh = 0;
  for (const g of [...transition.guards, ...(transition.pathConditions || [])]) {
    evidence.push({ term: g, sort: 'Bool' });
  }
  for (const c of creates) {
    for (const p of c.path || []) evidence.push({ term: p, sort: 'Bool' });
    for (const t of Object.values(c.fields || {})) evidence.push({ term: t, sort: `field$${fresh++}` });
  }
  for (const d of transition.divisions || []) {
    evidence.push({ term: d.denominator, sort: `denominator$${fresh++}` });
  }
  // The DECLARED sorts of this transition's symbols, read out of the compiled
  // package's DefDataType records by lfir.js. Absent on a hand-built
  // transition, and an absent map simply means every field falls back to
  // positional evidence - the behaviour before the types were decoded.
  const declared = transition.symbolTypes instanceof Map ? transition.symbolTypes : new Map();
  // Declarations also SEED the sort inference, which is where they pay off a
  // second time: a symbol the package declares Numeric pins its class, so a
  // field assigned from it is Real-sorted and the positional path agrees with
  // the declared one instead of contradicting it. Seeds are applied after
  // every position has been walked and only to symbols the terms mention, so
  // they cannot move a sort a position already decided (see inferSorts).
  const seeds = [];
  for (const [name, sort] of declared) {
    const smtSort = DECLARED_SMT_SORT.get(sort);
    if (smtSort) seeds.push([name, smtSort]);
  }
  const { sorts, pinned } = inferSorts(evidence, seeds);
  const isRealVar = (name) => pinned.has(name) && sorts.get(name) === 'Real';

  const checkable = [];
  const skipped = [];
  /** Fields the package declares NON-numeric: not obligations, not gaps. */
  const excluded = [];
  /**
   * How many of those are NESTED RECORDS, which is the one exclusion that
   * hides something. `create M with contractData = <a whole record>` assigns a
   * field that is not a number, so it is correctly not an obligation - but the
   * record it assigns may itself contain numeric fields, and this property
   * checks the fields a create ASSIGNS rather than descending into a record
   * assigned whole. Excluding it silently would let "no numeric field here"
   * read as "no numeric field anywhere in what was created", so the count is
   * carried onto the verdict in both the applicable and the non-applicable
   * case.
   */
  let nestedRecords = 0;
  /** Declared numeric, but the value itself is outside the fragment. */
  let skippedNumeric = 0;
  /**
   * Value outside the fragment AND no declaration: unreadable, so whether it
   * was even a numeric question is unknown. Counted apart from the class below
   * because the two lead to different verdicts - an unreadable field is a
   * REFUSAL (NOT-MODELLABLE: the property applies but cannot be expressed),
   * while a readable field nothing types as a number is NOT-APPLICABLE. That
   * distinction is the pipeline's whole vocabulary for "we could not" versus
   * "there was nothing to"; collapsing them would report refusals as absences.
   */
  let skippedUnreadable = 0;
  /** Readable, but nothing - declaration or position - says it is a number. */
  let skippedUnknown = 0;
  let total = 0;
  for (const c of creates) {
    const usablePath = [];
    const droppedPath = [];
    for (const p of c.path || []) {
      if (hasUnsupported(p)) droppedPath.push(p);
      else usablePath.push(p);
    }
    for (const [name, term] of Object.entries(c.fields || {})) {
      const at = `${c.template}.${name}`;
      // The CREATED record's own declaration first: this property is about the
      // field a contract is given, so the created template's record is the
      // direct answer, and it is the only one available when the assigned
      // value left the fragment. The value side is consulted only where the
      // created record could not be resolved (a target declared in a package
      // the archive does not carry). Both are reads of the same compiled
      // package, so where both answer they answer the same thing.
      const sort = (c.fieldSorts && c.fieldSorts[name]) || declaredSort(term, declared);

      // Declared non-numeric: excluded BEFORE anything else, including the
      // readability test. Whether the translation could read a Party field's
      // value does not matter - `>= 0` is not a question about it either way,
      // so it is not counted as an obligation in any state.
      if (sort && NON_NUMERIC_SORTS.has(sort)) {
        excluded.push(`${at} (${sort})`);
        if (sort === 'record') nestedRecords++;
        continue;
      }

      total++;
      if (hasUnsupported(term)) {
        // NOT assumed non-negative: an unreadable field is an unanswered
        // question, and it is reported as one.
        const why = unsupportedReasons(term).map((u) => u.why).join('; ');
        if (sort === 'numeric') {
          skippedNumeric++;
          skipped.push(
            `${at} is declared numeric by the package but its value is outside the fragment: ${why}`
          );
        } else {
          skippedUnreadable++;
          skipped.push(`${at} is outside the fragment: ${why}`);
        }
        continue;
      }
      if (sort === 'numeric' || numericEvidence(term, isRealVar)) {
        checkable.push({ at, term, path: usablePath, droppedPath });
        continue;
      }
      skippedUnknown++;
      skipped.push(
        `${at} is not known to be numeric: the package's field types do not cover the term it is ` +
          `assigned (no projection path from \`this\` or \`arg\` that the data-type records could ` +
          `be walked along) and nothing in the transition uses it as a number, so it is left ` +
          `unchecked rather than asserted about`
      );
    }
  }

  if (checkable.length === 0) {
    if (total === 0) {
      if (excluded.length) {
        // Every assigned field has a declared non-numeric type. This is a
        // genuine NOT-APPLICABLE - the property does not concern this
        // transition - and not a refusal: nothing here went unanswered.
        return {
          applicable: false,
          why:
            `every field the create(s) assign has a declared NON-numeric type ` +
            `(${[...new Set(excluded)].join(', ')}), so non-negativity is not a property of ` +
            `this transition` + (nestedRecords ? `; ${NESTED_RECORD_CAVEAT}` : ''),
        };
      }
      return { applicable: false, why: 'no create resolves a field the translation could read' };
    }
    // Every unchecked field was READABLE and simply not known to be a number:
    // nothing was refused, so this is non-applicability. One unreadable field
    // among them makes it a refusal instead - see skippedUnreadable.
    if (skippedUnknown === total) {
      return {
        applicable: false,
        why: `none of the ${total} resolved created field(s) is known to be numeric`,
      };
    }
    return {
      applicable: false,
      notModellable: true,
      why: `all ${total} resolved created field(s) are unchecked: ${[...new Set(skipped)].join('; ')}`,
    };
  }

  const goal = allOf(
    checkable.map((o) =>
      implies(allOf(o.path), { k: 'app', op: '>=', args: [o.term, { k: 'num', v: '0' }] })
    )
  );
  const { used, dropped } = usableGuards(transition);
  for (const o of checkable) {
    for (const p of o.droppedPath) dropped.push(unsupportedReasons(p).map((u) => u.why));
  }

  const inherits = creates.filter((c) => c.base === 'this' || c.base === 'arg');
  const notes = [];
  if (inherits.length) {
    notes.push(
      `${inherits.length} create(s) copy a record (\`create ${inherits[0].base} with ...\`) and ` +
        `inherit every field they do not name; only the fields they DO name are checked, because ` +
        `an inherited field's value is the pre-state's and this choice establishes nothing about it`
    );
  }
  if ((transition.rounding || []).length) {
    notes.push(
      `the path carries rounding builtins [${transition.rounding.join(', ')}]; none of them ` +
        `produces a term, so every field built through one is among the skipped ones above`
    );
  }
  if (excluded.length) {
    const shown = [...new Set(excluded)];
    notes.push(
      `${shown.length} assigned field(s) are NOT obligations of this property: the package ` +
        `declares them non-numeric (${shown.slice(0, 6).join(', ')}` +
        `${shown.length > 6 ? `, and ${shown.length - 6} more` : ''}). They are excluded from ` +
        `the coverage denominator rather than reported as unchecked, which they never were` +
        (nestedRecords ? `; ${NESTED_RECORD_CAVEAT}` : '')
    );
  }
  if (skippedNumeric) {
    notes.push(
      `${skippedNumeric} field(s) the package declares NUMERIC could not be checked because the ` +
        `value assigned is outside the translated fragment; those are real gaps, listed in the ` +
        `coverage split`
    );
  }

  return {
    applicable: true,
    guards: used,
    goal,
    dropped,
    notes,
    /**
     * `total` counts OBLIGATIONS, which is why declared non-numeric fields are
     * not in it: they are reported in `excluded` instead. The three skip
     * counters split the remainder - `skippedNumeric` is a question we know we
     * could not answer, `skippedUnreadable` a value we could not read at all,
     * `skippedUnknown` a value we read but nothing types as a number - and
     * they sum with `checked` to `total`.
     */
    coverage: {
      checked: checkable.length,
      total,
      skipped: [...new Set(skipped)],
      excluded: excluded.length,
      excludedFields: [...new Set(excluded)],
      excludedNestedRecords: nestedRecords,
      skippedNumeric,
      skippedUnreadable,
      skippedUnknown,
    },
  };
}

// ------------------------------------------------------- create-authority

/**
 * Re-root one of the CREATED template's party paths onto the CREATING
 * contract, using the create's own field assignments and nothing else.
 *
 * `create T with admin = this.admin` is the only kind of evidence that relates
 * two party references in this model. A signatory path `this.admin` of T is
 * rewritten to `this.admin` of the creating contract because the assignment
 * says so; a signatory path of T whose field the create assigns from anything
 * else - an expression, a fetched contract, a field the walk did not see -
 * comes back null, and the caller leaves that create unadjudicated rather than
 * relating the two by their shared FIELD NAME. Field names in two templates
 * are not known to denote the same ledger Party, which is exactly the
 * limitation src/analysis.js reports rather than asserts.
 *
 * A dotted path (`this.governance.approver`) is re-rooted at its FIRST
 * segment, since that is the field the create assigns.
 */
function relinkPartyPath(path, create, owningTemplate) {
  const dot = path.indexOf('.');
  if (dot < 0) return null;
  // Paths from a template's own signatory clause are rooted at that template's
  // parameter, which analysePartyExpr names `this`. Anything else (a choice
  // argument of some other choice) cannot appear and is not guessed at.
  if (path.slice(0, dot) !== 'this') return null;
  const rest = path.slice(dot + 1);
  const field = rest.split('.')[0];
  const tail = rest.slice(field.length);
  const fields = create.fields || {};
  if (Object.prototype.hasOwnProperty.call(fields, field)) {
    const assigned = fields[field];
    return assigned && assigned.k === 'var' ? `${assigned.name}${tail}` : null;
  }
  // Not assigned: the create copies a record wholesale and inherits it.
  if (create.base === 'this') {
    // `create this with ...` only type-checks against the SAME template, so a
    // mismatch means the walk mis-identified the record; refuse instead.
    return create.template === owningTemplate ? `this.${rest}` : null;
  }
  if (create.base === 'arg') return `arg.${rest}`;
  return null;
}

/**
 * CREATE AUTHORITY: every party required to sign a contract this choice
 * creates is covered by the authority the choice acts with.
 *
 * The acting authority of a sub-transaction of an exercise is the signatories
 * of the contract exercised on plus the controllers of the choice, so the
 * obligation, per created contract and per required signatory `s`, is
 *
 *     present(s)  =>  OR over authority a of ( present(a) AND s = a )
 *
 * with `present` the condition under which a conditional stakeholder clause
 * actually contributes that party (see lfir.js: PartyRef). Equality is
 * equality of UNINTERPRETED PARTY CONSTANTS: the solver has no way to make two
 * of them equal except through an equation the translation asserted, and the
 * only equations asserted are the create's own field assignments. So a
 * required signatory that could not be linked does not become "some other
 * party" and does not become "the same party" - it stays unconstrained, the
 * obligation stays unprovable, and this property reports the create as
 * UNCHECKED with the reason rather than answering about it.
 *
 * DIRECTION OF EVERY APPROXIMATION, because they must point opposite ways:
 *   * the required set is used only when the created template's clause was
 *     walked EXACTLY (over-approximating is safe, missing one is not);
 *   * the authority set is whatever was recovered, which under-approximates
 *     (inventing an authority would authorise a create the ledger rejects).
 * An under-approximated authority makes a DISPROVED weaker, not a PROVED
 * wrong, and the verdict says which parts were left out.
 *
 * WHAT A PARTY CONSTANT DENOTES, since a stakeholder field is not always one
 * party: it denotes the SET of parties the field reference stands for - a
 * singleton for `Party`, the list's parties for `[Party]`, the Optional's for
 * `Optional Party`. Read that way the obligation is still exactly right:
 * `s = a` says the two references denote the SAME set, which implies the
 * required set is contained in the authority. It is a SUFFICIENT condition,
 * never a necessary one, so it can leave a real coverage unproved (reported as
 * a DISPROVED with its caveats) but can never approve one that does not hold.
 */
export function createAuthority(transition) {
  const creates = transition.creates || [];
  if (!creates.length) {
    return { applicable: false, why: 'creates nothing (pure archive or effects outside the fragment)' };
  }

  const table = transition.templateSignatories;
  if (!table || typeof table.get !== 'function') {
    return {
      applicable: false,
      notModellable: true,
      why:
        'the transition carries no package-level signatory table, so the required signatories of ' +
        'a created template cannot be looked up (extractTransitions attaches one)',
    };
  }

  const own = transition.signatories || { refs: [], exact: false, why: 'not analysed' };
  const ctrl = transition.controllers || { refs: [], exact: false, why: 'not analysed' };
  const authority = [
    ...own.refs.map((r) => ({ ...r, from: `a signatory of ${transition.template}` })),
    ...ctrl.refs.map((r) => ({ ...r, from: `a controller of ${transition.choice}` })),
  ];
  if (!authority.length) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `no party reference could be recovered from the signatories of ${transition.template} or ` +
        `the controllers of ${transition.choice}, so there is no authority set to check against: ` +
        `${[own.why, ctrl.why].filter(Boolean).join('; ')}`,
    };
  }

  const covers = (s) =>
    anyOf(
      authority.map((a) =>
        allOf([a.presence, { k: 'app', op: '=', args: [T.party(s), T.party(a.path)] }])
      )
    );

  const checked = [];
  const skipped = [];
  for (const c of creates) {
    const target = table.get(c.template);
    if (!target) {
      skipped.push(
        `create of ${c.template}: no template of that name is declared in this package (it is ` +
          `declared in a dependency, or the create's type could not be named), so its required ` +
          `signatories are unknown`
      );
      continue;
    }
    if (target.ambiguous) {
      skipped.push(`create of ${c.template}: ${target.why}`);
      continue;
    }
    if (!target.exact) {
      skipped.push(
        `create of ${c.template}: its signatory clause was only partly walked (${target.why}), so ` +
          `the required signatory set is not known to be complete and proving the recovered part ` +
          `would claim more than was checked`
      );
      continue;
    }
    if (!target.refs.length) {
      skipped.push(`create of ${c.template}: its signatory clause yielded no party reference at all`);
      continue;
    }

    const link = (path) => relinkPartyPath(path, c, transition.template);
    const obligations = [];
    let unlinked = null;
    for (const req of target.refs) {
      const s = link(req.path);
      if (s === null) {
        unlinked = req.path;
        break;
      }
      const presence = rewriteVars(req.presence, link);
      if (hasUnsupported(presence)) {
        unlinked = req.path;
        break;
      }
      obligations.push(implies(presence, covers(s)));
    }
    if (unlinked !== null) {
      skipped.push(
        `create of ${c.template}: its required signatory \`${unlinked}\` is assigned something ` +
          `this translation cannot relate to a party of the creating contract, and two field ` +
          `names are NOT assumed to denote the same ledger Party, so the create is left unchecked`
      );
      continue;
    }

    const usablePath = (c.path || []).filter((p) => !hasUnsupported(p));
    checked.push({ template: c.template, goal: implies(allOf(usablePath), allOf(obligations)) });
  }

  if (!checked.length) {
    return {
      applicable: false,
      notModellable: true,
      why: `no create could be adjudicated: ${[...new Set(skipped)].join('; ')}`,
    };
  }

  const { used, dropped } = usableGuards(transition);
  const notes = [
    'party identity comes ONLY from the create\'s own field assignments: two party fields are ' +
      'equal in this model exactly when the compiled create assigned one from the other, never ' +
      'because they share a name',
  ];
  if (!ctrl.refs.length) {
    notes.push(
      `the acting authority is an UNDER-approximation: the controllers of ${transition.choice} ` +
        `contributed nothing (${ctrl.why}), so only ${transition.template}'s signatories were ` +
        `used - which can only make a goal harder to prove, and makes a DISPROVED here possibly ` +
        `an artifact of the missing controllers rather than a real authorisation gap`
    );
  }
  if (!own.exact) {
    notes.push(
      `${transition.template}'s own signatory clause was only partly walked (${own.why}); the ` +
        `authority uses the references that were recovered, which under-approximates it in the ` +
        `same safe direction`
    );
  }

  return {
    applicable: true,
    guards: used,
    goal: allOf(checked.map((c) => c.goal)),
    dropped,
    notes,
    coverage: { checked: checked.length, total: creates.length, skipped: [...new Set(skipped)] },
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
  'non-negative-fields': {
    fn: nonNegativeFields,
    describe:
      'every numeric field a created contract is given is >= 0 under the guards on the path ' +
      'that creates it; a field the translation cannot read, or cannot show to be numeric, is ' +
      'reported unchecked rather than assumed',
  },
  'create-authority': {
    fn: createAuthority,
    describe:
      "every party required to sign a contract the choice creates is covered by the choice's " +
      'acting authority (the signatories of the contract exercised on, plus the controllers); ' +
      'parties are uninterpreted constants related only by the create\'s own field assignments',
  },
};
