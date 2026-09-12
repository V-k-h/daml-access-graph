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

import { hasUnsupported, unsupportedReasons } from './lfir.js';

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
 * AMOUNT CONSERVATION for a consuming choice: archiving this contract and
 * creating its successors preserves the `amount` field in total:
 *
 *     sum(created.amount) = this.amount
 *
 * Applicability: the transition is consuming, and every create resolves an
 * `amount` field (directly, or by inheriting it from `this`).
 *
 * `notModellable` marks a refusal (the property makes sense here but the
 * translated fragment or the numeric abstraction cannot express it), as
 * opposed to plain non-applicability; verify.js reports the two differently.
 *
 * @returns {{applicable: boolean, notModellable?: boolean, why?: string, guards?: Object[], goal?: Object, dropped?: string[][]}}
 */
export function amountConservation(transition) {
  if (!transition.consuming) return { applicable: false, why: 'nonconsuming choice' };
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
    if (hasUnsupported(amount)) {
      return {
        applicable: false,
        notModellable: true,
        why:
          `amount of created ${c.template} is outside the translated fragment: ` +
          unsupportedReasons(amount).map((u) => u.why).join('; '),
      };
    }
    amounts.push(amount);
  }

  if (transition.rounding.length) {
    return {
      applicable: false,
      notModellable: true,
      why:
        `path uses rounding builtins [${transition.rounding.join(', ')}]; the exact-Real ` +
        `abstraction cannot prove exact equalities there`,
    };
  }

  const sum = amounts.length === 1 ? amounts[0] : { k: 'app', op: '+', args: amounts };
  const goal = { k: 'app', op: '=', args: [sum, { k: 'var', name: 'this.amount', sort: 'Real' }] };
  const { used, dropped } = usableGuards(transition);
  return { applicable: true, guards: used, goal, dropped };
}

/**
 * DIVISION SAFETY: every division denominator on the transition is nonzero
 * under the usable guards.
 */
export function divisionSafety(transition) {
  if (!transition.divisions.length) return { applicable: false, why: 'no division on this transition' };
  const bad = transition.divisions.find((d) => hasUnsupported(d.denominator));
  if (bad) {
    return {
      applicable: false,
      notModellable: true,
      why: `a denominator is outside the fragment: ${unsupportedReasons(bad.denominator).map((u) => u.why).join('; ')}`,
    };
  }
  const goal = {
    k: 'app',
    op: 'and',
    args: transition.divisions.map((d) => ({
      k: 'app',
      op: 'not',
      args: [{ k: 'app', op: '=', args: [d.denominator, { k: 'num', v: '0' }] }],
    })),
  };
  const { used, dropped } = usableGuards(transition);
  return { applicable: true, guards: used, goal: goal.args.length === 1 ? goal.args[0] : goal, dropped };
}

export const PROPERTIES = {
  'amount-conservation': {
    fn: amountConservation,
    describe:
      'consuming choices preserve the amount field in total across the contracts they create',
  },
  'division-safety': {
    fn: divisionSafety,
    describe: 'no division on the transition can divide by zero under its guards',
  },
};
