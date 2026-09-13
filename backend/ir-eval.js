// backend/ir-eval.js
//
// A reference evaluator for the guarded-transition IR (see lfir.js), used by
// the differential tests to cross-check the SMT emitter (smt.js) against an
// independent implementation of the same semantics.
//
// WHAT THIS ESTABLISHES, AND WHAT IT DOES NOT:
//
//   The differential layer built on this evaluator checks that, on concrete
//   points, the meaning smt.js gives a term (as judged by cvc5) agrees with
//   the meaning this evaluator gives it. That catches silent corruption in
//   the emitter (wrong operator, wrong literal rendering, wrong associativity,
//   wrong division semantics) and in this evaluator itself - a disagreement
//   means at least one of the two is wrong.
//
//   It does NOT verify that the translator (lfir.js) maps Daml-LF expressions
//   to the right IR terms. That correspondence is the pipeline's stated trust
//   gap and no amount of IR-level differential testing discharges it.
//
// SEMANTICS: this evaluator implements SMT-LIB Reals/Ints/Core semantics, not
// Daml semantics, because the thing being cross-checked is the SMT emitter.
//
//   - Numbers are exact rationals: pairs {p, q} of BigInt, normalized so that
//     q > 0 and gcd(|p|, q) = 1. No floating point anywhere.
//   - `+ - *` are exact; `/` is exact rational division.
//   - `to_real` is the exact injection Int -> Real. It does not change the
//     rational (an Int value is a rational with denominator 1); it changes the
//     SORT, and this evaluator keeps that distinction by REFUSING a
//     non-integer argument rather than quietly accepting one. See the
//     'toreal' case.
//   - `div` and `mod` are the SMT-LIB Ints operations. SMT-LIB defines them
//     with the EUCLIDEAN convention (Boolos): for n != 0,
//         m = n * (div m n) + (mod m n)   and   0 <= (mod m n) < |n|
//     so mod is always nonnegative and div rounds toward -inf for positive
//     divisors but toward +inf for negative ones. This is NOT truncated
//     division and NOT plain floor division; tests/differential.test.js
//     verifies the choice against cvc5 on all four sign combinations.
//   - Division (or div/mod) by zero: SMT-LIB treats x/0 as an UNSPECIFIED
//     but well-defined value (the function is total; its value at 0 is just
//     not pinned down by the theory). This evaluator cannot know which value
//     a given solver picks, so it returns the distinguished marker
//     UNDEF = {undef: 'div0'} and propagates it: any operation that NEEDS the
//     undefined value (arithmetic on it, comparing it, negating it) is itself
//     UNDEF. Callers - the differential tests - must SKIP undef cases rather
//     than assert anything about them, because both "the solver agrees" and
//     "the solver disagrees" are consistent with the standard there.
//     Two deliberate refinements keep the skip rate honest without losing
//     soundness of the skip discipline:
//       * `ite` is lazy: if the condition is defined, only the taken branch
//         is evaluated. Sound because in SMT the untaken branch denotes SOME
//         value, and ite ignores it.
//       * `and`/`or` use Kleene logic: (and false U) is false and
//         (or true U) is true even when U is undef, because U denotes SOME
//         boolean and the result does not depend on which.
//     Everything else propagates undef strictly. Strict propagation can be
//     conservative - e.g. (* 0 (/ x 0)) is 0 in SMT but UNDEF here - which
//     only ever causes an extra skip, never a wrong verdict.
//
// Errors vs undef: UNDEF is a semantic value of SMT-LIB ("unspecified");
// genuinely ill-formed terms (unknown ops, unbound vars, sort mismatches such
// as `div` on a non-integer) THROW, because they have no SMT meaning at all.
//
// UNINTERPRETED FUNCTIONS. A `uf` term denotes the application of a declared
// but unconstrained symbol (see smt.js). It has no fixed meaning, so this
// evaluator cannot compute one: the CALLER supplies an INTERPRETATION, a map
// from symbol name to a JavaScript function over already-evaluated arguments.
// That is exactly what the differential layer needs - it pins the symbol to a
// concrete function on both sides (here by calling it, in SMT by asserting its
// value at the sampled points) and then checks that emitter and evaluator
// agree. With no interpretation for a symbol the term is ill-formed HERE, not
// unspecified in SMT, so it throws rather than returning UNDEF: a silent undef
// would turn a missing test fixture into a skipped case.
//
// The interpretation's results go through the same discipline as everything
// else: a rational must be a {p, q} pair (no floats), a Bool a JS boolean, and
// arguments arrive already evaluated, so an interpretation never sees a term.
//
// DATATYPE CONSTANTS (a Daml enum value, or a variant's discriminant) need no
// interpretation at all, unlike an uninterpreted function and unlike a party
// constant: SMT-LIB fixes the meaning of a datatype's nullary constructors -
// they are pairwise distinct - so the term alone determines the value, and
// equality is identity of (sort, constructor). A variable of such a sort does
// take an environment entry, built with `dcon(sort, ctor)`.

// ---------------------------------------------------------------- rationals

/** The distinguished "unspecified value" marker for division by zero. */
export const UNDEF = Object.freeze({ undef: 'div0' });

/** Is a value the division-by-zero marker? */
export function isUndef(v) {
  return typeof v === 'object' && v !== null && v.undef === 'div0';
}

/**
 * A value of the uninterpreted `Party` sort: an opaque token naming which
 * element of the model's Party carrier this constant denotes. Two party
 * constants are equal exactly when their tokens are the same string, which is
 * all an uninterpreted sort ever fixes.
 */
export const party = (token) => ({ party: String(token) });

/** Is a value a party token? */
export function isParty(v) {
  return typeof v === 'object' && v !== null && typeof v.party === 'string';
}

/**
 * A value of a declared DATATYPE sort: a Daml enum constant, or the
 * discriminant of a variant (see smt.js). An SMT datatype's nullary
 * constructors are DISTINCT by the theory, so two of these are equal exactly
 * when they name the same constructor of the same sort - no interpretation is
 * involved and none is supplied.
 *
 * The sort travels with the value because constructor names are only unique
 * within a sort, and an equality that ignored the sort would agree with the
 * emitter for the wrong reason (the emitter's symbols are sort-qualified).
 */
export const dcon = (sort, ctor) => ({ dconSort: String(sort), ctor: String(ctor) });

/** Is a value a datatype constructor token? */
export function isDcon(v) {
  return (
    typeof v === 'object' && v !== null && typeof v.dconSort === 'string' && typeof v.ctor === 'string'
  );
}

/** Is a value a rational {p, q}? */
export function isRat(v) {
  return (
    typeof v === 'object' && v !== null && typeof v.p === 'bigint' && typeof v.q === 'bigint'
  );
}

function gcd(a, b) {
  a = a < 0n ? -a : a;
  b = b < 0n ? -b : b;
  while (b) {
    const t = a % b;
    a = b;
    b = t;
  }
  return a;
}

/** Normalize a BigInt pair into canonical form: q > 0, gcd(|p|, q) = 1. */
export function ratNorm(p, q) {
  if (typeof p !== 'bigint' || typeof q !== 'bigint') throw new Error('ratNorm: BigInt required');
  if (q === 0n) throw new Error('ratNorm: zero denominator');
  if (q < 0n) {
    p = -p;
    q = -q;
  }
  if (p === 0n) return { p: 0n, q: 1n };
  const g = gcd(p, q);
  return { p: p / g, q: q / g };
}

/** Build a rational from a BigInt (or integer Number) numerator. */
export function ratFromInt(n) {
  return ratNorm(BigInt(n), 1n);
}

/**
 * Parse a decimal string ("10.0000000000", "-1.5", "0") EXACTLY into a
 * rational. This is the same literal syntax T.num carries out of the
 * translator and that smt.js hands to the solver, so parsing it exactly is
 * what makes the two sides comparable. No floating point is involved.
 */
export function ratFromDecimal(s) {
  const m = /^(-)?(\d+)(?:\.(\d+))?$/.exec(String(s).trim());
  if (!m) throw new Error(`ratFromDecimal: not a decimal literal: ${JSON.stringify(s)}`);
  const [, neg, intPart, fracPart = ''] = m;
  const p = BigInt(intPart + fracPart) * (neg ? -1n : 1n);
  const q = 10n ** BigInt(fracPart.length);
  return ratNorm(p, q);
}

export function ratAdd(a, b) {
  return ratNorm(a.p * b.q + b.p * a.q, a.q * b.q);
}

export function ratSub(a, b) {
  return ratNorm(a.p * b.q - b.p * a.q, a.q * b.q);
}

export function ratMul(a, b) {
  return ratNorm(a.p * b.p, a.q * b.q);
}

export function ratNeg(a) {
  return { p: -a.p, q: a.q };
}

/** Exact rational division; UNDEF on a zero divisor (see header). */
export function ratDiv(a, b) {
  if (b.p === 0n) return UNDEF;
  return ratNorm(a.p * b.q, a.q * b.p);
}

/** Three-way comparison: -1, 0, 1. */
export function ratCmp(a, b) {
  const d = a.p * b.q - b.p * a.q;
  return d < 0n ? -1 : d > 0n ? 1 : 0;
}

export function ratEq(a, b) {
  // canonical form makes structural equality exact equality
  return a.p === b.p && a.q === b.q;
}

/** Is the rational an integer (canonical q = 1)? */
export function ratIsInt(a) {
  return a.q === 1n;
}

// ------------------------------------------------------- Euclidean div/mod

/**
 * SMT-LIB Ints (div m n): the unique quotient with 0 <= m - n*quot < |n|.
 * UNDEF when n = 0 (unspecified in SMT-LIB, same as real division by zero).
 */
export function eucDiv(m, n) {
  if (n === 0n) return UNDEF;
  const r = eucMod(m, n);
  return (m - r) / n;
}

/** SMT-LIB Ints (mod m n): always in [0, |n|). UNDEF when n = 0. */
export function eucMod(m, n) {
  if (n === 0n) return UNDEF;
  const abs = n < 0n ? -n : n;
  let r = m % abs;
  if (r < 0n) r += abs;
  return r;
}

// -------------------------------------------------------------- evaluation

function asBool(v, where) {
  if (typeof v !== 'boolean') throw new Error(`ir-eval: ${where}: expected Bool, got ${kindOf(v)}`);
  return v;
}

function asRat(v, where) {
  if (!isRat(v)) throw new Error(`ir-eval: ${where}: expected numeric, got ${kindOf(v)}`);
  return v;
}

function asIntBig(v, where) {
  const r = asRat(v, where);
  if (!ratIsInt(r)) throw new Error(`ir-eval: ${where}: div/mod on a non-integer rational`);
  return r.p;
}

function asStr(v, where) {
  if (typeof v !== 'string') throw new Error(`ir-eval: ${where}: expected String, got ${kindOf(v)}`);
  return v;
}

function kindOf(v) {
  if (isUndef(v)) return 'undef';
  if (isRat(v)) return 'rational';
  if (isDcon(v)) return `datatype constructor ${v.ctor}`;
  return typeof v;
}

/** Left-fold a rational op over evaluated args (SMT-LIB left associativity). */
function foldRat(args, op) {
  let acc = asRat(args[0], 'arith');
  for (let i = 1; i < args.length; i++) acc = op(acc, asRat(args[i], 'arith'));
  return acc;
}

/** Chainable predicate: (op a b c) means (and (op a b) (op b c)), per SMT-LIB. */
function chain(args, pred) {
  for (let i = 0; i + 1 < args.length; i++) {
    if (!pred(args[i], args[i + 1])) return false;
  }
  return true;
}

/**
 * Evaluate an IR term under an environment.
 *
 * @param {Object} term  an lfir.js T.* term (num | str | bool | var | app | ite | uf)
 * @param {Object|Map} env  var name -> rational {p,q}, boolean or string
 * @param {Object|Map} [interp]  uf symbol name -> (…evaluatedArgs) => value
 * @returns {{p: bigint, q: bigint} | boolean | string | typeof UNDEF}
 */
export function evalTerm(term, env, interp = undefined) {
  if (!term || typeof term !== 'object') throw new Error(`ir-eval: not a term: ${term}`);
  switch (term.k) {
    case 'num':
      return ratFromDecimal(term.v);
    case 'str':
      // Daml Text is the SMT String sort; a literal evaluates to itself.
      return String(term.v);
    case 'bool':
      return !!term.v;
    case 'var': {
      const v = env instanceof Map ? env.get(term.name) : env[term.name];
      if (v === undefined) throw new Error(`ir-eval: unbound variable ${term.name}`);
      if (typeof v === 'boolean' || typeof v === 'string') return v;
      if (isParty(v) || isDcon(v)) return v;
      if (isRat(v)) return ratNorm(v.p, v.q);
      throw new Error(
        `ir-eval: env value for ${term.name} is neither boolean, string nor {p,q}`
      );
    }
    case 'dcon':
      // A CONSTANT of a declared datatype sort. Unlike a party constant it
      // needs no environment entry: the term names the constructor, and a
      // datatype's nullary constructors are pairwise distinct by the theory,
      // so its meaning is fixed by the term alone.
      return dcon(term.sort, term.ctor);
    case 'party': {
      // A constant of the UNINTERPRETED `Party` sort. It has no structure and
      // no operations: the only thing a model fixes about it is which other
      // party constants it is equal to, so the caller's environment supplies
      // exactly that - an equivalence-class token - and nothing else.
      // Deliberately NOT a String: an SMT String and an uninterpreted sort are
      // different sorts, and letting a party compare equal to a Text literal
      // would let the evaluator agree with the emitter for the wrong reason.
      const v = env instanceof Map ? env.get(term.name) : env[term.name];
      if (v === undefined) throw new Error(`ir-eval: unbound party constant ${term.name}`);
      if (!isParty(v)) throw new Error(`ir-eval: env value for ${term.name} is not a party token`);
      return v;
    }
    case 'toreal': {
      // SMT-LIB `to_real`: the exact injection of the integers into the reals.
      // Numerically it is the identity on this evaluator's rationals - an Int
      // value IS a rational with denominator 1 - so the VALUE is returned
      // unchanged, and the only thing this case adds is the SORT CHECK.
      //
      // That check is the point. The emitter and this evaluator are two
      // independent implementations of the same semantics, and the failure a
      // separate Int sort introduces is an Int-sorted term and a Real-sorted
      // one being silently interchanged. A non-integer reaching a `to_real`
      // argument means one side believes the term is an Int and the other does
      // not, so it THROWS (ill-formed here) rather than returning UNDEF
      // (unspecified in SMT): an undef would be skipped by the differential
      // layer, which is exactly how such a disagreement would go unnoticed.
      const v = evalTerm(term.a, env, interp);
      if (isUndef(v)) return UNDEF;
      const r = asRat(v, 'to_real');
      if (!ratIsInt(r)) {
        throw new Error(
          `ir-eval: to_real applied to the non-integer rational ${r.p}/${r.q}; its argument is ` +
            `Int-sorted by construction, so a non-integer means emitter and evaluator disagree ` +
            `about the term's sort`
        );
      }
      return r;
    }
    case 'ite': {
      // lazy on the branches: sound because SMT ite ignores the untaken
      // branch's (always-existing) value; see header note on undef
      const c = evalTerm(term.c, env, interp);
      if (isUndef(c)) return UNDEF;
      return evalTerm(asBool(c, 'ite condition') ? term.a : term.b, env, interp);
    }
    case 'uf':
      return evalUf(term, env, interp);
    case 'app':
      return evalApp(term, env, interp);
    case 'record':
      throw new Error('ir-eval: a whole record is not a value in this fragment');
    case 'opt':
      // An Optional value is a (presence, payload) PAIR, matching smt.js: it
      // has no scalar meaning, and a property must destructure it into a
      // guarded obligation before either side can evaluate anything.
      throw new Error('ir-eval: an Optional value is a $some/$value pair, not a scalar');
    case 'unsupported':
      throw new Error(`ir-eval: unsupported term: ${term.why}`);
    default:
      throw new Error(`ir-eval: unknown term kind ${term.k}`);
  }
}

/**
 * Apply an uninterpreted symbol under the caller's interpretation.
 *
 * Arguments are evaluated first and undef propagates strictly: the symbol is
 * an arbitrary TOTAL function, but its value at an unspecified point is itself
 * unspecified, so there is nothing concrete to check and the case must be
 * skipped like any other undef.
 */
function evalUf(term, env, interp) {
  const fn = interp instanceof Map ? interp.get(term.name) : interp && interp[term.name];
  if (typeof fn !== 'function') {
    throw new Error(
      `ir-eval: no interpretation supplied for uninterpreted symbol ${term.name}`
    );
  }
  const args = term.args.map((a) => evalTerm(a, env, interp));
  if (args.some(isUndef)) return UNDEF;
  const out = fn(...args);
  if (typeof out === 'boolean' || typeof out === 'string' || isUndef(out)) return out;
  if (isRat(out)) return ratNorm(out.p, out.q);
  throw new Error(
    `ir-eval: interpretation of ${term.name} returned neither boolean, string nor {p,q}`
  );
}

function evalApp(term, env, interp) {
  const { op } = term;

  // Kleene and/or: a false (resp. true) operand decides the result even if a
  // sibling is undef, because undef still denotes SOME boolean.
  if (op === 'and' || op === 'or') {
    const decider = op === 'and' ? false : true;
    let sawUndef = false;
    for (const a of term.args) {
      const v = evalTerm(a, env, interp);
      if (isUndef(v)) sawUndef = true;
      else if (asBool(v, op) === decider) return decider;
    }
    return sawUndef ? UNDEF : !decider;
  }

  // strict ops: evaluate all args, propagate undef
  const args = term.args.map((a) => evalTerm(a, env, interp));
  if (args.some(isUndef)) return UNDEF;

  switch (op) {
    case 'not':
      if (args.length !== 1) throw new Error('ir-eval: not takes one argument');
      return !asBool(args[0], 'not');

    case '+':
      return foldRat(args, ratAdd);
    case '*':
      return foldRat(args, ratMul);
    case '-':
      // SMT-LIB: unary minus with one arg, left-associative subtraction after
      if (args.length === 1) return ratNeg(asRat(args[0], '-'));
      return foldRat(args, ratSub);
    case '/': {
      if (args.length < 2) throw new Error('ir-eval: / needs two arguments');
      let acc = asRat(args[0], '/');
      for (let i = 1; i < args.length; i++) {
        acc = ratDiv(acc, asRat(args[i], '/'));
        if (isUndef(acc)) return UNDEF;
      }
      return acc;
    }
    case 'div':
    case 'mod': {
      if (args.length < 2) throw new Error(`ir-eval: ${op} needs two arguments`);
      let acc = asIntBig(args[0], op);
      for (let i = 1; i < args.length; i++) {
        const n = asIntBig(args[i], op);
        const r = op === 'div' ? eucDiv(acc, n) : eucMod(acc, n);
        if (isUndef(r)) return UNDEF;
        acc = r;
      }
      return ratFromInt(acc);
    }

    case '<':
      return chain(args, (a, b) => ratCmp(asRat(a, '<'), asRat(b, '<')) < 0);
    case '<=':
      return chain(args, (a, b) => ratCmp(asRat(a, '<='), asRat(b, '<=')) <= 0);
    case '>':
      return chain(args, (a, b) => ratCmp(asRat(a, '>'), asRat(b, '>')) > 0);
    case '>=':
      return chain(args, (a, b) => ratCmp(asRat(a, '>='), asRat(b, '>=')) >= 0);

    case '=': {
      // polymorphic and chainable; all args must share a sort
      if (args.length < 2) throw new Error('ir-eval: = needs two arguments');
      if (typeof args[0] === 'boolean') {
        return chain(args, (a, b) => asBool(a, '=') === asBool(b, '='));
      }
      if (typeof args[0] === 'string') {
        return chain(args, (a, b) => asStr(a, '=') === asStr(b, '='));
      }
      if (isParty(args[0])) {
        // Equality on an uninterpreted sort is identity of the model's
        // element, which the class token names.
        return chain(args, (a, b) => {
          if (!isParty(a) || !isParty(b)) throw new Error('ir-eval: = mixes a party with another sort');
          return a.party === b.party;
        });
      }
      if (isDcon(args[0])) {
        // Distinctness of a datatype's nullary constructors is part of the
        // theory, so equality is identity of (sort, constructor).
        return chain(args, (a, b) => {
          if (!isDcon(a) || !isDcon(b)) {
            throw new Error('ir-eval: = mixes a datatype constructor with another sort');
          }
          if (a.dconSort !== b.dconSort) {
            throw new Error('ir-eval: = compares constructors of two different datatype sorts');
          }
          return a.ctor === b.ctor;
        });
      }
      return chain(args, (a, b) => ratEq(asRat(a, '='), asRat(b, '=')));
    }

    default:
      throw new Error(`ir-eval: unknown operator ${op}`);
  }
}
