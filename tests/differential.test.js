// tests/differential.test.js
//
//   node --test
//
// DIFFERENTIAL TESTING between the reference IR evaluator (backend/ir-eval.js)
// and the SMT semantics of the emitter (backend/smt.js termToSmt), judged by
// cvc5. For a generated term and a concrete environment we compute
// expected = evalTerm(term, env), then ask the solver whether the emitted term
// can DIFFER from that value under the same bindings:
//
//   (assert (= var value)) for every var
//   (assert (not (= <termToSmt(term)> <expected literal>)))
//   (check-sat)            -> unsat means evaluator and emitter agree here
//
// A sat verdict is a concrete point where the pipeline's idea of a term's
// meaning and the solver's idea disagree - the silent-corruption failure mode
// of any homegrown emitter - and the test fails printing the term, the env,
// the expected value and the reproduction script.
//
// WHAT THIS ESTABLISHES AND WHAT IT DOES NOT: it tests emitter/evaluator
// agreement on concrete points (literal rendering, operator choice,
// associativity/chaining, div/mod convention). It does NOT verify the
// translator (lfir.js) against Daml-LF semantics; that trust gap belongs to
// other layers and is deliberately not claimed here. Nor does agreement on
// sampled points PROVE the two semantics identical - it makes a mismatch of
// the kind emitters actually have (systematic, not adversarial) very loud.
//
// UNINTERPRETED FUNCTIONS: a `uf` term has no fixed meaning, so there is
// nothing to check until one is chosen. Each case that contains a uf comes
// with an INTERPRETATION - a concrete function per symbol - which the
// evaluator applies directly and the query PINS by asserting the symbol's
// value at the points the case actually reaches. Both sides then speak about
// the same function, and a disagreement is again an emitter/evaluator bug
// (wrong application syntax, wrong argument order, a missing declare-fun).
//
// DIVISION BY ZERO: SMT-LIB makes x/0 (and div/mod by 0) an unspecified
// value, so no concrete expectation is checkable there. The evaluator returns
// a distinguished undef marker on such paths and those cases are SKIPPED, not
// asserted; skips are counted and bounded so they cannot silently eat the
// test. See the header of backend/ir-eval.js.

import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync } from 'node:child_process';
import { writeFileSync, mkdtempSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { T, hasUnsupported, extractTransitions } from '../backend/lfir.js';
import { termToSmt, inferSorts } from '../backend/smt.js';
import { readDarRaw } from '../backend/dalf.js';
import {
  UNDEF,
  isUndef,
  isRat,
  ratNorm,
  ratFromInt,
  ratFromDecimal,
  ratAdd,
  ratSub,
  ratMul,
  ratDiv,
  ratNeg,
  ratCmp,
  ratEq,
  ratIsInt,
  eucDiv,
  eucMod,
  evalTerm,
  party,
  dcon,
  isDcon,
} from '../backend/ir-eval.js';

// ------------------------------------------------------------ solver gating
// Same pattern as tests/verify.test.js: solver-dependent tests are skipped,
// with a message, when cvc5 is not installed.

function hasSolver() {
  try {
    execFileSync('cvc5', ['--version'], { stdio: 'ignore', timeout: 5000 });
    return true;
  } catch (_) {
    return false;
  }
}
const SOLVER = hasSolver();
const NO_SOLVER_MSG = 'cvc5 not installed; differential checks need a live solver';

function runSolver(script, extraArgs = []) {
  const dir = mkdtempSync(join(tmpdir(), 'diff-'));
  const file = join(dir, 'q.smt2');
  writeFileSync(file, script);
  try {
    return execFileSync('cvc5', [...extraArgs, '--lang', 'smt2', file], {
      encoding: 'utf8',
      timeout: 60000,
    });
  } catch (e) {
    return `${e.stdout || ''}${e.stderr || ''}`;
  }
}

/** Extract the ordered sat/unsat/unknown verdicts from solver output. */
function parseVerdicts(out) {
  return out
    .split(/\r?\n/)
    .map((l) => l.trim())
    .filter((l) => l === 'sat' || l === 'unsat' || l === 'unknown');
}

// -------------------------------------------------------------- seeded PRNG
// mulberry32: small, seeded, reproducible. No Math.random anywhere, so a
// failure reproduces by rerunning the file.

const SEED = 0x5eed2026;

function mulberry32(seed) {
  let a = seed >>> 0;
  return function () {
    a = (a + 0x6d2b79f5) >>> 0;
    let t = a;
    t = Math.imul(t ^ (t >>> 15), t | 1);
    t ^= t + Math.imul(t ^ (t >>> 7), t | 61);
    return ((t ^ (t >>> 14)) >>> 0) / 4294967296;
  };
}

const pick = (rnd, arr) => arr[Math.floor(rnd() * arr.length)];
const chance = (rnd, p) => rnd() < p;

// -------------------------------------------------------- SMT value literals

/** Quote a var name exactly the way smt.js does (keep in sync with sym()). */
const smtSym = (name) => `|${name.replace(/[|\\]/g, '_')}|`;

/**
 * Render an exact rational (or boolean) as an unambiguous SMT literal.
 * Int sort gets numerals; Real sort gets decimal / (/ p.0 q.0) forms, with
 * negation wrapped as (- ...). The literal-syntax probe test below validates
 * these forms against cvc5 before the scaled run relies on them.
 */
function valueToSmt(v, sort) {
  if (typeof v === 'boolean') return v ? 'true' : 'false';
  // SMT-LIB escapes a double quote by doubling it, exactly as smt.js does.
  if (typeof v === 'string') return `"${v.replace(/"/g, '""')}"`;
  if (!isRat(v)) throw new Error('valueToSmt: not a boolean, string or rational');
  const neg = v.p < 0n;
  const p = neg ? -v.p : v.p;
  let core;
  if (sort === 'Int') {
    if (v.q !== 1n) throw new Error('valueToSmt: non-integer value for an Int sort');
    core = `${p}`;
  } else {
    core = v.q === 1n ? `${p}.0` : `(/ ${p}.0 ${v.q}.0)`;
  }
  return neg ? `(- ${core})` : core;
}

// --------------------------------------------------------------- generation
//
// Cases are generated in one of two numeric modes, mirroring the two SMT
// arithmetic sorts the emitter's output can inhabit:
//   Real mode: ops + - * /, Real vars, decimal literals
//   Int mode:  ops + - * div mod, Int vars, integer literals
// (SMT-LIB types div/mod at Int only - cvc5 rejects (div x y) on Reals - so
// a well-sorted term never mixes the two families on the same variables.)
//
// A Real-mode term may additionally contain an INT-SORTED SUBTERM under an
// explicit `to_real` coercion - which is exactly the shape INT64_TO_NUMERIC
// produces (lfir.js) and the only well-sorted way the two arithmetic families
// meet in one term. It is generated in its own sub-mode ('IntC') over a
// DISJOINT set of variables, because a single variable cannot be Int in one
// occurrence and Real in another: that is a sort conflict, not a case.
//
// This is the arm that pins the coercion end to end - the emitter's `to_real`
// rendering, the evaluator's integrality check, the Int literal rendering
// underneath it, and the fact that the Real arithmetic around it is unchanged.

const NUM_VARS = ['n0', 'n1', 'n2', 'n3'];
/** Int-sorted variables, reachable only under a `to_real` coercion. */
const COERCED_INT_VARS = ['c0', 'c1'];
const BOOL_VARS = ['b0', 'b1'];

/** Does this generation mode produce Int-sorted terms? */
const isIntMode = (mode) => mode === 'Int' || mode === 'IntC';
/** The variables a mode draws on; 'IntC' has its own so sorts never clash. */
const varsForMode = (mode) => (mode === 'IntC' ? COERCED_INT_VARS : NUM_VARS);

// Real-mode literals always carry a decimal point, as the translator's
// Numeric literals do ("0.0000000000"): SMT-LIB types a bare numeral as Int,
// and while cvc5 casts it in arithmetic/equality contexts it rejects it as an
// ite branch against a Real. The one place the pipeline itself relies on the
// numeral leniency - divisionSafety's (= denom 0) - gets a targeted probe in
// the literal-syntax test below.
const REAL_LITERALS = [
  '0.0', '1.0', '2.0', '-1.0', '0.5', '-2.75', '3.1415926535',
  '10.0000000000', '0.0000000000', '-0.0000000001',
  '9007199254740993.0000000001', // exceeds double precision: floats would corrupt it
  '123456789.987654321', '-99999999999999999999.9999999999',
];
const INT_LITERALS = [
  '0', '1', '2', '7', '-1', '-7', '5', '-13', '100',
  '9007199254740993', '-123456789123456789', '288230376151711744',
];

// Uninterpreted symbols the generator may apply. Their interpretations are
// fixed here (see UF_INTERP) so the evaluator and the solver can be pinned to
// the same function; the point of the check is the APPLICATION MACHINERY -
// declaration, arity, argument order, rendering - not the functions chosen.
// Only Real-mode numeric arguments are generated: div/mod force Int-sorted
// variables, and a symbol declared over Real would not be well sorted there.
const UF_NUM = [
  { name: 'uf.n1', arity: 1, sort: 'Real' },
  { name: 'uf.n2', arity: 2, sort: 'Real' },
];
const UF_BOOL = [
  { name: 'uf.b1', arity: 1, sort: 'Bool' },
  { name: 'uf.b2', arity: 2, sort: 'Bool' },
];

/** Concrete meanings, shared by the evaluator and the pinned query. */
const UF_INTERP = {
  // 3a - 1
  'uf.n1': (a) => ratSub(ratMul(ratFromInt(3), a), ratFromInt(1)),
  // a - 2b
  'uf.n2': (a, b) => ratSub(a, ratMul(ratFromInt(2), b)),
  // a > 1
  'uf.b1': (a) => ratCmp(a, ratFromInt(1)) > 0,
  // a <= b (ORDER MATTERS: a swapped-argument emitter must fail here)
  'uf.b2': (a, b) => ratCmp(a, b) <= 0,
};

function genNum(rnd, depth, mode) {
  // Literals carry the sort of the LF field they would have been read out of:
  // `T.int` for an int64 literal, `T.num(v, 'Real')` for a numeric one. That
  // tag is what makes a Real literal meeting an Int term a sort conflict
  // rather than a silent coercion, so the generator uses it too.
  const lit = () =>
    isIntMode(mode) ? T.int(pick(rnd, INT_LITERALS)) : T.num(pick(rnd, REAL_LITERALS), 'Real');
  const vr = () => T.varRef(pick(rnd, varsForMode(mode)), isIntMode(mode) ? 'Int' : 'Real');
  if (depth <= 0) return chance(rnd, 0.5) ? lit() : vr();
  const roll = rnd();
  if (roll < 0.15) return lit();
  if (roll < 0.3) return vr();
  if (roll < 0.45) {
    const n = chance(rnd, 0.3) ? 3 : 2;
    return T.app('+', Array.from({ length: n }, () => genNum(rnd, depth - 1, mode)));
  }
  if (roll < 0.6) {
    // unary minus sometimes, to exercise the (- x) rendering
    if (chance(rnd, 0.25)) return T.app('-', [genNum(rnd, depth - 1, mode)]);
    return T.app('-', [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)]);
  }
  if (roll < 0.75) return T.app('*', [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)]);
  if (roll < 0.85) {
    const op = isIntMode(mode) ? (chance(rnd, 0.5) ? 'div' : 'mod') : '/';
    return T.app(op, [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)]);
  }
  if (roll < 0.92 && mode === 'Real') {
    const u = pick(rnd, UF_NUM);
    return T.uf(u.name, Array.from({ length: u.arity }, () => genNum(rnd, depth - 1, mode)), u.sort);
  }
  // An Int-sorted subterm lifted into this Real term by an explicit coercion.
  if (roll < 0.96 && mode === 'Real') return T.toReal(genNum(rnd, depth - 1, 'IntC'));
  return T.ite(genBool(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode));
}

function genBool(rnd, depth, mode) {
  const vr = () => T.varRef(pick(rnd, BOOL_VARS), 'Bool');
  if (depth <= 0) return chance(rnd, 0.4) ? T.bool(chance(rnd, 0.5)) : vr();
  const roll = rnd();
  if (roll < 0.08) return T.bool(chance(rnd, 0.5));
  if (roll < 0.2) return vr();
  if (roll < 0.32) return T.app('not', [genBool(rnd, depth - 1, mode)]);
  if (roll < 0.5) {
    const n = chance(rnd, 0.3) ? 3 : 2;
    const op = chance(rnd, 0.5) ? 'and' : 'or';
    return T.app(op, Array.from({ length: n }, () => genBool(rnd, depth - 1, mode)));
  }
  if (roll < 0.78) {
    const op = pick(rnd, ['<', '<=', '>', '>=']);
    return T.app(op, [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)]);
  }
  if (roll < 0.88) {
    // polymorphic equality: numeric or boolean operands
    return chance(rnd, 0.7)
      ? T.app('=', [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)])
      : T.app('=', [genBool(rnd, depth - 1, mode), genBool(rnd, depth - 1, mode)]);
  }
  if (roll < 0.94 && mode === 'Real') {
    const u = pick(rnd, UF_BOOL);
    return T.uf(u.name, Array.from({ length: u.arity }, () => genNum(rnd, depth - 1, mode)), u.sort);
  }
  return T.ite(genBool(rnd, depth - 1, mode), genBool(rnd, depth - 1, mode), genBool(rnd, depth - 1, mode));
}

function randomRat(rnd) {
  const roll = rnd();
  if (roll < 0.35) return ratFromDecimal(pick(rnd, REAL_LITERALS));
  if (roll < 0.5) return ratFromInt(BigInt(Math.floor(rnd() * 2001) - 1000));
  // a genuine non-decimal rational, e.g. -437/97
  const p = BigInt(Math.floor(rnd() * 2001) - 1000);
  const q = BigInt(1 + Math.floor(rnd() * 96));
  return ratNorm(p, q);
}

function randomInt(rnd) {
  const roll = rnd();
  if (roll < 0.15) return ratFromInt(0);
  if (roll < 0.3) return ratFromDecimal(pick(rnd, INT_LITERALS));
  return ratFromInt(BigInt(Math.floor(rnd() * 20001) - 10000));
}

function randomEnv(rnd, mode) {
  const env = new Map();
  for (const n of NUM_VARS) env.set(n, isIntMode(mode) ? randomInt(rnd) : randomRat(rnd));
  // The coerced variables are Int in every mode: they only ever occur under a
  // `to_real`, and binding one to a fraction would be binding an Int-sorted
  // symbol to a non-integer - which the evaluator rightly refuses.
  for (const c of COERCED_INT_VARS) env.set(c, randomInt(rnd));
  for (const b of BOOL_VARS) env.set(b, chance(rnd, 0.5));
  return env;
}

/** Variable names occurring in a term (only those get declared and bound). */
function varsOf(term, out = new Set()) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'var') out.add(term.name);
  else if (term.k === 'app' || term.k === 'uf') term.args.forEach((a) => varsOf(a, out));
  else if (term.k === 'ite') [term.c, term.a, term.b].forEach((a) => varsOf(a, out));
  else if (term.k === 'toreal') varsOf(term.a, out);
  return out;
}

/** Every uninterpreted application in a term, innermost first. */
function ufAppsOf(term, out = []) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'uf') {
    term.args.forEach((a) => ufAppsOf(a, out));
    out.push(term);
  } else if (term.k === 'app') term.args.forEach((a) => ufAppsOf(a, out));
  else if (term.k === 'ite') [term.c, term.a, term.b].forEach((a) => ufAppsOf(a, out));
  else if (term.k === 'toreal') ufAppsOf(term.a, out);
  return out;
}

/** The uf symbols a term applies, with their signature. */
function ufSigsOf(term) {
  const sigs = new Map();
  for (const u of ufAppsOf(term)) {
    if (!sigs.has(u.name)) sigs.set(u.name, { args: u.args.length, ret: u.sort });
  }
  return sigs;
}

// ------------------------------------------------------------ query building

/**
 * One differential case: bind each used var to its concrete value, then ask
 * whether the emitted term can differ from the evaluator's expected value.
 * `varSorts` maps var name -> 'Bool' | 'Real' | 'Int'.
 */
function caseLines(c) {
  const lines = [];
  for (const name of [...varsOf(c.term)].sort()) {
    const sort = c.varSorts.get(name);
    const value = c.env.get(name);
    lines.push(`(declare-const ${smtSym(name)} ${sort})`);
    lines.push(`(assert (= ${smtSym(name)} ${valueToSmt(value, sort)}))`);
  }
  const numSort = c.mode === 'Int' ? 'Int' : 'Real';
  // Uninterpreted symbols are declared and then PINNED at exactly the argument
  // points this case reaches, by evaluating the interpretation there. Pinning
  // pointwise rather than defining the function keeps the emitted term under
  // test - the query still has to apply the symbol the same way the evaluator
  // did, to the same arguments, in the same order.
  for (const [name, sig] of ufSigsOf(c.term)) {
    const resolved = c.ufSorts && c.ufSorts.get(name);
    const argSorts = resolved ? resolved.args : Array(sig.args).fill(numSort);
    lines.push(
      `(declare-fun ${smtSym(name)} (${argSorts.join(' ')}) ${resolved ? resolved.ret : sig.ret})`
    );
  }
  const interp = c.interp || UF_INTERP;
  for (const u of ufAppsOf(c.term)) {
    const argVals = u.args.map((a) => evalTerm(a, c.env, interp));
    if (argVals.some(isUndef)) continue; // unspecified point: nothing to pin
    const out = interp[u.name](...argVals);
    const applied = `(${smtSym(u.name)} ${argVals
      .map((v, i) => valueToSmt(v, (c.ufSorts && c.ufSorts.get(u.name).args[i]) || numSort))
      .join(' ')})`;
    lines.push(
      `(assert (= ${applied} ${valueToSmt(out, u.sort || c.ufSorts.get(u.name).ret)}))`
    );
  }
  const expectedSort =
    typeof c.expected === 'boolean'
      ? 'Bool'
      : typeof c.expected === 'string'
        ? 'String'
        : c.expectedSort || numSort;
  lines.push(`(assert (not (= ${termToSmt(c.term)} ${valueToSmt(c.expected, expectedSort)})))`);
  return lines;
}

function standaloneScript(c) {
  return ['(set-logic ALL)', ...caseLines(c), '(check-sat)', ''].join('\n');
}

/**
 * Run a batch of cases in ONE incremental cvc5 process, one (push)/(pop) and
 * (check-sat) per case so a failure maps back to exactly one case (a single
 * conjoined query would prove nothing per-case and localize nothing).
 * Returns the per-case verdicts in order.
 */
function runBatch(cases) {
  const lines = ['(set-logic ALL)'];
  for (const c of cases) {
    lines.push('(push 1)', ...caseLines(c), '(check-sat)', '(pop 1)');
  }
  const script = lines.join('\n') + '\n';
  const out = runSolver(script, ['--incremental']);
  const verdicts = parseVerdicts(out);
  if (verdicts.length !== cases.length) {
    throw new Error(
      `solver returned ${verdicts.length} verdicts for ${cases.length} cases; output:\n${out}\nscript:\n${script}`
    );
  }
  return verdicts;
}

const jsonBig = (x) =>
  JSON.stringify(x, (k, v) => (typeof v === 'bigint' ? `${v}n` : v instanceof Map ? Object.fromEntries(v) : v));

function showValue(v) {
  if (typeof v === 'boolean') return String(v);
  if (isUndef(v)) return 'undef(div0)';
  return v.q === 1n ? `${v.p}` : `${v.p}/${v.q}`;
}

function describeFailure(c, verdict) {
  const env = {};
  for (const name of [...varsOf(c.term)].sort()) env[name] = showValue(c.env.get(name));
  return [
    `verdict: ${verdict} (expected unsat: evaluator and emitter should agree)`,
    `term: ${jsonBig(c.term)}`,
    `env: ${JSON.stringify(env)}`,
    `expected: ${showValue(c.expected)}`,
    `reproduction (.smt2):`,
    standaloneScript(c),
  ].join('\n');
}

/** Run all cases through the solver in batches; return failure descriptions. */
function differential(cases, batchSize = 25) {
  const failures = [];
  for (let i = 0; i < cases.length; i += batchSize) {
    const batch = cases.slice(i, i + batchSize);
    const verdicts = runBatch(batch);
    verdicts.forEach((v, j) => {
      if (v !== 'unsat') failures.push(describeFailure(batch[j], v));
    });
  }
  return failures;
}

// ==================================================== unit: rational parsing

test('ratFromDecimal parses decimal strings exactly (no floats involved)', () => {
  assert.deepEqual(ratFromDecimal('0'), { p: 0n, q: 1n });
  assert.deepEqual(ratFromDecimal('10.0000000000'), { p: 10n, q: 1n });
  assert.deepEqual(ratFromDecimal('-1.5'), { p: -3n, q: 2n });
  assert.deepEqual(ratFromDecimal('0.50'), { p: 1n, q: 2n });
  assert.deepEqual(ratFromDecimal('-0.0000000001'), { p: -1n, q: 10000000000n });
  // beyond double precision: parseFloat would collapse this to 9007199254740992
  assert.deepEqual(ratFromDecimal('9007199254740993.0000000001'), {
    p: 90071992547409930000000001n,
    q: 10000000000n,
  });
  // normalization: q > 0, gcd = 1, canonical zero
  assert.deepEqual(ratNorm(-4n, -6n), { p: 2n, q: 3n });
  assert.deepEqual(ratNorm(0n, -7n), { p: 0n, q: 1n });
  assert.throws(() => ratFromDecimal('1e5'), /not a decimal/);
  assert.throws(() => ratFromDecimal('1.2.3'), /not a decimal/);
  assert.throws(() => ratFromDecimal(''), /not a decimal/);
});

test('rational arithmetic is exact', () => {
  const a = ratFromDecimal('0.1');
  const b = ratFromDecimal('0.2');
  assert.ok(ratEq(ratAdd(a, b), ratFromDecimal('0.3'))); // famously false in floats
  assert.ok(ratEq(ratMul(ratFromDecimal('-1.5'), ratFromDecimal('2')), ratFromDecimal('-3')));
  assert.ok(ratEq(ratSub(ratFromInt(1), ratFromDecimal('0.9999999999')), ratFromDecimal('0.0000000001')));
  assert.ok(ratEq(ratDiv(ratFromInt(1), ratFromInt(3)), ratNorm(1n, 3n)));
  assert.equal(ratCmp(ratNorm(1n, 3n), ratFromDecimal('0.3333333333')), 1);
  assert.ok(ratEq(ratNeg(ratNorm(1n, 3n)), ratNorm(-1n, 3n)));
  assert.ok(ratIsInt(ratFromDecimal('42.00')));
  assert.ok(!ratIsInt(ratFromDecimal('42.5')));
  // division by zero is the distinguished marker, not an exception
  assert.ok(isUndef(ratDiv(ratFromInt(1), ratFromInt(0))));
  assert.ok(isUndef(UNDEF));
});

// ============================================= unit: Euclidean div and mod

test('eucDiv/eucMod implement SMT-LIB (Euclidean) semantics on all sign combos', () => {
  // identity: m = n * div + mod, with 0 <= mod < |n|
  const combos = [
    [7n, 2n, 3n, 1n],
    [-7n, 2n, -4n, 1n], // NOT truncation (-3); mod stays nonnegative
    [7n, -2n, -3n, 1n], // NOT floor (-4); Euclidean rounds toward +inf here
    [-7n, -2n, 4n, 1n],
    [6n, 3n, 2n, 0n],
    [-6n, 3n, -2n, 0n],
    [0n, 5n, 0n, 0n],
    [0n, -5n, 0n, 0n],
  ];
  for (const [m, n, d, r] of combos) {
    assert.equal(eucDiv(m, n), d, `div ${m} ${n}`);
    assert.equal(eucMod(m, n), r, `mod ${m} ${n}`);
    assert.equal(n * d + r, m, `identity for ${m} ${n}`);
  }
  // large values beyond float precision
  const big = 90071992547409930000000001n;
  assert.equal(eucDiv(big, 10n) * 10n + eucMod(big, 10n), big);
  assert.equal(eucMod(-big, 7n) >= 0n, true);
  // zero divisor is undef, not an exception
  assert.ok(isUndef(eucDiv(5n, 0n)));
  assert.ok(isUndef(eucMod(5n, 0n)));
});

// ======================================================== unit: evaluation

test('evalTerm: core semantics, laziness and undef discipline', () => {
  const env = new Map([
    ['x', ratFromDecimal('7')],
    ['y', ratFromDecimal('-2.5')],
    ['f', true],
  ]);
  const v = (n) => T.varRef(n, 'Real');
  // exact arithmetic and chainable comparisons
  assert.ok(ratEq(evalTerm(T.app('+', [v('x'), v('y')]), env), ratFromDecimal('4.5')));
  assert.ok(ratEq(evalTerm(T.app('-', [v('y')]), env), ratFromDecimal('2.5')));
  assert.equal(evalTerm(T.app('<', [v('y'), T.num('0')]), env), true);
  // '=' on booleans
  assert.equal(evalTerm(T.app('=', [T.varRef('f', 'Bool'), T.bool(true)]), env), true);
  // ite is lazy: the untaken branch may divide by zero without poisoning
  const divZero = T.app('/', [v('x'), T.num('0')]);
  assert.ok(ratEq(evalTerm(T.ite(T.bool(true), v('x'), divZero), env), ratFromDecimal('7')));
  // but a NEEDED division by zero is undef, and it propagates through arith
  assert.ok(isUndef(evalTerm(divZero, env)));
  assert.ok(isUndef(evalTerm(T.app('+', [divZero, T.num('1')]), env)));
  assert.ok(isUndef(evalTerm(T.app('=', [divZero, divZero]), env))); // solver could say true; we must not guess
  // Kleene and/or: a deciding operand wins even next to undef
  const undefBool = T.app('<', [divZero, T.num('1')]);
  assert.equal(evalTerm(T.app('and', [T.bool(false), undefBool]), env), false);
  assert.equal(evalTerm(T.app('or', [T.bool(true), undefBool]), env), true);
  assert.ok(isUndef(evalTerm(T.app('and', [T.bool(true), undefBool]), env)));
  // ill-formed terms throw (no SMT meaning), they do not return undef
  assert.throws(() => evalTerm(T.varRef('nope', 'Real'), env), /unbound/);
  assert.throws(() => evalTerm(T.app('div', [v('y'), T.num('2')]), env), /non-integer/);
  assert.throws(() => evalTerm(T.app('shell', [v('x')]), env), /unknown operator/);
  assert.throws(() => evalTerm(T.unsupported('why', 'at'), env), /unsupported/);
});

test('evalTerm: to_real is exact on the value and STRICT about the sort', () => {
  const env = new Map([
    ['i', ratFromInt(7n)],
    ['r', ratFromDecimal('2.5')],
  ]);
  // Numerically the identity: an Int value IS a rational with denominator 1,
  // so the coercion changes the sort and nothing else.
  assert.ok(ratEq(evalTerm(T.toReal(T.varRef('i', 'Int')), env), ratFromInt(7n)));
  assert.ok(
    ratEq(
      evalTerm(T.app('+', [T.toReal(T.varRef('i', 'Int')), T.num('0.5', 'Real')]), env),
      ratFromDecimal('7.5')
    )
  );
  assert.ok(ratEq(evalTerm(T.toReal(T.int('-13')), env), ratFromInt(-13n)));

  // The SORT is what this case is really for. `to_real`'s argument is
  // Int-sorted by construction, so a non-integer there means the emitter and
  // this evaluator disagree about a term's sort - the exact failure a second
  // arithmetic sort introduces. It THROWS rather than returning UNDEF,
  // because the differential layer SKIPS undef and a silent skip is how such a
  // disagreement would go unnoticed.
  assert.throws(() => evalTerm(T.toReal(T.varRef('r', 'Real')), env), /non-integer/);

  // undef still propagates, and an unsupported node under a coercion is still
  // ill-formed rather than quietly a value.
  assert.ok(isUndef(evalTerm(T.toReal(T.app('div', [T.int('1'), T.int('0')])), env)));
  assert.throws(() => evalTerm(T.toReal(T.unsupported('why', 'at')), env), /unsupported/);
});

// chainable comparisons: (< a b c) is (and (< a b) (< b c)) per SMT-LIB
test('evalTerm: chainable comparison follows SMT-LIB adjacent-pair semantics', () => {
  const env = new Map([['x', ratFromDecimal('7')], ['y', ratFromDecimal('-2.5')]]);
  const v = (n) => T.varRef(n, 'Real');
  assert.equal(evalTerm(T.app('<', [v('y'), T.num('0'), v('x')]), env), true);
  assert.equal(evalTerm(T.app('<', [T.num('0'), v('y'), v('x')]), env), false);
  assert.equal(evalTerm(T.app('=', [T.num('1'), T.num('1.0'), T.num('1.00')]), env), true);
});

// ================================================ solver: literal syntax

test('cvc5 accepts our exact-rational literal forms', { skip: !SOLVER && NO_SOLVER_MSG }, () => {
  // hand-built cases through the SAME machinery the scaled run uses, so the
  // literal syntax is validated before we trust 500 generated verdicts
  const mk = (envVal, litTerm) => ({
    term: T.varRef('x', 'Real'),
    mode: 'Real',
    env: new Map([['x', envVal]]),
    varSorts: new Map([['x', 'Real']]),
    expected: litTerm,
  });
  const cases = [
    mk(ratFromDecimal('9007199254740993.0000000001'), ratFromDecimal('9007199254740993.0000000001')),
    mk(ratNorm(-7n, 2n), ratFromDecimal('-3.5')),
    mk(ratNorm(1n, 3n), ratNorm(1n, 3n)), // (/ 1.0 3.0)
    mk(ratNorm(-999999999999999999999n, 7n), ratNorm(-999999999999999999999n, 7n)),
    mk(ratFromInt(5), ratFromInt(5)), // 5.0
    mk(ratFromInt(0), ratFromInt(0)),
    // divisionSafety emits (= <Real term> 0) with a bare numeral; cvc5 casts
    // numerals to Real in equality contexts, and this pins that assumption
    {
      term: T.app('=', [T.varRef('x', 'Real'), T.num('0')]),
      mode: 'Real',
      env: new Map([['x', ratFromInt(0)]]),
      varSorts: new Map([['x', 'Real']]),
      expected: true,
    },
    // The Int/Real boundary, pinned as a ground fact: an Int-sorted symbol
    // lifted into Real arithmetic by `to_real`, which is exactly the shape
    // INT64_TO_NUMERIC (`intToDecimal`) produces. The emitter must write the
    // coercion, declare the symbol `Int`, and keep the surrounding Real
    // literals as Real literals.
    {
      term: T.app('+', [T.toReal(T.varRef('i', 'Int')), T.num('0.5', 'Real')]),
      mode: 'Real',
      env: new Map([['i', ratFromInt(7n)]]),
      varSorts: new Map([['i', 'Int']]),
      expected: ratFromDecimal('7.5'),
    },
    // ...and the Int side keeps INTEGER numerals: `(* i 10) + 1` is odd for
    // every integer i, which is the fact the whole Int sort exists to make
    // available to the solver.
    {
      term: T.app('=', [
        { k: 'app', op: '+', args: [
          { k: 'app', op: '*', args: [T.varRef('i', 'Int'), T.int('10')], ns: 'Int' },
          T.int('1'),
        ], ns: 'Int' },
        T.num('0'),
      ]),
      mode: 'Int',
      env: new Map([['i', ratFromInt(-3n)]]),
      varSorts: new Map([['i', 'Int']]),
      expected: false,
    },
  ];
  const failures = differential(cases);
  assert.equal(failures.length, 0, failures.join('\n\n'));
});

// ============================================ solver: div/mod convention

test('cvc5 div/mod is Euclidean, matching eucDiv/eucMod exactly', { skip: !SOLVER && NO_SOLVER_MSG }, () => {
  // Ground facts, checked both ways: asserting the Euclidean result is sat
  // (it is THE value) and asserting the truncated/floored alternative, where
  // it differs, is unsat. This pins the convention rather than assuming it.
  const script = [
    '(set-logic ALL)',
    // Euclidean values (from eucDiv/eucMod) must be satisfiable ground truths
    `(push 1) (assert (= (div (- 7) 2) (- ${-eucDiv(-7n, 2n)}))) (check-sat) (pop 1)`, // -4
    `(push 1) (assert (= (div 7 (- 2)) (- ${-eucDiv(7n, -2n)}))) (check-sat) (pop 1)`, // -3
    `(push 1) (assert (= (div (- 7) (- 2)) ${eucDiv(-7n, -2n)})) (check-sat) (pop 1)`, // 4
    `(push 1) (assert (= (mod (- 7) 2) ${eucMod(-7n, 2n)})) (check-sat) (pop 1)`, // 1
    `(push 1) (assert (= (mod 7 (- 2)) ${eucMod(7n, -2n)})) (check-sat) (pop 1)`, // 1
    `(push 1) (assert (= (mod (- 7) (- 2)) ${eucMod(-7n, -2n)})) (check-sat) (pop 1)`, // 1
    // truncation says div(-7,2) = -3; floor says div(7,-2) = -4; both must be refuted
    '(push 1) (assert (= (div (- 7) 2) (- 3))) (check-sat) (pop 1)',
    '(push 1) (assert (= (div 7 (- 2)) (- 4))) (check-sat) (pop 1)',
    '(push 1) (assert (= (mod (- 7) 2) (- 1))) (check-sat) (pop 1)',
    '(push 1) (assert (= (mod 7 (- 2)) (- 1))) (check-sat) (pop 1)',
    '',
  ].join('\n');
  const out = runSolver(script, ['--incremental']);
  const verdicts = parseVerdicts(out);
  assert.deepEqual(
    verdicts,
    ['sat', 'sat', 'sat', 'sat', 'sat', 'sat', 'unsat', 'unsat', 'unsat', 'unsat'],
    `unexpected verdicts; solver output:\n${out}`
  );
});

// ======================================== THE DIFFERENTIAL PROPERTY (scaled)

test('differential: evalTerm agrees with termToSmt through cvc5 on 500+ generated cases', { skip: !SOLVER && NO_SOLVER_MSG }, (t) => {
  const rnd = mulberry32(SEED);
  const TARGET = 520; // checked (non-undef) cases; the property needs >= 500
  const MAX_ATTEMPTS = 4000;

  const cases = [];
  let attempts = 0;
  let skippedUndef = 0;
  while (cases.length < TARGET && attempts < MAX_ATTEMPTS) {
    attempts++;
    const mode = chance(rnd, 0.5) ? 'Int' : 'Real';
    const rootBool = chance(rnd, 0.5);
    // depth 4 below the root keeps terms at depth <= 5
    const term = rootBool ? genBool(rnd, 4, mode) : genNum(rnd, 4, mode);
    const env = randomEnv(rnd, mode);
    const expected = evalTerm(term, env, UF_INTERP);
    if (isUndef(expected)) {
      // division by zero on the needed path: SMT calls the value unspecified,
      // so there is no concrete expectation to check - skip, never assert
      skippedUndef++;
      continue;
    }
    const numSort = mode === 'Int' ? 'Int' : 'Real';
    const varSorts = new Map();
    for (const n of NUM_VARS) varSorts.set(n, numSort);
    for (const c of COERCED_INT_VARS) varSorts.set(c, 'Int');
    for (const b of BOOL_VARS) varSorts.set(b, 'Bool');
    cases.push({ term, env, varSorts, expected, mode });
  }

  const withUf = cases.filter((c) => ufAppsOf(c.term).length > 0).length;
  const withCoercion = cases.filter((c) => containsCoercion(c.term)).length;
  t.diagnostic(
    `generated ${attempts} term/env pairs; checked ${cases.length}; ` +
      `skipped ${skippedUndef} undef (div0); ${withUf} apply an uninterpreted symbol; ` +
      `${withCoercion} carry an Int -> Real coercion`
  );
  assert.ok(cases.length >= 500, `only ${cases.length} checkable cases generated (skip rate too high)`);
  // Without this the uf arm could silently stop being generated and the whole
  // uninterpreted-application path would go untested while the test passed.
  assert.ok(withUf >= 50, `only ${withUf} cases exercise an uninterpreted application`);
  // Same guard for the coercion arm: without it the Int/Real boundary - the
  // one place the two arithmetic sorts meet - could silently stop being
  // generated while the test still passed.
  assert.ok(
    withCoercion >= 25,
    `only ${withCoercion} cases carry an Int -> Real coercion`
  );

  const failures = differential(cases);
  assert.equal(
    failures.length,
    0,
    `${failures.length} case(s) where the evaluator and the emitter disagree:\n\n${failures.join('\n\n')}`
  );
});

// ================================================== live-DAR smoke test

// Supplied via the environment; the test skips when absent.
const DAR_PATH = process.env.TOKENS_DAR || '';
const HAVE_DAR = DAR_PATH !== '' && existsSync(DAR_PATH);

/** Is every node of a term something both the evaluator and emitter model? */
function termIsClean(term) {
  if (!term || typeof term !== 'object') return false;
  switch (term.k) {
    case 'num':
      return /^-?\d+(\.\d+)?$/.test(String(term.v));
    case 'bool':
      return true;
    case 'var':
      return true;
    case 'str':
      return true;
    case 'uf':
      // An uninterpreted application IS in the checkable fragment: the case
      // pins the symbol pointwise, so both sides speak about one function.
      return term.args.every(termIsClean);
    case 'app':
      return (
        ['+', '-', '*', '/', 'div', 'mod', '<', '<=', '>', '>=', '=', 'not', 'and', 'or'].includes(term.op) &&
        term.args.length > 0 &&
        term.args.every(termIsClean)
      );
    case 'ite':
      return [term.c, term.a, term.b].every(termIsClean);
    case 'toreal':
      // The Int -> Real coercion: both sides model it exactly.
      return termIsClean(term.a);
    default:
      return false; // record, unsupported, anything unknown
  }
}

/**
 * A deterministic interpretation for the uninterpreted symbols a REAL DAR term
 * applies, built from the signature the emitter would declare.
 *
 * Any total function will do - what is being checked is that the emitter
 * APPLIES the symbol the way the evaluator does - so the interpretation is a
 * cheap hash of the argument values. It must be a FUNCTION (equal arguments
 * give equal results), which is why it hashes the values rather than drawing
 * them randomly.
 */
function darInterpretation(ufSorts) {
  const interp = {};
  for (const [name, sig] of ufSorts) {
    interp[name] = (...args) => {
      let h = 0;
      const mix = (key) => {
        for (let i = 0; i < key.length; i++) h = ((h << 5) - h + key.charCodeAt(i)) | 0;
      };
      for (const a of args) {
        mix(typeof a === 'string' || typeof a === 'boolean' ? String(a) : `${a.p}/${a.q}`);
      }
      mix(name);
      if (sig.ret === 'Bool') return (h & 1) === 0;
      if (sig.ret === 'String') return `s${Math.abs(h % 97)}`;
      return ratNorm(BigInt(h % 1000), 7n);
    };
  }
  return interp;
}

/** Does the term contain an Int -> Real coercion anywhere? */
function containsCoercion(term) {
  if (!term || typeof term !== 'object') return false;
  if (term.k === 'toreal') return true;
  if (term.k === 'app' || term.k === 'uf') return term.args.some(containsCoercion);
  if (term.k === 'ite') return [term.c, term.a, term.b].some(containsCoercion);
  return false;
}

function containsOp(term, ops) {
  if (!term || typeof term !== 'object') return false;
  if (term.k === 'app') return ops.includes(term.op) || term.args.some((a) => containsOp(a, ops));
  if (term.k === 'ite') return [term.c, term.a, term.b].some((a) => containsOp(a, ops));
  if (term.k === 'toreal') return containsOp(term.a, ops);
  return false;
}

test(
  'differential smoke test over REAL translated terms from a live DAR',
  { skip: (!SOLVER && NO_SOLVER_MSG) || (!HAVE_DAR && `DAR not present at ${DAR_PATH}`) },
  (t) => {
    // This closes the loop on terms the translator ACTUALLY produces (real
    // variable names with dots, real Numeric literals), not just synthetic
    // shapes. It still only tests emitter/evaluator agreement on points; it
    // says nothing about whether the translation matches Daml-LF semantics.
    const raw = readDarRaw(DAR_PATH);
    const transitions = extractTransitions(raw);
    assert.ok(transitions.length > 0, 'DAR yielded no transitions');

    // collect candidate terms: guards (Bool roots), create-field values and
    // division denominators (numeric roots), all free of unsupported nodes
    const candidates = [];
    for (const tr of transitions) {
      for (const g of tr.guards) candidates.push({ term: g, rootSort: 'Bool' });
      for (const c of tr.creates) {
        // The root sort is INFERRED, not asserted: a created field or a
        // denominator may be Int-sorted (a declared `Int` field, an INT64
        // arithmetic chain, a `div`), and forcing Real on it would turn a
        // perfectly well-sorted real term into a skipped sort conflict - which
        // is coverage silently lost rather than a check.
        for (const f of Object.values(c.fields)) if (f) candidates.push({ term: f, rootSort: null });
      }
      for (const d of tr.divisions) candidates.push({ term: d.denominator, rootSort: null });
    }

    const rnd = mulberry32(SEED ^ 0xda5);
    const cases = [];
    let eligible = 0;
    let intRooted = 0;
    let skippedDirty = 0;
    let skippedSort = 0;
    let skippedUndef = 0;
    let withUf = 0;
    // A probe variable unified with the term's own class, so the ROOT's
    // resolved sort can be read back off `sorts`. It occurs in no term, so it
    // is never declared or bound and cannot perturb the query.
    const ROOT_PROBE = '$root';
    for (const { term, rootSort } of candidates) {
      if (hasUnsupported(term) || !termIsClean(term)) {
        skippedDirty++;
        continue;
      }
      const rootClass = rootSort || 'root$class';
      const { sorts, conflicts, ufs } = inferSorts([
        { term, sort: rootClass },
        { term: T.varRef(ROOT_PROBE, null), sort: rootClass },
      ]);
      // A genuine sort conflict - a term mixing `div` with real division, an
      // Int-declared field in a Numeric arithmetic chain - is not a case: the
      // emitter refuses such a query too, so there is nothing to agree about.
      if (conflicts.length) {
        skippedSort++;
        continue;
      }
      eligible++;
      if (ufs.size) withUf++;
      const interp = darInterpretation(ufs);
      for (let i = 0; i < 3; i++) {
        const env = new Map();
        const varSorts = new Map();
        // Every variable is bound AT ITS INFERRED SORT, which is what keeps an
        // Int-sorted symbol integral on both sides: the evaluator refuses a
        // non-integer under `to_real` and valueToSmt refuses to render one as
        // an Int literal, so a mismatch here fails loudly instead of being
        // papered over.
        for (const name of varsOf(term)) {
          const sort = sorts.get(name) || 'Real';
          varSorts.set(name, sort);
          env.set(
            name,
            sort === 'Bool'
              ? chance(rnd, 0.5)
              : sort === 'String'
                ? `t${Math.floor(rnd() * 5)}`
                : sort === 'Int'
                  ? randomInt(rnd)
                  : randomRat(rnd)
          );
        }
        let expected;
        try {
          expected = evalTerm(term, env, interp);
        } catch (e) {
          skippedSort++; // e.g. a fractional literal feeding div
          continue;
        }
        if (isUndef(expected)) {
          skippedUndef++;
          continue;
        }
        cases.push({
          term, env, varSorts, expected, interp, ufSorts: ufs,
          expectedSort: sorts.get(ROOT_PROBE) || 'Real',
          mode: 'Real',
        });
      }
    }

    intRooted = cases.filter((c) => c.expectedSort === 'Int').length;
    const coerced = cases.filter((c) => containsCoercion(c.term)).length;
    t.diagnostic(
      `DAR terms: ${candidates.length} candidates, ${eligible} eligible ` +
        `(${withUf} applying an uninterpreted symbol), ${skippedDirty} outside the fragment, ` +
        `${skippedSort} sort-skipped, ${skippedUndef} undef; ${cases.length} differential cases ` +
        `(${intRooted} Int-rooted, ${coerced} carrying an Int -> Real coercion)`
    );
    assert.ok(eligible > 0, 'no eligible terms in the DAR: the smoke test checked nothing');
    // The DAR does abstract text operations; if that stopped happening, this
    // test would quietly stop covering the uninterpreted path.
    assert.ok(withUf > 0, 'no DAR term applied an uninterpreted symbol');
    assert.ok(cases.length > 0, 'no checkable cases from the DAR');

    const failures = differential(cases);
    assert.equal(
      failures.length,
      0,
      `${failures.length} live-DAR case(s) where the evaluator and the emitter disagree:\n\n${failures.join('\n\n')}`
    );
  }
);

// ============================================ differential: the Party sort
//
// The authorisation property (smt.js: createAuthority) introduces a sort the
// emitter had no previous reason to speak: an UNINTERPRETED `Party`, whose
// only operation is equality. Nothing in the arithmetic differential harness
// above reaches it - there is no value to bind a party to - so it gets its own
// cross-check, and it is worth having precisely because a false PROVED here
// would be a security-relevant lie rather than a wrong number.
//
// The model of an uninterpreted sort is fixed by saying which constants are
// equal. A case therefore draws a random PARTITION of the party constants;
// the query asserts that partition (equalities inside a class, disequalities
// across classes) and the evaluator is given the same partition as class
// tokens. If the emitted goal and the evaluated goal ever disagree, the goal
// construction, the sort emission or the evaluator's equality is wrong.

/** A random partition of `names` into at most `k` classes. */
function randomPartition(rnd, names, k) {
  const classes = new Map();
  for (const n of names) classes.set(n, `c${Math.floor(rnd() * k)}`);
  return classes;
}

/** A create-authority goal over party constants, plus the parties it names. */
function authorityCase(required, authority) {
  const cover = (s) => ({
    k: 'app',
    op: 'or',
    args: authority.map((a) => ({ k: 'app', op: '=', args: [T.party(s), T.party(a)] })),
  });
  const goals = required.map(cover);
  const goal = goals.length === 1 ? goals[0] : { k: 'app', op: 'and', args: goals };
  const names = [...new Set([...required, ...authority])].map((p) => T.party(p).name);
  return { goal, names };
}

test(
  'differential: an uninterpreted Party agrees with the evaluator on every partition',
  { skip: !SOLVER && 'cvc5 not installed' },
  (t) => {
    const rnd = mulberry32(SEED ^ 0x9a27);
    const shapes = [
      { required: ['this.admin'], authority: ['this.admin'] },
      { required: ['this.admin'], authority: ['this.owner'] },
      { required: ['this.admin', 'arg.newOwner'], authority: ['this.admin', 'arg.actor'] },
      { required: ['this.gov.approver'], authority: ['this.admin', 'this.gov.approver'] },
      { required: ['a', 'b', 'c'], authority: ['b', 'd'] },
    ];
    let checked = 0;
    const failures = [];
    for (const shape of shapes) {
      const { goal, names } = authorityCase(shape.required, shape.authority);
      const { sorts } = inferSorts([{ term: goal, sort: 'Bool' }]);
      for (const n of names) {
        assert.equal(sorts.get(n), 'Party', `${n} must be Party-sorted, not defaulted to Real`);
      }
      for (let i = 0; i < 12; i++) {
        const partition = randomPartition(rnd, names, 1 + Math.floor(rnd() * names.length));
        const env = new Map();
        for (const [n, c] of partition) env.set(n, party(c));
        const expected = evalTerm(goal, env);
        assert.equal(typeof expected, 'boolean');

        const lines = ['(set-logic ALL)', '(declare-sort Party 0)'];
        for (const n of names) lines.push(`(declare-const |${n}| Party)`);
        // Pin the model: same class means equal, different classes distinct.
        for (let a = 0; a < names.length; a++) {
          for (let b = a + 1; b < names.length; b++) {
            const same = partition.get(names[a]) === partition.get(names[b]);
            const eq = `(= |${names[a]}| |${names[b]}|)`;
            lines.push(`(assert ${same ? eq : `(not ${eq})`})`);
          }
        }
        lines.push(`(assert (not (= ${termToSmt(goal, true)} ${expected})))`);
        lines.push('(check-sat)');
        const out = runSolver(lines.join('\n') + '\n');
        checked++;
        if (!/^unsat/m.test(out)) {
          failures.push(
            `partition ${JSON.stringify(Object.fromEntries(partition))} expected ${expected}\n` +
              lines.join('\n') +
              `\nsolver said:\n${out}`
          );
        }
      }
    }
    t.diagnostic(`Party differential: ${checked} partition case(s)`);
    assert.equal(failures.length, 0, failures.join('\n\n'));
  }
);

// ==================================== differential: declared datatype sorts
//
// A Daml enum (and a variant's discriminant) becomes an SMT ALGEBRAIC DATATYPE
// declared with exactly the constructors the package declares, and the only
// operation on it is equality. Unlike an uninterpreted function there is
// nothing to pin: SMT-LIB fixes the meaning of a datatype's nullary
// constructors - they are pairwise distinct and they exhaust the sort - so the
// emitter and the evaluator must agree with no interpretation supplied at all.
//
// Both of those facts are exercised here, and the second one is the load-
// bearing half: the EXHAUSTIVENESS of the declared list is what makes a
// `_ ->` catch-all sound as the negation of the alternatives above it. If the
// sort admitted a value outside the declaration, `not C1 and not C2 => C3`
// would be false in the solver and true in the evaluator, and this test would
// say so.

const COLOR = 'enum M:Color@diffpkg';
const COLOR_CTORS = ['Red', 'Green', 'Blue'];
const TAG = 'variant M:Result@diffpkg';
const TAG_CTORS = ['Ok', 'Err'];

const dc = (sort, ctors) => (ctor) => T.dcon(sort, ctor, ctors);
const color = dc(COLOR, COLOR_CTORS);
const tag = dc(TAG, TAG_CTORS);

/** The SMT symbol a datatype value renders as, matching smt.js's dconSymbol. */
const dconSmt = (v) => smtSym(`${v.dconSort}#${v.ctor}`);

/**
 * A self-contained differential script for a term over datatype sorts.
 * Declares every sort the term mentions from the term's OWN constructor lists
 * (which is what buildQuery does), binds each variable to its value, and asks
 * whether the emitted term can differ from what the evaluator computed.
 */
function datatypeScript(term, env, expected) {
  const expectedSort =
    typeof expected === 'boolean' ? 'Bool' : isDcon(expected) ? expected.dconSort : 'Real';
  const { sorts, conflicts, datatypes } = inferSorts([{ term, sort: expectedSort }]);
  assert.deepEqual(conflicts, [], 'a differential case must be well sorted');
  const sortText = (name) => (datatypes.has(name) ? smtSym(name) : name);
  const lines = ['(set-logic ALL)'];
  for (const [name, ctors] of [...datatypes.entries()].sort()) {
    lines.push(
      `(declare-datatypes ((${smtSym(name)} 0)) ((${ctors
        .map((c) => `(${smtSym(`${name}#${c}`)})`)
        .join(' ')})))`
    );
  }
  for (const [name, sort] of [...sorts.entries()].sort()) {
    lines.push(`(declare-const ${smtSym(name)} ${sortText(sort)})`);
    const value = env[name];
    lines.push(
      `(assert (= ${smtSym(name)} ${isDcon(value) ? dconSmt(value) : valueToSmt(value, sort)}))`
    );
  }
  const expectedSmt = isDcon(expected)
    ? dconSmt(expected)
    : valueToSmt(expected, expectedSort === 'Bool' ? 'Bool' : 'Real');
  lines.push(`(assert (not (= ${termToSmt(term, true)} ${expectedSmt})))`);
  lines.push('(check-sat)');
  return lines.join('\n') + '\n';
}

test(
  'differential: datatype equality and case chains agree with the evaluator',
  { skip: !SOLVER && NO_SOLVER_MSG },
  (t) => {
    const rnd = mulberry32(SEED ^ 0xda7a);
    const failures = [];
    let checked = 0;

    // A case chain over a scrutinee variable, with a catch-all: exactly the
    // shape translateDataCase builds.
    const chain = (scrut, ctors, bodies, fallback) => {
      let out = fallback;
      for (let i = ctors.length - 1; i >= 0; i--) {
        out = T.ite(T.app('=', [scrut, color(ctors[i])]), bodies[i], out);
      }
      return out;
    };

    for (let i = 0; i < 60; i++) {
      const cv = pick(rnd, COLOR_CTORS);
      const tv = pick(rnd, TAG_CTORS);
      const env = { 'this.shade': dcon(COLOR, cv), 'this.status': dcon(TAG, tv) };
      const shade = T.varRef('this.shade', 'Real');
      const status = T.varRef('this.status', 'Real');

      // 1. plain equality, both against a constant and between two variables
      const terms = [
        T.app('=', [shade, color(pick(rnd, COLOR_CTORS))]),
        T.app('=', [status, tag(pick(rnd, TAG_CTORS))]),
        T.app('not', [T.app('=', [shade, color(pick(rnd, COLOR_CTORS))])]),
        // 2. an EXHAUSTIVE chain with the last test dropped - the step whose
        //    soundness rests on the sort being closed over the declared list
        chain(shade, ['Red', 'Green'], [T.num('1'), T.num('2')], T.num('3')),
        // 3. a chain with a catch-all, i.e. the negation of what is above it
        chain(shade, ['Blue'], [T.num('7')], T.num('9')),
        // 4. a datatype-VALUED conditional: the branches share the sort
        T.ite(T.app('=', [status, tag('Ok')]), color('Red'), shade),
      ];

      for (const term of terms) {
        const expected = evalTerm(term, env);
        const script = datatypeScript(term, env, expected);
        const out = runSolver(script);
        checked++;
        if (!/^unsat/m.test(out)) {
          failures.push(
            `env ${JSON.stringify({ shade: cv, status: tv })} expected ` +
              `${isDcon(expected) ? expected.ctor : showValue(expected)}\n${script}\nsolver said:\n${out}`
          );
        }
      }
    }
    t.diagnostic(`datatype differential: ${checked} case(s)`);
    assert.equal(failures.length, 0, failures.slice(0, 2).join('\n\n'));
  }
);

test('evalTerm: datatype constants need no interpretation, and never mix sorts', () => {
  // Distinctness of nullary constructors is part of the theory, so the term
  // alone fixes the value - unlike a uf, which throws without one.
  assert.deepEqual(evalTerm(color('Red'), {}), dcon(COLOR, 'Red'));
  assert.equal(evalTerm(T.app('=', [color('Red'), color('Red')]), {}), true);
  assert.equal(evalTerm(T.app('=', [color('Red'), color('Green')]), {}), false);
  // A variable of the sort takes its value from the environment, like a party.
  const env = { x: dcon(COLOR, 'Blue') };
  assert.equal(evalTerm(T.app('=', [T.varRef('x', 'Real'), color('Blue')]), env), true);
  assert.equal(evalTerm(T.app('=', [T.varRef('x', 'Real'), color('Red')]), env), false);
  // Comparing across sorts is not a well-sorted question and must throw rather
  // than answer false - a silent false would agree with the emitter for the
  // wrong reason, exactly what the party sort's own rule exists to prevent.
  assert.throws(
    () => evalTerm(T.app('=', [color('Red'), tag('Ok')]), {}),
    /two different datatype sorts/
  );
  assert.throws(
    () => evalTerm(T.app('=', [color('Red'), T.varRef('p', 'Real')]), { p: party('p1') }),
    /mixes a datatype constructor with another sort/
  );
  assert.throws(
    () => evalTerm(T.app('+', [color('Red'), T.num('1')]), {}),
    /expected numeric/
  );
});

test('evalTerm: an Optional VALUE is a pair, not a scalar', () => {
  // The emitter's matching refusal is pinned in tests/verify.test.js. Keeping
  // both means neither side can start treating half the pair as a value
  // without the other noticing.
  assert.throws(
    () => evalTerm(T.opt(T.bool(true), T.num('1')), {}),
    /\$some\/\$value pair, not a scalar/
  );
});
