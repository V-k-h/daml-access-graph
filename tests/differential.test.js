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
  if (!isRat(v)) throw new Error('valueToSmt: not a boolean or rational');
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

const NUM_VARS = ['n0', 'n1', 'n2', 'n3'];
const BOOL_VARS = ['b0', 'b1'];

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

function genNum(rnd, depth, mode) {
  const lit = () => T.num(pick(rnd, mode === 'Int' ? INT_LITERALS : REAL_LITERALS));
  const vr = () => T.varRef(pick(rnd, NUM_VARS), mode === 'Int' ? 'Int' : 'Real');
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
  if (roll < 0.9) {
    const op = mode === 'Int' ? (chance(rnd, 0.5) ? 'div' : 'mod') : '/';
    return T.app(op, [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)]);
  }
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
  if (roll < 0.92) {
    // polymorphic equality: numeric or boolean operands
    return chance(rnd, 0.7)
      ? T.app('=', [genNum(rnd, depth - 1, mode), genNum(rnd, depth - 1, mode)])
      : T.app('=', [genBool(rnd, depth - 1, mode), genBool(rnd, depth - 1, mode)]);
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
  for (const n of NUM_VARS) env.set(n, mode === 'Int' ? randomInt(rnd) : randomRat(rnd));
  for (const b of BOOL_VARS) env.set(b, chance(rnd, 0.5));
  return env;
}

/** Variable names occurring in a term (only those get declared and bound). */
function varsOf(term, out = new Set()) {
  if (!term || typeof term !== 'object') return out;
  if (term.k === 'var') out.add(term.name);
  else if (term.k === 'app') term.args.forEach((a) => varsOf(a, out));
  else if (term.k === 'ite') [term.c, term.a, term.b].forEach((a) => varsOf(a, out));
  return out;
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
  const expectedSort = typeof c.expected === 'boolean' ? 'Bool' : c.mode === 'Int' ? 'Int' : 'Real';
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
    const expected = evalTerm(term, env);
    if (isUndef(expected)) {
      // division by zero on the needed path: SMT calls the value unspecified,
      // so there is no concrete expectation to check - skip, never assert
      skippedUndef++;
      continue;
    }
    const numSort = mode === 'Int' ? 'Int' : 'Real';
    const varSorts = new Map();
    for (const n of NUM_VARS) varSorts.set(n, numSort);
    for (const b of BOOL_VARS) varSorts.set(b, 'Bool');
    cases.push({ term, env, varSorts, expected, mode });
  }

  t.diagnostic(`generated ${attempts} term/env pairs; checked ${cases.length}; skipped ${skippedUndef} undef (div0)`);
  assert.ok(cases.length >= 500, `only ${cases.length} checkable cases generated (skip rate too high)`);

  const failures = differential(cases);
  assert.equal(
    failures.length,
    0,
    `${failures.length} case(s) where the evaluator and the emitter disagree:\n\n${failures.join('\n\n')}`
  );
});

// ================================================== live-DAR smoke test

const DAR_PATH =
  '/private/tmp/claude-501/-Users-vijay-Downloads-carbon-core/713989a1-4f06-45ac-823b-b4ec40f8b2b8/scratchpad/canton/dlt-canton-main/daml/canton-tokens.dar';
const HAVE_DAR = existsSync(DAR_PATH);

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
    case 'app':
      return (
        ['+', '-', '*', '/', 'div', 'mod', '<', '<=', '>', '>=', '=', 'not', 'and', 'or'].includes(term.op) &&
        term.args.length > 0 &&
        term.args.every(termIsClean)
      );
    case 'ite':
      return [term.c, term.a, term.b].every(termIsClean);
    default:
      return false; // record, unsupported, anything unknown
  }
}

function containsOp(term, ops) {
  if (!term || typeof term !== 'object') return false;
  if (term.k === 'app') return ops.includes(term.op) || term.args.some((a) => containsOp(a, ops));
  if (term.k === 'ite') return [term.c, term.a, term.b].some((a) => containsOp(a, ops));
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
        for (const f of Object.values(c.fields)) if (f) candidates.push({ term: f, rootSort: 'Real' });
      }
      for (const d of tr.divisions) candidates.push({ term: d.denominator, rootSort: 'Real' });
    }

    const rnd = mulberry32(SEED ^ 0xda5);
    const cases = [];
    let eligible = 0;
    let skippedDirty = 0;
    let skippedSort = 0;
    let skippedUndef = 0;
    for (const { term, rootSort } of candidates) {
      if (hasUnsupported(term) || !termIsClean(term)) {
        skippedDirty++;
        continue;
      }
      // div/mod force Int-sorted variables; a term mixing them with real
      // division or fractional literals is not well-sorted for this check
      const intMode = containsOp(term, ['div', 'mod']);
      if (intMode && containsOp(term, ['/'])) {
        skippedSort++;
        continue;
      }
      const { sorts, conflicts } = inferSorts([{ term, sort: rootSort }]);
      if (conflicts.length) {
        skippedSort++;
        continue;
      }
      eligible++;
      const numSort = intMode ? 'Int' : 'Real';
      for (let i = 0; i < 3; i++) {
        const env = new Map();
        const varSorts = new Map();
        for (const name of varsOf(term)) {
          const sort = sorts.get(name) === 'Bool' ? 'Bool' : numSort;
          varSorts.set(name, sort);
          env.set(name, sort === 'Bool' ? chance(rnd, 0.5) : intMode ? randomInt(rnd) : randomRat(rnd));
        }
        let expected;
        try {
          expected = evalTerm(term, env);
        } catch (e) {
          skippedSort++; // e.g. a fractional literal feeding div in Int mode
          continue;
        }
        if (isUndef(expected)) {
          skippedUndef++;
          continue;
        }
        cases.push({ term, env, varSorts, expected, mode: intMode ? 'Int' : 'Real' });
      }
    }

    t.diagnostic(
      `DAR terms: ${candidates.length} candidates, ${eligible} eligible, ` +
        `${skippedDirty} outside the fragment, ${skippedSort} sort-skipped, ${skippedUndef} undef; ` +
        `${cases.length} differential cases`
    );
    assert.ok(eligible > 0, 'no eligible terms in the DAR: the smoke test checked nothing');
    assert.ok(cases.length > 0, 'no checkable cases from the DAR');

    const failures = differential(cases);
    assert.equal(
      failures.length,
      0,
      `${failures.length} live-DAR case(s) where the evaluator and the emitter disagree:\n\n${failures.join('\n\n')}`
    );
  }
);
