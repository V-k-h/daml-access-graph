// tests/verify.test.js
//
//   node --test
//
// The verification pipeline: IR helpers, the SMT emitter, the property
// definitions, and (when a solver is installed) a live proof and a live
// counterexample through cvc5.
//
// What is deliberately NOT tested here: that the translator's output matches
// Daml-LF semantics. That is the pipeline's stated trust gap - lfir.js is
// tested on shapes, not verified against the spec - and pretending a unit
// test discharges it would be the same overclaim these tools exist to avoid.

import test from 'node:test';
import assert from 'node:assert/strict';
import { execFileSync, spawnSync } from 'node:child_process';
import { writeFileSync, mkdtempSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import {
  T,
  hasUnsupported,
  unsupportedReasons,
  divisors,
  instantiateFolds,
  foldLists,
  DEFAULT_BOUND,
} from '../backend/lfir.js';
import {
  termToSmt,
  inferSorts,
  buildQuery,
  usableGuards,
  amountConservation,
  divisionSafety,
  nonNegativeFields,
  createAuthority,
} from '../backend/smt.js';

const v = (name) => T.varRef(name, 'Real');
const eq = (a, b) => T.app('=', [a, b]);
const plus = (a, b) => T.app('+', [a, b]);

function hasSolver() {
  try {
    execFileSync('cvc5', ['--version'], { stdio: 'ignore', timeout: 5000 });
    return true;
  } catch (_) {
    return false;
  }
}
const SOLVER = hasSolver();

// A real compiled package, used by the end-to-end tests below. Declared here
// rather than next to them because `skip` options are evaluated when a test is
// REGISTERED, which happens before any later `const` is initialized.
const TOKENS_DAR =
  '/private/tmp/claude-501/-Users-vijay-Downloads-carbon-core/713989a1-4f06-45ac-823b-b4ec40f8b2b8/scratchpad/canton/dlt-canton-main/daml/canton-tokens.dar';
const HAVE_TOKENS_DAR = existsSync(TOKENS_DAR);

// ------------------------------------------------------------------ helpers

test('hasUnsupported sees through app and ite nesting', () => {
  const clean = T.ite(eq(v('a'), v('b')), plus(v('a'), T.num('1')), v('b'));
  assert.equal(hasUnsupported(clean), false);
  const dirty = T.app('+', [v('a'), T.ite(T.bool(true), T.unsupported('x', 'here'), v('b'))]);
  assert.equal(hasUnsupported(dirty), true);
  assert.deepEqual(unsupportedReasons(dirty).map((u) => u.why), ['x']);
});

test('divisors collects every denominator, nested included', () => {
  const t = T.app('+', [
    T.app('/', [v('a'), v('b')]),
    T.ite(T.bool(true), T.app('div', [v('c'), T.app('/', [v('d'), v('e')])]), T.num('0')),
  ]);
  assert.deepEqual(divisors(t).map((d) => d.name || d.k), ['b', 'app', 'e']);
});

// ---------------------------------------------------------------------- smt

test('termToSmt renders the fragment, and only the fragment', () => {
  assert.equal(termToSmt(T.num('10.0000000000')), '10.0000000000');
  assert.equal(termToSmt(T.num('-1.5')), '(- 1.5)');
  assert.equal(termToSmt(v('this.amount')), '|this.amount|');
  assert.equal(termToSmt(eq(plus(v('a'), v('b')), T.num('0'))), '(= (+ |a| |b|) 0)');
  assert.equal(
    termToSmt(T.ite(T.bool(true), v('a'), v('b'))),
    '(ite true |a| |b|)'
  );
  // reaching the emitter with an unsupported node is a caller bug -> throw
  assert.throws(() => termToSmt(T.unsupported('nope', 'x')), /unsupported term/);
  assert.throws(() => termToSmt(T.record('this')), /whole record/);
  assert.throws(() => termToSmt(T.app('shell', [v('a')])), /unknown operator/);
});

test('inferSorts: position decides, conflicts are surfaced', () => {
  const guard = T.app('not', [v('flag')]);
  const goal = eq(v('x'), T.num('1'));
  const { sorts, conflicts } = inferSorts([
    { term: guard, sort: 'Bool' },
    { term: goal, sort: 'Bool' },
  ]);
  assert.equal(sorts.get('flag'), 'Bool');
  assert.equal(sorts.get('x'), 'Real');
  assert.deepEqual(conflicts, []);

  // the same variable as a Bool and inside arithmetic must conflict, not win by order
  const bad = inferSorts([
    { term: T.app('not', [v('y')]), sort: 'Bool' },
    { term: eq(plus(v('y'), T.num('1')), T.num('2')), sort: 'Bool' },
  ]);
  assert.ok(bad.conflicts.length > 0);
});

test('buildQuery asserts guards and the negated goal', () => {
  const { script, vars } = buildQuery(
    [T.app('>', [v('x'), T.num('0')])],
    T.app('>', [plus(v('x'), T.num('1')), T.num('1')])
  );
  assert.match(script, /\(declare-const \|x\| Real\)/);
  // buildQuery renders numerals as Real literals: every numeric position it
  // emits is Real, and a bare numeral is an Int that cvc5 refuses as an `ite`
  // branch against one (see termToSmt's realNumerals).
  assert.match(script, /\(assert \(> \|x\| 0\.0\)\)/);
  assert.match(script, /\(assert \(not \(> \(\+ \|x\| 1\.0\) 1\.0\)\)\)/);
  assert.match(script, /\(check-sat\)/);
  assert.deepEqual(vars, ['x']);
});

// ----------------------------------------------------------------- property

/** A minimal transition record, the shape extractTransitions emits. */
function transition(overrides = {}) {
  return {
    module: 'M',
    template: 'Tok',
    choice: 'C',
    consuming: true,
    guards: [],
    pathConditions: [],
    creates: [],
    divisions: [],
    rounding: [],
    unsupported: [],
    ...overrides,
  };
}

test('amount-conservation: lock shape is applicable and states the right goal', () => {
  const t = transition({
    creates: [{ template: 'LockedTok', base: null, fields: { amount: v('this.amount') }, path: [] }],
  });
  const inst = amountConservation(t);
  assert.equal(inst.applicable, true);
  assert.equal(termToSmt(inst.goal), '(= |this.amount| |this.amount|)');
});

test('amount-conservation: a split sums the created amounts', () => {
  const t = transition({
    creates: [
      { template: 'Tok', base: null, fields: { amount: v('arg.amount') }, path: [] },
      {
        template: 'Tok',
        base: null,
        fields: { amount: T.app('-', [v('this.amount'), v('arg.amount')]) },
        path: [],
      },
    ],
  });
  const inst = amountConservation(t);
  assert.equal(inst.applicable, true);
  assert.equal(
    termToSmt(inst.goal),
    '(= (+ |arg.amount| (- |this.amount| |arg.amount|)) |this.amount|)'
  );
});

test('amount-conservation: refusals are explicit, never silent passes', () => {
  // nonconsuming: archiving nothing, conserving nothing
  assert.equal(amountConservation(transition({ consuming: false })).applicable, false);
  // no creates
  assert.match(amountConservation(transition()).why, /creates nothing/);
  // an amount outside the fragment
  const dirty = transition({
    creates: [{ template: 'T', base: null, fields: { amount: T.unsupported('helper call', 'x') }, path: [] }],
  });
  assert.match(amountConservation(dirty).why, /outside the translated fragment/);
  // rounding on the path: exact-Real equality would be unsound, so refuse
  const rounded = transition({
    rounding: ['ROUND_NUMERIC'],
    creates: [{ template: 'T', base: null, fields: { amount: v('this.amount') }, path: [] }],
  });
  assert.match(amountConservation(rounded).why, /rounding/);
});

test('amount-conservation: `create this` with no amount override inherits it', () => {
  const t = transition({
    creates: [{ template: 'Tok', base: 'this', fields: {}, path: [] }],
  });
  const inst = amountConservation(t);
  assert.equal(inst.applicable, true);
  assert.equal(termToSmt(inst.goal), '(= |this.amount| |this.amount|)');
});

test('division-safety builds a nonzero goal per denominator', () => {
  const t = transition({
    divisions: [{ denominator: v('arg.price') }, { denominator: plus(v('a'), v('b')) }],
  });
  const inst = divisionSafety(t);
  assert.equal(inst.applicable, true);
  assert.match(termToSmt(inst.goal), /\(not \(= \|arg\.price\| 0\)\)/);
  assert.match(termToSmt(inst.goal), /\(not \(= \(\+ \|a\| \|b\|\) 0\)\)/);
});

test('usableGuards drops untranslatable guards and reports each drop', () => {
  const good = T.app('>', [v('x'), T.num('0')]);
  const bad = T.ite(T.unsupported('ensure helper', 'T.ensure'), T.bool(true), T.bool(false));
  const { used, dropped } = usableGuards(transition({ guards: [good, bad] }));
  assert.deepEqual(used, [good]);
  assert.equal(dropped.length, 1);
  assert.deepEqual(dropped[0], ['ensure helper']);
});

// -------------------------------------------------------------- live solver

test('cvc5 proves a valid implication (unsat)', { skip: !SOLVER }, () => {
  const { script } = buildQuery(
    [T.app('>', [v('x'), T.num('0')])],
    T.app('>', [plus(v('x'), T.num('1')), T.num('1')])
  );
  const out = runSolver(script);
  assert.match(out, /^unsat/m);
});

test('cvc5 refutes an invalid claim with a model (sat)', { skip: !SOLVER }, () => {
  // x > 0 does NOT imply x > 1; the model must witness it
  const { script } = buildQuery(
    [T.app('>', [v('x'), T.num('0')])],
    T.app('>', [v('x'), T.num('1')])
  );
  const out = runSolver(script);
  assert.match(out, /^sat/m);
  assert.match(out, /define-fun/);
});

test('cvc5 proves conservation for the split shape', { skip: !SOLVER }, () => {
  // the property that matters on token UTXOs: a + (total - a) = total
  const inst = amountConservation(
    transition({
      creates: [
        { template: 'T', base: null, fields: { amount: v('arg.amount') }, path: [] },
        {
          template: 'T',
          base: null,
          fields: { amount: T.app('-', [v('this.amount'), v('arg.amount')]) },
          path: [],
        },
      ],
    })
  );
  const out = runSolver(buildQuery(inst.guards, inst.goal).script);
  assert.match(out, /^unsat/m);
});

function runSolver(script) {
  const dir = mkdtempSync(join(tmpdir(), 'dvt-'));
  const file = join(dir, 'q.smt2');
  writeFileSync(file, script);
  try {
    return execFileSync('cvc5', ['--lang', 'smt2', file], { encoding: 'utf8', timeout: 15000 });
  } catch (e) {
    return `${e.stdout || ''}${e.stderr || ''}`;
  }
}

// ---------------------------------------------------------------------------
// Guard conjuncts, aborts, text, Optional, interface-instance transitions
// ---------------------------------------------------------------------------

import { decodeMessage } from '../backend/protobuf.js';
import * as S from '../backend/lf2-schema.js';
import { decodeDalfRaw, readDarRaw } from '../backend/dalf.js';
import {
  guardConjuncts,
  translateExpr,
  makeCtx,
  extractTransitions,
  BF,
} from '../backend/lfir.js';

// protobuf encoding helpers (test-only), same style as dalf.test.js
function varint(n) {
  const bytes = [];
  let v = n;
  do {
    let b = v & 0x7f;
    v = Math.floor(v / 128);
    if (v > 0) b |= 0x80;
    bytes.push(b);
  } while (v > 0);
  return Buffer.from(bytes);
}
const tag = (fieldNumber, wireType) => varint(fieldNumber * 8 + wireType);
const vf = (fieldNumber, value) => Buffer.concat([tag(fieldNumber, 0), varint(value)]);
const bf = (fieldNumber, buf) => Buffer.concat([tag(fieldNumber, 2), varint(buf.length), buf]);
const sf = (fieldNumber, str) => bf(fieldNumber, Buffer.from(str, 'utf8'));
const msg = (...parts) => Buffer.concat(parts);

test('guardConjuncts: throw-on-false and && shapes decompose into conjuncts', () => {
  const c = v('c');
  const a = T.app('>', [v('x'), T.num('0')]);
  // if c then a else throw  ->  [c, a]
  assert.deepEqual(guardConjuncts(T.ite(c, a, T.abort('throw'))), [c, a]);
  // if c then True else throw  ->  [c]   (the compiled `ensure c` shape)
  assert.deepEqual(guardConjuncts(T.ite(c, T.bool(true), T.abort('throw'))), [c]);
  // if c then False else b  ->  [not c, b]
  assert.deepEqual(guardConjuncts(T.ite(c, T.bool(false), a)), [T.app('not', [c]), a]);
  // nested &&-as-ite: if c1 then (if c2 then a else False) else False -> [c1, c2, a]
  const nested = T.ite(v('c1'), T.ite(v('c2'), a, T.bool(false)), T.bool(false));
  assert.deepEqual(guardConjuncts(nested), [v('c1'), v('c2'), a]);
  // explicit and() flattens; trivial `true` conjuncts vanish
  assert.deepEqual(guardConjuncts(T.app('and', [c, T.bool(true), a])), [c, a]);
  // an OR is NOT split: ite(c, True, b) must stay whole
  const orTerm = T.ite(c, T.bool(true), a);
  assert.deepEqual(guardConjuncts(orTerm), [orTerm]);
});

test('guardConjuncts: an abort it cannot eliminate degrades to unsupported, never asserted', () => {
  // abort buried inside a comparison, not a Bool branch: cannot be eliminated
  const bad = T.app('=', [T.ite(v('c'), T.num('1'), T.abort('call to error')), T.num('1')]);
  const [conj] = guardConjuncts(bad);
  assert.equal(hasUnsupported(conj), true);
  assert.match(unsupportedReasons(conj)[0].why, /abort/);
  // and usableGuards therefore drops it, with the reason reported
  const { used, dropped } = usableGuards(transition({ guards: [conj] }));
  assert.deepEqual(used, []);
  assert.match(dropped[0][0], /abort/);
});

test('abort counts as unsupported until eliminated', () => {
  assert.equal(hasUnsupported(T.abort('throw')), true);
  assert.match(unsupportedReasons(T.abort('throw'))[0].why, /abort/);
});

test('text literals render as SMT Strings; equality drives String sorts', () => {
  assert.equal(termToSmt(T.str('alpha')), '"alpha"');
  assert.equal(termToSmt(T.str('say "hi"')), '"say ""hi"""');
  const guard = eq(v('this.id'), T.str('alpha'));
  const { sorts, conflicts } = inferSorts([{ term: guard, sort: 'Bool' }]);
  assert.deepEqual(conflicts, []);
  assert.equal(sorts.get('this.id'), 'String');
  const { script } = buildQuery([guard], eq(v('this.id'), T.str('alpha')));
  assert.match(script, /\(declare-const \|this\.id\| String\)/);
  assert.match(script, /"alpha"/);
});

test('amount-conservation distinguishes refusals (notModellable) from non-applicability', () => {
  // untranslated body parts with no recovered creates: refusal, not a pass
  const lost = amountConservation(
    transition({ creates: [], unsupported: [{ why: 'exercise in the choice body' }] })
  );
  assert.equal(lost.applicable, false);
  assert.equal(lost.notModellable, true);
  // clean empty creates: genuinely not applicable
  const clean = amountConservation(transition());
  assert.equal(clean.notModellable, undefined);
  // rounding on the path is a refusal
  const rounded = amountConservation(
    transition({
      rounding: ['ROUND_NUMERIC'],
      creates: [{ template: 'T', base: null, fields: { amount: v('this.amount') }, path: [] }],
    })
  );
  assert.equal(rounded.notModellable, true);
});

// ------------------------------------------------- synthetic LF expressions

/** A minimal fake interning context for direct translateExpr tests. */
function fakePkg(strings) {
  return {
    str: (i) => strings[i],
    dname: (i) => `<dname:${i}>`,
    internedExprs: [],
    resolveValue: () => undefined,
    selfPackageId: 'testpkg',
  };
}

const exprVar = (si) => msg(vf(S.Expr.varInternedStr, si));
const exprProj = (recordExpr, fieldSi) =>
  msg(
    bf(
      S.Expr.recProj,
      msg(vf(S.RecProj.fieldInternedStr, fieldSi), bf(S.RecProj.record, recordExpr))
    )
  );
const exprInt = (n) => msg(bf(S.Expr.builtinLit, msg(vf(S.BuiltinLit.int64, n))));
const APP = S.message('Expr.App');
const exprApp = (funExpr, argExprs) =>
  msg(bf(S.Expr.app, msg(bf(APP.fun, funExpr), ...argExprs.map((a) => bf(APP.args, a)))));
const exprBuiltin = (b) => msg(vf(S.Expr.builtin, b));
const TYAPP = S.message('Expr.TyApp');
const TYABS = S.message('Expr.TyAbs');
const ABS = S.message('Expr.Abs');
const exprTyApp = (e) => msg(bf(S.Expr.tyApp, bf(TYAPP.expr, e)));
const exprTyAbs = (e) => msg(bf(S.Expr.tyAbs, bf(TYABS.body, e)));
const exprAbs = (paramSi, body) =>
  msg(
    bf(
      S.Expr.abs,
      msg(bf(ABS.param, msg(vf(S.VarWithType.varInternedStr, paramSi))), bf(ABS.body, body))
    )
  );

test('a builtin under type application/abstraction layers still translates', () => {
  // GREATER_EQ compiled as app(tyApp(tyAbs(tyApp(builtin))), this.amount, 5)
  const strings = ['this', 'amount'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  const wrapped = exprTyApp(exprTyAbs(exprTyApp(exprBuiltin(BF.GREATER_EQ))));
  const e = exprApp(wrapped, [exprProj(exprVar(0), 1), exprInt(5)]);
  const term = translateExpr(decodeMessage(e), ctx);
  assert.equal(termToSmt(term), '(>= |this.amount| 5)');
});

test('Optional case over a contract field becomes a $some/$value symbol pair', () => {
  const strings = ['this', 'opt', 'x'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  const CASE = S.message('Case');
  const altNone = msg(bf(S.CaseAlt.optionalNone, msg()), bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_FALSE))));
  const altSome = msg(
    bf(S.CaseAlt.optionalSome, msg(vf(S.OptionalSomeAlt.varBodyInternedStr, 2))),
    bf(S.CaseAlt.body, exprApp(exprBuiltin(BF.GREATER), [exprVar(2), exprInt(5)]))
  );
  const caseExpr = msg(
    bf(
      S.Expr.case,
      msg(bf(CASE.scrut, exprProj(exprVar(0), 1)), bf(CASE.alts, altNone), bf(CASE.alts, altSome))
    )
  );
  const term = translateExpr(decodeMessage(caseExpr), ctx);
  assert.equal(
    termToSmt(term),
    '(ite |this.opt.$some| (> |this.opt.$value| 5) false)'
  );
});

test('Optional case over a computed value is refused with a reason', () => {
  const strings = ['this', 'opt', 'x'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  const CASE = S.message('Case');
  const altNone = msg(bf(S.CaseAlt.optionalNone, msg()), bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_FALSE))));
  const altSome = msg(
    bf(S.CaseAlt.optionalSome, msg(vf(S.OptionalSomeAlt.varBodyInternedStr, 2))),
    bf(S.CaseAlt.body, exprVar(2))
  );
  // scrutinee is `this` itself (a record, not a registered Optional field)
  const caseExpr = msg(
    bf(
      S.Expr.case,
      msg(bf(CASE.scrut, exprVar(0)), bf(CASE.alts, altNone), bf(CASE.alts, altSome))
    )
  );
  const term = translateExpr(decodeMessage(caseExpr), ctx);
  assert.equal(term.k, 'unsupported');
  assert.match(term.why, /Optional case/);
});

test('an Optional case naming ONE constructor plus `_` is still the $some encoding', () => {
  // The compiled Eq instance for Optional writes `case x of None -> _; _ -> _`.
  // Refusing a case that spells out only one constructor made every
  // `field /= None` guard untranslatable; the catch-all simply binds nothing.
  const strings = ['this', 'opt'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  const CASE = S.message('Case');
  const altNone = msg(
    bf(S.CaseAlt.optionalNone, msg()),
    bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_TRUE)))
  );
  const altDefault = msg(
    bf(S.CaseAlt.default, msg()),
    bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_FALSE)))
  );
  const caseExpr = msg(
    bf(S.Expr.case, msg(bf(CASE.scrut, exprProj(exprVar(0), 1)), bf(CASE.alts, altNone), bf(CASE.alts, altDefault)))
  );
  const term = translateExpr(decodeMessage(caseExpr), ctx);
  assert.equal(termToSmt(term), '(ite |this.opt.$some| false true)');
});

test('a case on a LITERAL Optional constructor is evaluated, not abstracted', () => {
  // `case None of None -> True; _ -> False` IS True. This is evaluation: the
  // compiled Eq instance for Optional compares its argument against the
  // constant `None`, and without deciding that case the comparison dies.
  const strings = ['x'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: null, argParam: null, label: 't' });
  const CASE = S.message('Case');
  const altNone = msg(
    bf(S.CaseAlt.optionalNone, msg()),
    bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_TRUE)))
  );
  const altDefault = msg(
    bf(S.CaseAlt.default, msg()),
    bf(S.CaseAlt.body, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_FALSE)))
  );
  const noneExpr = msg(bf(S.Expr.optionalNone, msg()));
  const caseExpr = msg(
    bf(S.Expr.case, msg(bf(CASE.scrut, noneExpr), bf(CASE.alts, altNone), bf(CASE.alts, altDefault)))
  );
  assert.equal(termToSmt(translateExpr(decodeMessage(caseExpr), ctx)), 'true');

  // and the Some side binds the payload
  const SOME = S.message('Expr.OptionalSome');
  const someExpr = msg(bf(S.Expr.optionalSome, msg(bf(SOME.value, exprInt(7)))));
  const altSome = msg(
    bf(S.CaseAlt.optionalSome, msg(vf(S.OptionalSomeAlt.varBodyInternedStr, 0))),
    bf(S.CaseAlt.body, exprVar(0))
  );
  const caseSome = msg(
    bf(S.Expr.case, msg(bf(CASE.scrut, someExpr), bf(CASE.alts, altSome), bf(CASE.alts, altDefault)))
  );
  assert.equal(termToSmt(translateExpr(decodeMessage(caseSome), ctx)), '7');
});

test('a typeclass method is resolved through its dictionary, exactly', () => {
  // `x == y` compiles to `(structProj m_== $dEq) x y`. Resolving the struct to
  // the compiled instance picks the very implementation the call site runs;
  // left unresolved it died as "a function the translation cannot inline",
  // which is what made Optional and Text comparisons untranslatable.
  const strings = ['this', 'amount', 'm_==', 'dict'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  const STRUCTCON = S.message('Expr.StructCon');
  const FIELD = S.message('FieldWithExpr');
  const dict = msg(
    bf(
      S.Expr.structCon,
      msg(
        bf(
          STRUCTCON.fields,
          msg(vf(FIELD.fieldInternedStr, 2), bf(FIELD.expr, exprBuiltin(BF.EQUAL)))
        )
      )
    )
  );
  const method = msg(
    bf(S.Expr.structProj, msg(vf(S.StructProj.fieldInternedStr, 2), bf(S.StructProj.struct, dict)))
  );
  const e = exprApp(method, [exprProj(exprVar(0), 1), exprInt(3)]);
  assert.equal(termToSmt(translateExpr(decodeMessage(e), ctx)), '(= |this.amount| 3)');

  // a dictionary that does not reduce to a struct is refused BY NAME, so the
  // report says which method went unresolved rather than "some application"
  const opaque = msg(
    bf(S.Expr.structProj, msg(vf(S.StructProj.fieldInternedStr, 2), bf(S.StructProj.struct, exprVar(3))))
  );
  const bad = translateExpr(decodeMessage(opaque), ctx);
  assert.equal(bad.k, 'unsupported');
  assert.match(bad.why, /`m_==` projected off a value the translation could not reduce/);
});

test('nested projections through let-bound sub-records extend the symbol path', () => {
  const strings = ['this', 'contractData', 'investorId'];
  const ctx = makeCtx(fakePkg(strings), { selfParam: 'this', argParam: null, label: 't' });
  // let-free double projection chain: (this.contractData).investorId
  const e = exprProj(exprProj(exprVar(0), 1), 2);
  const term = translateExpr(decodeMessage(e), ctx);
  assert.equal(termToSmt(term), '|this.contractData.investorId|');
});

// ------------------------------------- interface instance -> transition, e2e

/**
 * A one-package DAR fixture with the real split/merge shape:
 *
 *   interface Utxo (choice Split, consuming, arg) whose update applies the
 *   hoisted value `Mod:splitImpl this self arg`;
 *   `Mod:splitImpl = \i -> call_interface @Utxo splitImpl i`;
 *   template Tok has an `interface instance` whose splitImpl method creates
 *   Tok twice: once with amount = arg.amount, once with this.amount - arg.amount.
 */
function buildInterfaceFixtureDalf() {
  const strings = ['this', 'self', 'arg', 'amount', 'i', 's2', 'a2', 'c1', 'c2', 'pkg', '1.0.0'];
  const SI = Object.fromEntries(strings.map((s, i) => [s, i]));
  const dnames = ['Mod', 'Tok', 'Utxo', 'splitImpl'];
  const DN = Object.fromEntries(dnames.map((s, i) => [s, i]));
  const stringTable = [...strings, ...dnames];
  const dnameIndex = (s) => stringTable.indexOf(s);

  const dnameMsgs = dnames.map((d) =>
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(dnameIndex(d))))
  );

  const selfModule = msg(
    bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
    vf(S.ModuleId.moduleNameInternedDname, DN.Mod)
  );
  const tyconTok = msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, DN.Tok));
  const tyconUtxo = msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, DN.Utxo));

  const CREATE = S.message('Update.Create');
  const createTok = (recordExpr) =>
    msg(bf(S.Expr.update, bf(S.Update.create, msg(bf(CREATE.template, tyconTok), bf(CREATE.expr, recordExpr)))));
  const updAmount = (valueExpr) =>
    msg(
      bf(
        S.Expr.recUpd,
        msg(
          vf(S.RecUpd.fieldInternedStr, SI.amount),
          bf(S.RecUpd.record, exprVar(SI.this)),
          bf(S.RecUpd.update, valueExpr)
        )
      )
    );

  const subAmounts = exprApp(exprBuiltin(BF.SUB_NUMERIC), [
    exprProj(exprVar(SI.this), SI.amount),
    exprProj(exprVar(SI.a2), SI.amount),
  ]);
  const binding = (nameSi, bound) =>
    msg(bf(S.Binding.binder, msg(vf(S.VarWithType.varInternedStr, nameSi))), bf(S.Binding.bound, bound));
  const pureUnit = msg(
    bf(
      S.Expr.update,
      bf(S.Update.pure, msg(bf(S.message('Pure').expr, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_UNIT)))))
    )
  );
  const doBlock = msg(
    bf(
      S.Expr.update,
      bf(
        S.Update.block,
        msg(
          bf(S.Block.bindings, binding(SI.c1, createTok(updAmount(exprProj(exprVar(SI.a2), SI.amount))))),
          bf(S.Block.bindings, binding(SI.c2, createTok(updAmount(subAmounts)))),
          bf(S.Block.body, pureUnit)
        )
      )
    )
  );
  // method value: \s2 -> \a2 -> do { ... }
  const methodValue = exprAbs(SI.s2, exprAbs(SI.a2, doBlock));

  // top-level value: splitImpl = \i -> call_interface splitImpl i
  const callIface = msg(
    bf(
      S.Expr.callInterface,
      msg(vf(S.CallInterface.methodInternedName, dnameIndex('splitImpl')), bf(S.CallInterface.interfaceExpr, exprVar(SI.i)))
    )
  );
  const splitImplValue = msg(
    bf(S.DefValue.nameWithType, msg(vf(S.NameWithType.nameInternedDname, DN.splitImpl))),
    bf(S.DefValue.expr, exprAbs(SI.i, callIface))
  );

  const valRef = msg(
    bf(S.Expr.val, msg(bf(S.ValueId.module, selfModule), vf(S.ValueId.nameInternedDname, DN.splitImpl)))
  );
  // The choice reuses the 'splitImpl' string as its name; what matters is the
  // dispatch through the value + call_interface, not the label.
  const splitChoiceMsg = msg(
    vf(S.TemplateChoice.nameInternedStr, stringTable.indexOf('splitImpl')),
    vf(S.TemplateChoice.consuming, 1),
    vf(S.TemplateChoice.selfBinderInternedStr, SI.self),
    bf(S.TemplateChoice.argBinder, msg(vf(S.VarWithType.varInternedStr, SI.arg))),
    bf(
      S.TemplateChoice.update,
      exprApp(valRef, [exprVar(SI.this), exprVar(SI.self), exprVar(SI.arg)])
    )
  );

  const iface = msg(
    vf(S.DefInterface.tyconInternedDname, DN.Utxo),
    vf(S.DefInterface.paramInternedStr, SI.this),
    bf(S.DefInterface.choices, splitChoiceMsg)
  );

  const implMsg = msg(
    bf(S.Implements.interface, tyconUtxo),
    bf(
      S.Implements.body,
      msg(
        bf(
          S.InterfaceInstanceBody.methods,
          msg(
            vf(S.InterfaceInstanceMethod.methodInternedName, dnameIndex('splitImpl')),
            bf(S.InterfaceInstanceMethod.value, methodValue)
          )
        )
      )
    )
  );
  const location = msg(
    bf(S.Location.range, msg(vf(S.Range.startLine, 9), vf(S.Range.endLine, 19)))
  );
  const template = msg(
    vf(S.DefTemplate.tyconInternedDname, DN.Tok),
    vf(S.DefTemplate.paramInternedStr, SI.this),
    bf(S.DefTemplate.implements, implMsg),
    bf(S.DefTemplate.location, location)
  );

  const module = msg(
    vf(S.Module.nameInternedDname, DN.Mod),
    bf(S.Module.values, splitImplValue),
    bf(S.Module.templates, template),
    bf(S.Module.interfaces, iface)
  );

  const pkg = msg(
    bf(S.Package.modules, module),
    ...stringTable.map((s) => sf(S.Package.internedStrings, s)),
    ...dnameMsgs,
    bf(
      S.Package.metadata,
      msg(vf(S.PackageMetadata.nameInternedStr, SI.pkg), vf(S.PackageMetadata.versionInternedStr, SI['1.0.0']))
    )
  );
  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'cafebabe'));
}

test('interface instance methods become transitions with the split shape', () => {
  const raw = decodeDalfRaw(buildInterfaceFixtureDalf());
  const transitions = extractTransitions(raw);
  const split = transitions.find((t) => t.via === 'Utxo');
  assert.ok(split, 'expected a (via Utxo) transition');
  assert.equal(split.template, 'Tok');
  assert.equal(split.choice, 'splitImpl'); // the fixture reuses the string as the choice name
  assert.equal(split.consuming, true);
  assert.equal(split.creates.length, 2, 'both creates of the split must be recovered');

  const inst = amountConservation(split);
  assert.equal(inst.applicable, true);
  assert.equal(
    termToSmt(inst.goal),
    '(= (+ |arg.amount| (- |this.amount| |arg.amount|)) |this.amount|)'
  );

  // location threading: LF 0-based lines reported 1-based
  assert.deepEqual(
    { startLine: split.location.startLine, endLine: split.location.endLine },
    { startLine: 10, endLine: 20 }
  );
});

test('cvc5 proves conservation for the interface-instance split transition', { skip: !SOLVER }, () => {
  const raw = decodeDalfRaw(buildInterfaceFixtureDalf());
  const split = extractTransitions(raw).find((t) => t.via === 'Utxo');
  const inst = amountConservation(split);
  const out = runSolver(buildQuery(inst.guards, inst.goal).script);
  assert.match(out, /^unsat/m);
});

test('cvc5 handles String-sorted guards', { skip: !SOLVER }, () => {
  // this.id = "alpha" implies this.id /= "beta"
  const { script } = buildQuery(
    [eq(v('this.id'), T.str('alpha'))],
    T.app('not', [eq(v('this.id'), T.str('beta'))])
  );
  const out = runSolver(script);
  assert.match(out, /^unsat/m);
});

// ---------------------------------------------------------------------------
// Exact conversions and partial coverage
// ---------------------------------------------------------------------------

test('INT64_TO_NUMERIC is an exact conversion, not a rounding builtin', async () => {
  // Misfiling it as rounding made amountConservation refuse every transition
  // whose arithmetic touched a scaled constant, and made every scaled division
  // denominator untranslatable. The conversion itself loses nothing; its only
  // partiality is overflow, which aborts rather than rounds.
  const { ROUNDING, EXACT_CONVERSION, BF } = await import('../backend/lfir.js');
  assert.equal(ROUNDING.has(BF.INT64_TO_NUMERIC), false, 'exact, must not be in ROUNDING');
  assert.equal(EXACT_CONVERSION.has(BF.INT64_TO_NUMERIC), true);
  // the truncating direction stays flagged
  assert.equal(ROUNDING.has(BF.NUMERIC_TO_INT64), true, 'truncation is real value loss');
  assert.equal(ROUNDING.has(BF.ROUND_NUMERIC), true);
});

test('division-safety adjudicates per denominator instead of refusing wholesale', () => {
  // One untranslatable denominator must not hide the ones that do translate:
  // on a real perb calculation this was 19 provable obligations hidden by 1.
  const t = transition({
    divisions: [
      { denominator: v('arg.fx') },
      { denominator: T.unsupported('helper call', 'x') },
      { denominator: T.num('1000') },
    ],
  });
  const inst = divisionSafety(t);
  assert.equal(inst.applicable, true, 'must still produce a goal');
  assert.equal(inst.coverage.checked, 2);
  assert.equal(inst.coverage.total, 3);
  assert.deepEqual(inst.coverage.skipped, ['helper call']);
  // the goal covers exactly the checkable denominators
  const smt = termToSmt(inst.goal);
  assert.match(smt, /arg\.fx/);
  assert.match(smt, /1000/);
});

test('division-safety still refuses when NO denominator is translatable', () => {
  const t = transition({
    divisions: [{ denominator: T.unsupported('opaque', 'x') }],
  });
  const inst = divisionSafety(t);
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /all 1 denominator\(s\) are outside the fragment/);
});

test('a zero-capable denominator is refuted, a constant one is proved', { skip: !SOLVER }, () => {
  // the shape of the real perb finding: dividing by a scaled balance field
  const unsafe = divisionSafety(
    transition({ divisions: [{ denominator: T.app('/', [v('this.balance'), T.num('1000000000')]) }] })
  );
  assert.match(runSolver(buildQuery(unsafe.guards, unsafe.goal).script), /^sat/m);

  // guarded by a precondition, the same denominator is safe
  const guarded = divisionSafety(
    transition({
      guards: [T.app('>', [v('this.balance'), T.num('0')])],
      divisions: [{ denominator: T.app('/', [v('this.balance'), T.num('1000000000')]) }],
    })
  );
  assert.match(runSolver(buildQuery(guarded.guards, guarded.goal).script), /^unsat/m);
});

test('unapplied lambda parameters become fresh symbolic elements', async () => {
  // A lambda handed to foldl/map is never applied, so its parameters used to
  // translate as `unbound variable`, making everything inside unreachable.
  // Each parameter now stands for an arbitrary element of the list.
  const { T: Tm, makeCtx } = await import('../backend/lfir.js');
  assert.ok(Tm.record('elem$0').root === 'elem$0');
  // the context tracks them so a verdict can disclose the quantification
  const ctx = makeCtx({ str: () => 'x', dname: () => 'y', internedExprs: [], resolveValue: () => null }, {
    selfParam: 'this', argParam: 'arg', label: 'T.C',
  });
  assert.deepEqual(ctx.symbolicElements, []);
  assert.equal(ctx.elementCount, 0);
});

test('an arbitrary element with an unconstrained divisor is refuted', { skip: !SOLVER }, () => {
  // the ApplyConcentration shape: dividing by a field of a fold element
  const inst = divisionSafety(
    transition({ divisions: [{ denominator: v('elem$0.fx') }] })
  );
  assert.match(runSolver(buildQuery(inst.guards, inst.goal).script), /^sat/m);

  // constrain that element and the same division is safe: this is why the
  // verdict must disclose that the element is arbitrary
  const guarded = divisionSafety(
    transition({
      guards: [T.app('>', [v('elem$0.fx'), T.num('0')])],
      divisions: [{ denominator: v('elem$0.fx') }],
    })
  );
  assert.match(runSolver(buildQuery(guarded.guards, guarded.goal).script), /^unsat/m);
});

test('conservation refuses a choice that consumes contracts besides `this`', () => {
  // A merge consumes its inputs, so `sum(created) = this.amount` is simply the
  // wrong statement: the true one adds the consumed amounts. Answering the
  // misstated question would produce a spurious DISPROVED.
  const t = transition({
    consumesOthers: [{ effect: 'exercise (interface)' }],
    creates: [{ template: 'Tok', base: null, fields: { amount: v('this.amount') }, path: [] }],
  });
  const inst = amountConservation(t);
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /consumes contracts besides/);
  assert.match(inst.why, /wrong statement/);
});

test('the wrong-property refusal dominates a mere translation gap', () => {
  // Both problems present: the refusal must name the property error, which is
  // fundamental, not the FOLDL gap, which is incidental.
  const t = transition({
    consumesOthers: [{ effect: 'exercise' }],
    creates: [
      { template: 'Tok', base: null, fields: { amount: T.unsupported('builtin FOLDL', 'x') }, path: [] },
    ],
  });
  assert.match(amountConservation(t).why, /consumes contracts besides/);
});

test('a self-contained split is unaffected by the consuming-others rule', () => {
  const t = transition({
    consumesOthers: [],
    creates: [
      { template: 'Tok', base: null, fields: { amount: v('arg.amount') }, path: [] },
      { template: 'Tok', base: null, fields: { amount: T.app('-', [v('this.amount'), v('arg.amount')]) }, path: [] },
    ],
  });
  assert.equal(amountConservation(t).applicable, true);
});

// ===========================================================================
// Bounded folds, archived inputs, and the symbol identity they turn on
// ===========================================================================
//
// The design point these tests exist to protect: merge conservation is
// `sum(created) = this.amount + sum(archived)`, and it is only a TRUE
// statement if the elements the fold sums and the elements the choice
// archives are THE SAME SYMBOLS. Key them independently - A0..Ak for the fold,
// B0..Bk for the archive loop - and the goal becomes `this + sum(A) =
// this + sum(B)`, which is satisfiable, and a correct merge is reported
// DISPROVED. Every test below is either about producing that identity or
// about refusing when it cannot be produced.

const fold = (listName, op, unrolled) => T.fold(listName, op, unrolled);

test('instantiateFolds picks the unrolling for the list length asked for', () => {
  const f = fold('arg.holdings', 'foldl', [
    T.num('0'),
    v('arg.holdings$0.amount'),
    plus(v('arg.holdings$0.amount'), v('arg.holdings$1.amount')),
  ]);
  const term = plus(v('this.amount'), f);
  assert.equal(termToSmt(instantiateFolds(term, 0)), '(+ |this.amount| 0)');
  assert.equal(termToSmt(instantiateFolds(term, 1)), '(+ |this.amount| |arg.holdings$0.amount|)');
  assert.equal(
    termToSmt(instantiateFolds(term, 2)),
    '(+ |this.amount| (+ |arg.holdings$0.amount| |arg.holdings$1.amount|))'
  );
  // beyond the unrolling: an explicit refusal, never a silently shorter list
  const over = instantiateFolds(term, 3);
  assert.equal(hasUnsupported(over), true);
  assert.match(unsupportedReasons(over)[0].why, /does not cover list length 3/);
});

test('an uninstantiated fold counts as unsupported everywhere it could be asserted', () => {
  // This is what keeps every property that does not opt into bounded
  // reasoning behaving exactly as it did when a fold was `builtin FOLDL is
  // outside the fragment`: dropped or skipped, with a reason, never asserted.
  const f = fold('arg.xs', 'foldl', [T.num('0'), v('arg.xs$0.amount')]);
  assert.equal(hasUnsupported(f), true);
  assert.match(unsupportedReasons(f)[0].why, /foldl over `arg\.xs`/);
  assert.throws(() => termToSmt(f), /uninstantiated foldl over `arg\.xs`/);

  // a guard carrying one is dropped, and the drop is reported
  const { used, dropped } = usableGuards(transition({ guards: [T.app('>', [f, T.num('0')])] }));
  assert.deepEqual(used, []);
  assert.match(dropped[0][0], /foldl over `arg\.xs`/);

  // a denominator carrying one is skipped, not silently proved
  const inst = divisionSafety(transition({ divisions: [{ denominator: f }] }));
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
});

test('foldLists names the lists a term folds over', () => {
  const f1 = fold('arg.a', 'foldl', [T.num('0')]);
  const f2 = fold('arg.b', 'foldr', [T.num('0')]);
  assert.deepEqual([...foldLists(plus(f1, f2))], ['arg.a', 'arg.b']);
  assert.deepEqual([...foldLists(v('x'))], []);
});

// ------------------------------------------- the merge statement, synthetic

/** `create this with amount = this.amount + foldl (+) 0 <list>`, archiving <list>. */
function mergeTransition(overrides = {}) {
  const listName = overrides.listName || 'arg.holdings';
  const bound = overrides.bound ?? 3;
  const unrolled = [T.num('0')];
  for (let i = 0; i < bound; i++) {
    unrolled.push(plus(unrolled[i], v(`${listName}$${i}.amount`)));
  }
  return transition({
    bound,
    creates: [
      {
        template: 'Tok',
        base: 'this',
        fields: { amount: plus(v('this.amount'), fold(listName, 'foldl', unrolled)) },
        path: [],
      },
    ],
    archivedInputs: [{ listName: overrides.archivedList || listName, effect: 'exercise (interface)' }],
    unmodelledLoopEffects: [],
    ...overrides,
  });
}

test('conservation states the merge form: created = this.amount + the archived amounts', () => {
  const inst = amountConservation(mergeTransition());
  assert.equal(inst.applicable, true);
  assert.equal(inst.bounded, true);
  assert.equal(inst.bound, 3);
  assert.equal(inst.listName, 'arg.holdings');
  assert.equal(inst.instances.length, 4, 'one query per list length 0..3');
  assert.deepEqual(inst.instances.map((i) => i.k), [0, 1, 2, 3]);

  // k = 0: no elements on either side
  assert.equal(termToSmt(inst.instances[0].goal), '(= (+ |this.amount| 0) |this.amount|)');
  // k = 2: the fold's two elements on the left, the archived two on the right
  assert.equal(
    termToSmt(inst.instances[2].goal),
    '(= (+ |this.amount| (+ (+ 0 |arg.holdings$0.amount|) |arg.holdings$1.amount|)) ' +
      '(+ |this.amount| |arg.holdings$0.amount| |arg.holdings$1.amount|))'
  );
});

/** Every `|...|` symbol in a rendered query, as a Set. */
const symbolsOf = (smt) => new Set([...smt.matchAll(/\|([^|]+)\|/g)].map((m) => m[1]));

test('the fold elements and the archived elements are THE SAME symbols', () => {
  // THE test this whole design exists for. Not "the two sides are equal by
  // some algebra" - they are the same free variables, so no model can make
  // them differ, at any list length.
  const inst = amountConservation(mergeTransition());
  for (const i of inst.instances) {
    const [lhs, rhs] = i.goal.args;
    const left = [...symbolsOf(termToSmt(lhs))].filter((n) => n.includes('$'));
    const right = [...symbolsOf(termToSmt(rhs))].filter((n) => n.includes('$'));
    assert.deepEqual(
      left.sort(),
      right.sort(),
      `at list length ${i.k} the two sides must name the same elements`
    );
    assert.equal(left.length, i.k, `list length ${i.k} must mention exactly ${i.k} element(s)`);
    for (const n of left) assert.match(n, /^arg\.holdings\$\d+\.amount$/);
  }
});

test('cvc5 proves the merge at every bounded list length', { skip: !SOLVER }, () => {
  const inst = amountConservation(mergeTransition());
  for (const i of inst.instances) {
    const out = runSolver(buildQuery(i.guards, i.goal).script);
    assert.match(out, /^unsat/m, `list length ${i.k} should be unsat`);
  }
});

test('a mismatched-symbol model of the SAME merge is refuted by cvc5', { skip: !SOLVER }, () => {
  // The bug the list-keyed naming prevents, written out. If the archived
  // inputs were modelled as a second family of symbols (B0, B1) instead of
  // the ones the fold produced (arg.holdings$i.amount), the goal is
  // satisfiable and a correct merge comes back DISPROVED.
  const shared = eq(
    plus(v('this.amount'), plus(v('arg.holdings$0.amount'), v('arg.holdings$1.amount'))),
    plus(v('this.amount'), plus(v('arg.holdings$0.amount'), v('arg.holdings$1.amount')))
  );
  assert.match(runSolver(buildQuery([], shared).script), /^unsat/m);

  const mismatched = eq(
    plus(v('this.amount'), plus(v('arg.holdings$0.amount'), v('arg.holdings$1.amount'))),
    plus(v('this.amount'), plus(v('archived$0.amount'), v('archived$1.amount')))
  );
  const out = runSolver(buildQuery([], mismatched).script);
  assert.match(out, /^sat/m, 'unrelated symbols must be satisfiable - i.e. a spurious DISPROVED');
});

test('conservation refuses an archived list the created amounts never fold over', () => {
  // Adding `sum(L$i.amount)` for a list nothing else mentions would invent a
  // family of unconstrained symbols (spurious DISPROVED); leaving it out would
  // assume the archived contracts carry no amount (spurious PROVED).
  const inst = amountConservation(
    transition({
      bound: 3,
      creates: [{ template: 'Tok', base: 'this', fields: { amount: v('this.amount') }, path: [] }],
      archivedInputs: [{ listName: 'arg.holdings', effect: 'exercise' }],
    })
  );
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /archives every element of `arg\.holdings`/);
  assert.match(inst.why, /no created amount is built from a fold over that list/);
});

test('conservation refuses a mismatch between the folded list and the archived list', () => {
  // The compiled-shape version of the same trap: the sum ranges over one list
  // and the archive loop over another.
  const inst = amountConservation(mergeTransition({ archivedList: 'arg.others' }));
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /arg\.others/);
});

test('conservation refuses a transition mixing two distinct lists', () => {
  const inst = amountConservation(
    transition({
      bound: 3,
      creates: [
        {
          template: 'Tok',
          base: 'this',
          fields: {
            amount: plus(
              fold('arg.a', 'foldl', [T.num('0'), v('arg.a$0.amount')]),
              fold('arg.b', 'foldl', [T.num('0'), v('arg.b$0.amount')])
            ),
          },
          path: [],
        },
      ],
      archivedInputs: [],
    })
  );
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /2 distinct lists/);
  assert.match(inst.why, /combinations of differing lengths/);
});

test('conservation refuses creates inside a per-element loop', () => {
  const inst = amountConservation(
    mergeTransition({
      unmodelledLoopEffects: [{ why: '1 create(s) inside a traversal over `arg.holdings`' }],
    })
  );
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /create\(s\) inside a traversal/);
});

test('a transition with no lists keeps the exact, unbounded statement', () => {
  // Today's verdicts must not become bounded just because the machinery exists.
  const inst = amountConservation(
    transition({
      creates: [
        { template: 'Tok', base: null, fields: { amount: v('arg.amount') }, path: [] },
        {
          template: 'Tok',
          base: null,
          fields: { amount: T.app('-', [v('this.amount'), v('arg.amount')]) },
          path: [],
        },
      ],
    })
  );
  assert.equal(inst.applicable, true);
  assert.equal(inst.bounded, undefined, 'no list is involved, so nothing is bounded');
  assert.equal(inst.instances, undefined);
  assert.equal(
    termToSmt(inst.goal),
    '(= (+ |arg.amount| (- |this.amount| |arg.amount|)) |this.amount|)'
  );
});

test('an unidentified consuming effect still refuses, and says why', () => {
  const inst = amountConservation(
    transition({
      consumesOthers: [{ effect: 'exerciseByKey' }],
      creates: [{ template: 'Tok', base: 'this', fields: {}, path: [] }],
    })
  );
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /consumes contracts besides `this`/);
  assert.match(inst.why, /could not identify/);
});

test('division-safety is bounded when a denominator comes from an unrolled fold step', () => {
  const inst = divisionSafety(
    transition({
      bound: 3,
      divisions: [
        { denominator: v('this.rate') },
        { denominator: v('arg.xs$0.qty'), fold: 'arg.xs', index: 0 },
      ],
    })
  );
  assert.equal(inst.applicable, true);
  assert.equal(inst.bounded, true);
  assert.equal(inst.bound, 3);
  assert.match(inst.boundedNote, /1 of 2 checked denominator\(s\) come from fold steps/);
  assert.match(inst.boundedNote, /nothing is claimed about longer lists/);

  // and a transition with no fold-derived denominator stays unbounded
  const plain = divisionSafety(transition({ divisions: [{ denominator: v('this.rate') }] }));
  assert.equal(plain.bounded, undefined);
});

// --------------------------------------------- the same shapes, COMPILED

/**
 * A one-package DAR fixture with the compiled MERGE shape, so the translator
 * itself is exercised rather than hand-written IR:
 *
 *   template Tok, consuming choice Merge with arg:
 *     [viaMapA] tokens <- DA.Internal.Prelude:mapA fetch arg.holdings
 *     _        <- DA.Foldable:mapA_ (\cid -> exercise @Holding Archive cid) arg.holdings
 *     create this with amount = this.amount + FOLDL (\acc t -> acc + t.amount) 0 <list>
 *
 * `<list>` is `arg.holdings` directly, or `tokens` when viaMapA - which is the
 * shape a real merge compiles to, and the one that breaks if element symbols
 * are keyed to anything but the source list.
 *
 * `archiveList` lets the archive loop range over a DIFFERENT field, which is
 * the compiled form of the mismatch this design refuses.
 */
function buildMergeFixtureDalf({
  viaMapA = false,
  foldr = false,
  archiveList = 'holdings',
  doubleCount = false,
} = {}) {
  const strings = [
    'this', 'self', 'arg', 'amount', 'holdings', 'others', 'acc', 't', 'cid', 'h',
    'tokens', 'ignored', 'Archive', 'Merge', 'pkg', '1.0.0',
    'Mod', 'Tok', 'Holding', 'DA', 'Foldable', 'mapA_', 'Internal', 'Prelude', 'mapA',
  ];
  const SI = Object.fromEntries(strings.map((s, i) => [s, i]));

  // interned dotted names, each a packed list of string indices
  const dotted = [
    ['Mod'], ['Tok'], ['Holding'], ['DA', 'Foldable'], ['mapA_'],
    ['DA', 'Internal', 'Prelude'], ['mapA'],
  ];
  const DN = { Mod: 0, Tok: 1, Holding: 2, DAFoldable: 3, mapA_: 4, DAPrelude: 5, mapA: 6 };
  const dnameMsgs = dotted.map((segs) =>
    bf(
      S.Package.internedDottedNames,
      bf(S.InternedDottedName.segmentsInternedStr, Buffer.concat(segs.map((x) => varint(SI[x]))))
    )
  );

  const moduleRef = (dn) =>
    msg(
      bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
      vf(S.ModuleId.moduleNameInternedDname, dn)
    );
  const tycon = (modDn, nameDn) =>
    msg(bf(S.TypeConId.module, moduleRef(modDn)), vf(S.TypeConId.nameInternedDname, nameDn));
  const valRef = (modDn, nameDn) =>
    msg(bf(S.Expr.val, msg(bf(S.ValueId.module, moduleRef(modDn)), vf(S.ValueId.nameInternedDname, nameDn))));
  const defValue = (nameDn, body) =>
    msg(
      bf(S.DefValue.nameWithType, msg(vf(S.NameWithType.nameInternedDname, nameDn))),
      bf(S.DefValue.expr, body)
    );

  const pureUnit = msg(
    bf(
      S.Expr.update,
      bf(S.Update.pure, msg(bf(S.message('Pure').expr, msg(vf(S.Expr.builtinCon, S.ENUMS.BuiltinCon.CON_UNIT)))))
    )
  );

  // the two stdlib traversals, recognised by their fully qualified names
  const traversalBody = exprAbs(SI.h, exprAbs(SI.cid, pureUnit));
  const foldableModule = msg(
    vf(S.Module.nameInternedDname, DN.DAFoldable),
    bf(S.Module.values, defValue(DN.mapA_, traversalBody))
  );
  const preludeModule = msg(
    vf(S.Module.nameInternedDname, DN.DAPrelude),
    bf(S.Module.values, defValue(DN.mapA, traversalBody))
  );

  const EI = S.message('Update.ExerciseInterface');
  const archiveFn = exprAbs(
    SI.cid,
    msg(
      bf(
        S.Expr.update,
        bf(
          S.Update.exerciseInterface,
          msg(
            bf(EI.interface, tycon(DN.Mod, DN.Holding)),
            vf(EI.choiceInternedStr, SI.Archive),
            bf(EI.cid, exprVar(SI.cid))
          )
        )
      )
    )
  );
  const fetchFn = exprAbs(SI.h, pureUnit);

  const holdingsExpr = exprProj(exprVar(SI.arg), SI.holdings);
  const archiveListExpr = exprProj(exprVar(SI.arg), SI[archiveList]);
  // `doubleCount` adds each input's amount TWICE: a merge that really does
  // violate conservation, and only from the first element onwards.
  const contribution = doubleCount
    ? exprApp(exprBuiltin(BF.ADD_NUMERIC), [exprProj(exprVar(SI.t), SI.amount), exprProj(exprVar(SI.t), SI.amount)])
    : exprProj(exprVar(SI.t), SI.amount);
  const step = foldr
    ? exprAbs(SI.t, exprAbs(SI.acc, exprApp(exprBuiltin(BF.ADD_NUMERIC), [contribution, exprVar(SI.acc)])))
    : exprAbs(SI.acc, exprAbs(SI.t, exprApp(exprBuiltin(BF.ADD_NUMERIC), [exprVar(SI.acc), contribution])));
  const foldedList = viaMapA ? exprVar(SI.tokens) : holdingsExpr;
  const foldExpr = exprApp(exprBuiltin(foldr ? BF.FOLDR : BF.FOLDL), [step, exprInt(0), foldedList]);

  const CREATE = S.message('Update.Create');
  const createTok = msg(
    bf(
      S.Expr.update,
      bf(
        S.Update.create,
        msg(
          bf(CREATE.template, tycon(DN.Mod, DN.Tok)),
          bf(
            CREATE.expr,
            msg(
              bf(
                S.Expr.recUpd,
                msg(
                  vf(S.RecUpd.fieldInternedStr, SI.amount),
                  bf(S.RecUpd.record, exprVar(SI.this)),
                  bf(
                    S.RecUpd.update,
                    exprApp(exprBuiltin(BF.ADD_NUMERIC), [exprProj(exprVar(SI.this), SI.amount), foldExpr])
                  )
                )
              )
            )
          )
        )
      )
    )
  );

  const binding = (nameSi, bound) =>
    msg(bf(S.Binding.binder, msg(vf(S.VarWithType.varInternedStr, nameSi))), bf(S.Binding.bound, bound));
  const bindings = [];
  if (viaMapA) {
    bindings.push(
      bf(S.Block.bindings, binding(SI.tokens, exprApp(exprApp(valRef(DN.DAPrelude, DN.mapA), [fetchFn]), [holdingsExpr])))
    );
  }
  bindings.push(
    bf(S.Block.bindings, binding(SI.ignored, exprApp(exprApp(valRef(DN.DAFoldable, DN.mapA_), [archiveFn]), [archiveListExpr])))
  );
  const body = msg(
    bf(S.Expr.update, bf(S.Update.block, msg(...bindings, bf(S.Block.body, createTok))))
  );

  const choiceMsg = msg(
    vf(S.TemplateChoice.nameInternedStr, SI.Merge),
    vf(S.TemplateChoice.consuming, 1),
    vf(S.TemplateChoice.selfBinderInternedStr, SI.self),
    bf(S.TemplateChoice.argBinder, msg(vf(S.VarWithType.varInternedStr, SI.arg))),
    bf(S.TemplateChoice.update, body)
  );
  const template = msg(
    vf(S.DefTemplate.tyconInternedDname, DN.Tok),
    vf(S.DefTemplate.paramInternedStr, SI.this),
    bf(S.DefTemplate.choices, choiceMsg)
  );
  const module = msg(vf(S.Module.nameInternedDname, DN.Mod), bf(S.Module.templates, template));

  const pkg = msg(
    bf(S.Package.modules, module),
    bf(S.Package.modules, foldableModule),
    bf(S.Package.modules, preludeModule),
    ...strings.map((s) => sf(S.Package.internedStrings, s)),
    ...dnameMsgs,
    bf(
      S.Package.metadata,
      msg(vf(S.PackageMetadata.nameInternedStr, SI.pkg), vf(S.PackageMetadata.versionInternedStr, SI['1.0.0']))
    )
  );
  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'deadbeef'));
}

const mergeFixture = (opts, bound = 3) =>
  extractTransitions(decodeDalfRaw(buildMergeFixtureDalf(opts)), { bound }).find(
    (t) => t.choice === 'Merge'
  );

test('a compiled FOLDL is unrolled, keyed to the list it ranges over', () => {
  const t = mergeFixture({});
  const amount = t.creates[0].fields.amount;
  assert.deepEqual([...foldLists(amount)], ['arg.holdings']);
  assert.equal(
    termToSmt(instantiateFolds(amount, 2)),
    '(+ |this.amount| (+ (+ 0 |arg.holdings$0.amount|) |arg.holdings$1.amount|))'
  );
  assert.deepEqual(
    t.listElements,
    [
      { listName: 'arg.holdings', index: 0 },
      { listName: 'arg.holdings', index: 1 },
      { listName: 'arg.holdings', index: 2 },
    ]
  );
});

test('a compiled FOLDR unrolls from the right, element first', () => {
  // foldr f z [e0,e1] = f e0 (f e1 z): the element order the unroller has to
  // get right, and the one a left-to-right unrolling would silently invert.
  const t = mergeFixture({ foldr: true });
  assert.equal(
    termToSmt(instantiateFolds(t.creates[0].fields.amount, 2)),
    '(+ |this.amount| (+ |arg.holdings$0.amount| (+ |arg.holdings$1.amount| 0)))'
  );
});

test('a compiled archive loop is recorded as archiving the elements of its list', () => {
  const t = mergeFixture({});
  assert.deepEqual(t.archivedInputs, [{ listName: 'arg.holdings', effect: 'exercise (interface)' }]);
  assert.deepEqual(t.consumesOthers, [], 'an identified archive loop is not an unidentified one');
  assert.deepEqual(t.unmodelledLoopEffects, []);
});

test('a fold over a mapA RESULT is named after the source list, not the binder', () => {
  // The shape that makes or breaks the whole property: the sum ranges over
  // `tokens <- mapA fetch arg.holdings` while the archive loop ranges over
  // `arg.holdings`. Naming the fold's elements `tokens$i` would leave the two
  // sides talking about different symbols, and the merge would come back
  // DISPROVED for no reason at all.
  const t = mergeFixture({ viaMapA: true });
  assert.deepEqual([...foldLists(t.creates[0].fields.amount)], ['arg.holdings']);
  assert.deepEqual(t.archivedInputs, [{ listName: 'arg.holdings', effect: 'exercise (interface)' }]);

  const inst = amountConservation(t);
  assert.equal(inst.applicable, true);
  assert.equal(inst.bounded, true);
  for (const i of inst.instances) {
    const [lhs, rhs] = i.goal.args;
    const left = [...symbolsOf(termToSmt(lhs))].filter((n) => n.includes('$')).sort();
    const right = [...symbolsOf(termToSmt(rhs))].filter((n) => n.includes('$')).sort();
    assert.deepEqual(left, right, `list length ${i.k}: same elements on both sides`);
  }
});

test('cvc5 proves the COMPILED merge at every bounded list length', { skip: !SOLVER }, () => {
  const inst = amountConservation(mergeFixture({ viaMapA: true }));
  assert.equal(inst.instances.length, 4);
  for (const i of inst.instances) {
    assert.match(runSolver(buildQuery(i.guards, i.goal).script), /^unsat/m, `k=${i.k}`);
  }
});

test('a compiled archive loop over a DIFFERENT list is refused, not proved', () => {
  // Same merge, but the loop archives `arg.others` while the sum ranges over
  // `arg.holdings`. There is no honest statement relating them, so refuse.
  const t = mergeFixture({ archiveList: 'others' });
  assert.deepEqual(t.archivedInputs, [{ listName: 'arg.others', effect: 'exercise (interface)' }]);
  const inst = amountConservation(t);
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /arg\.others/);
});

test('--bound decides how far the compiled fold is unrolled', () => {
  for (const bound of [0, 1, 5]) {
    const t = mergeFixture({}, bound);
    assert.equal(t.bound, bound);
    const inst = amountConservation(t);
    assert.equal(inst.instances.length, bound + 1, `bound ${bound} gives ${bound + 1} queries`);
    assert.equal(inst.bound, bound);
  }
  assert.equal(DEFAULT_BOUND, 3);
});

// ===========================================================================
// UNINTERPRETED FUNCTIONS
//
// The asymmetry is the whole point and it is tested from both sides: an unsat
// over a query with a UF is a proof, a sat over one is a candidate that must
// say so. See the header of backend/smt.js.
// ===========================================================================

test('a uf term renders as an application and is declared with its signature', () => {
  const g = T.uf('isBlank', [v('this.id')], 'Bool');
  assert.equal(termToSmt(g), '(|isBlank| |this.id|)');
  // nullary symbols apply as bare symbols, the way a 0-arity declare-fun does
  assert.equal(termToSmt(T.uf('now', [], 'Real')), '|now|');

  const { script, ufs } = buildQuery([g], T.bool(true));
  assert.match(script, /\(declare-fun \|isBlank\| \(Real\) Bool\)/);
  assert.match(script, /\(assert \(\|isBlank\| \|this\.id\|\)\)/);
  assert.deepEqual(ufs, ['isBlank']);
});

test('uf argument sorts are inferred from the arguments, and pinned when declared', () => {
  // an unconstrained argument defaults to Real, as every other position does
  const loose = inferSorts([{ term: T.uf('f', [v('a')], 'Bool'), sort: 'Bool' }]);
  assert.deepEqual(loose.conflicts, []);
  assert.deepEqual(loose.ufs.get('f'), { args: ['Real'], ret: 'Bool' });

  // a String literal anywhere in the argument's sort class pins the whole
  // class - the order dependence the old single-pass inference had is gone
  const pinned = inferSorts([
    { term: T.uf('f', [v('a')], 'Bool'), sort: 'Bool' },
    { term: eq(v('a'), T.str('x')), sort: 'Bool' },
  ]);
  assert.deepEqual(pinned.conflicts, []);
  assert.deepEqual(pinned.ufs.get('f'), { args: ['String'], ret: 'Bool' });
  assert.equal(pinned.sorts.get('a'), 'String');

  // declared argument sorts (a builtin whose LF type is fixed) propagate OUT
  // to the variable, rather than being overridden by it
  const declared = inferSorts([
    { term: eq(T.uf('cat', [v('p'), v('q')], 'String', ['String', 'String']), T.str('ab')), sort: 'Bool' },
  ]);
  assert.deepEqual(declared.conflicts, []);
  assert.equal(declared.sorts.get('p'), 'String');
  assert.equal(declared.sorts.get('q'), 'String');
});

test('a uf used at two different signatures is a conflict, not a reconciliation', () => {
  // same name, two arities
  const arity = inferSorts([
    { term: T.uf('f', [v('a')], 'Bool'), sort: 'Bool' },
    { term: T.uf('f', [v('a'), v('b')], 'Bool'), sort: 'Bool' },
  ]);
  assert.ok(arity.conflicts.some((c) => /applied to 1 and 2 arguments/.test(c)));

  // same name, two result sorts
  const ret = inferSorts([
    { term: T.uf('g', [v('a')], 'Bool'), sort: 'Bool' },
    { term: eq(T.uf('g', [v('a')], 'Real'), T.num('1')), sort: 'Bool' },
  ]);
  assert.ok(ret.conflicts.length > 0);

  // and a conflict refuses the query rather than emitting an ill-sorted script
  assert.throws(
    () => buildQuery([T.uf('f', [v('a')], 'Bool')], T.uf('f', [v('a'), v('b')], 'Bool')),
    /sort conflicts/
  );
});

test('cvc5: an unsat over a uf query is a proof; a sat over one is only a candidate', { skip: !SOLVER }, () => {
  const blank = (x) => T.uf('isBlank', [x], 'Bool');
  // f(x) => f(x) holds for EVERY interpretation of f: unsat, a real proof
  assert.match(
    runSolver(buildQuery([blank(v('this.id'))], blank(v('this.id'))).script),
    /^unsat/m
  );
  // f(x) => f(y) holds only for the interpretations where they agree, so the
  // solver finds one where they do not: sat, and the counterexample is about
  // an invented interpretation, not about the code
  assert.match(
    runSolver(buildQuery([blank(v('this.id'))], blank(v('this.other'))).script),
    /^sat/m
  );
});

test(
  'the CLI marks a DISPROVED drawn from a uf query as possibly an artifact',
  { skip: (!SOLVER && 'no cvc5') || (!HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}`) },
  () => {
    const cli = new URL('../backend/verify.js', import.meta.url).pathname;
    // verify.js exits 1 when anything is DISPROVED, which is the case here.
    // spawnSync rather than execFileSync: the report still comes out in full
    // on stdout, which execFileSync truncates on a nonzero exit.
    const run = spawnSync(
      'node',
      [cli, TOKENS_DAR, '--property', 'amount-conservation', '--json'],
      { encoding: 'utf8', maxBuffer: 64 * 1024 * 1024 }
    );
    const out = JSON.parse(run.stdout).results;

    const withUf = out.filter((r) => (r.uninterpreted || []).length > 0);
    assert.ok(withUf.length > 0, 'expected some verdicts to rest on uninterpreted symbols');

    // every verdict that used one discloses it, proved or disproved alike
    for (const r of withUf) {
      assert.match(r.note || '', /uninterpreted symbol\(s\) in the query/, r.transition);
    }
    // and a DISPROVED additionally says the counterexample may be an artifact
    const disproved = withUf.filter((r) => r.status === 'DISPROVED');
    assert.ok(disproved.length > 0, 'expected a DISPROVED resting on an uninterpreted symbol');
    for (const r of disproved) {
      assert.match(r.note, /MAY BE AN ARTIFACT/, r.transition);
    }
    // a PROVED must NOT carry the artifact caveat: unsat is sound under the
    // abstraction, and saying otherwise would be its own kind of overclaim
    for (const r of withUf.filter((r) => r.status.startsWith('PROVED'))) {
      assert.doesNotMatch(r.note, /MAY BE AN ARTIFACT/, r.transition);
    }
  }
);

test(
  'a real `ensure` recovered from the token DAR: text predicate, Optional and all',
  { skip: !HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}` },
  () => {
    // Abl.CollateralAssetNft's validateCollateralAssetNftData reads
    //   isValidLifecycleScopedTokenIdShape contractData.id contractData.backdated &&
    //   validateAssetTokenId (scopedTokenIdPrefix contractData.id) &&
    //   contractData.businessDate /= None &&
    //   isNonBlankText contractData.relationshipId &&
    //   isNonBlankText contractData.investorId &&
    //   <three `all` quantifiers over contractData.additionalMetadata>
    // Every line of it used to be dropped; this pins what each one became.
    const t = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 }).find(
      (x) => x.choice === 'UpdateCollateralAssetNft'
    );
    assert.ok(t, 'expected an UpdateCollateralAssetNft transition');
    const { used, dropped } = usableGuards(t);
    const rendered = used.map((g) => termToSmt(g));

    // `isNonBlankText x` is `isNotEmpty (trim x)`: the opaque part is `trim`,
    // and the comparison the compiler generated for isNotEmpty SURVIVES as
    // real structure rather than being swallowed by one opaque predicate
    assert.ok(
      rendered.some((r) => /\(not \(= \(\|DA\.Text:trim@[0-9a-f]+\| \|this\.contractData\.relationshipId\|\) ""\)\)/.test(r)),
      `expected a recovered isNonBlankText guard, got:\n${rendered.join('\n')}`
    );
    // `businessDate /= None` is the EXISTING Optional encoding, not a UF: it
    // reduces to the presence flag, with no uninterpreted symbol in sight
    assert.ok(
      rendered.some((r) => /this\.contractData\.businessDate\.\$some/.test(r) && !/@/.test(r)),
      `expected businessDate /= None as a $some comparison, got:\n${rendered.join('\n')}`
    );
    // the `all` quantifiers over additionalMetadata are still dropped, and
    // they say why: a fold, not a text chain, and no UF pretends otherwise
    assert.ok(dropped.length > 0, 'the fold-based conjuncts must still be dropped');
    assert.ok(
      dropped.flat().some((w) => /FOLDL|foldl/.test(w)),
      `expected the dropped conjuncts to name the fold, got:\n${JSON.stringify(dropped)}`
    );
    // and the whole query is emittable
    const { script, ufs } = buildQuery(used, T.bool(true));
    assert.match(script, /\(declare-fun \|DA\.Text:trim@[0-9a-f]+\| \(/);
    assert.ok(ufs.length > 0);
  }
);

test(
  'an aborting branch is never abstracted into an uninterpreted value',
  { skip: !HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}` },
  () => {
    // Error paths format their messages with text builtins, so a rule that
    // looked only at "was the obstacle text?" turned `error` itself into a
    // uninterpreted Bool - which would treat an aborting branch as a reachable
    // post-state and silently weaken every `if c then _ else error` guard.
    const ts = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 });
    const names = new Set();
    for (const t of ts) for (const u of t.uninterpreted || []) names.add(u.name);
    for (const n of names) {
      assert.doesNotMatch(n, /GHC\.Err:error|GHC\.Err:undefined|DA\.Exception/, `abstracted ${n}`);
    }
  }
);

test('every uninterpreted symbol carries the reason it exists', { skip: !HAVE_TOKENS_DAR && 'no DAR' }, () => {
  const ts = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 });
  let seen = 0;
  for (const t of ts) {
    for (const u of t.uninterpreted || []) {
      seen++;
      assert.ok(u.why && u.why.length > 20, `no reason recorded for ${u.name}`);
      // a UF is a modelling choice with a stated cause, never a shrug
      assert.match(u.why, /TEXT|text|APPEND_TEXT|EXPLODE_TEXT|IMPLODE_TEXT|CODE_POINTS|counterpart/);
      // the symbol identifies ONE compiled value: package-qualified, or a
      // globally unique builtin
      assert.ok(/^builtin:[A-Z0-9_]+$/.test(u.name) || /@[0-9a-f]{8}$/.test(u.name), u.name);
    }
  }
  assert.ok(seen > 0, 'the token DAR abstracts nothing: this test checked nothing');
});

// ---------------------------------------------- the real thing, end to end

test(
  'a real compiled merge: the fold and the archive loop agree on `arg.holdings`',
  { skip: !HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}` },
  () => {
    // TransferableRecToken.Merge_Utxo, whose compiled body is
    //   tokens <- mapA (fetch+validate) arg.holdings
    //   let total = this.amount + foldl (\acc t -> acc + t.amount) 0.0 tokens
    //   mapA_ archive arg.holdings; create this with amount = total
    const t = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 }).find(
      (x) => x.choice === 'Merge_Utxo'
    );
    assert.ok(t, 'expected a Merge_Utxo transition');
    assert.equal(t.consuming, true);
    assert.deepEqual([...foldLists(t.creates[0].fields.amount)], ['arg.holdings']);
    assert.deepEqual(t.archivedInputs, [
      { listName: 'arg.holdings', effect: 'exercise (interface)' },
    ]);
    assert.deepEqual(t.consumesOthers, []);

    const inst = amountConservation(t);
    assert.equal(inst.applicable, true, inst.why);
    assert.equal(inst.bounded, true);
    assert.equal(inst.listName, 'arg.holdings');
    assert.deepEqual(inst.instances.map((i) => i.k), [0, 1, 2, 3]);
    for (const i of inst.instances) {
      const [lhs, rhs] = i.goal.args;
      const left = [...symbolsOf(termToSmt(lhs))].filter((n) => n.includes('$')).sort();
      const right = [...symbolsOf(termToSmt(rhs))].filter((n) => n.includes('$')).sort();
      assert.deepEqual(left, right, `k=${i.k}: the fold and the archive name the same elements`);
      assert.equal(left.length, i.k);
    }
  }
);

test(
  'cvc5 proves the real merge at every bounded list length',
  { skip: (!SOLVER && 'no cvc5') || (!HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}`) },
  () => {
    const t = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 }).find(
      (x) => x.choice === 'Merge_Utxo'
    );
    const inst = amountConservation(t);
    for (const i of inst.instances) {
      assert.match(runSolver(buildQuery(i.guards, i.goal).script), /^unsat/m, `k=${i.k}`);
    }
  }
);

test(
  'a merge that double counts its inputs fails, and the FIRST failing length is 1',
  { skip: !SOLVER },
  () => {
    // The counterexample side of bounded checking: k = 0 is still fine (an
    // empty list conserves trivially), and the property breaks as soon as
    // there is one element. Reporting "somewhere at or below 3" would be
    // strictly less useful than "already at 1", which is what verify.js
    // prints because it stops at the first sat.
    const inst = amountConservation(mergeFixture({ doubleCount: true }));
    assert.equal(inst.bounded, true);
    const verdicts = inst.instances.map(
      (i) => (/^unsat/m.test(runSolver(buildQuery(i.guards, i.goal).script)) ? 'unsat' : 'sat')
    );
    assert.deepEqual(verdicts, ['unsat', 'sat', 'sat', 'sat']);
  }
);

test(
  'the CLI prints a bounded proof as its own status, carrying the bound',
  { skip: (!SOLVER && 'no cvc5') || (!HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}`) },
  () => {
    const cli = new URL('../backend/verify.js', import.meta.url).pathname;
    const run = (extra) =>
      JSON.parse(
        execFileSync(
          'node',
          [cli, TOKENS_DAR, '--property', 'amount-conservation', '--choice', 'Merge_Utxo', '--json', ...extra],
          { encoding: 'utf8' }
        )
      ).results[0];

    const dflt = run([]);
    assert.equal(dflt.status, 'PROVED-BOUNDED (lists up to length 3)');
    assert.notEqual(dflt.status, 'PROVED', 'a bounded proof must never print as PROVED');
    assert.equal(dflt.bound, 3);
    assert.equal(dflt.queries, 4);
    assert.match(dflt.note, /the archived inputs are the same `arg\.holdings\$<i>\.amount` symbols/);

    // --bound changes the claim, and the status says so in words
    const narrow = run(['--bound', '1']);
    assert.equal(narrow.status, 'PROVED-BOUNDED (lists up to length 1)');
    assert.equal(narrow.queries, 2);
  }
);

// ---------------------------------------------------------------------------
// non-negative-fields and create-authority
//
// Two things are being pinned here, and they pull in opposite directions.
// For non-negativity it is that a field is checked only on EVIDENCE that it is
// numeric, so that a party or a text field is reported unchecked rather than
// asserted about. For authorisation it is that a party is covered only on
// EVIDENCE that it is the same party, so that a false PROVED - the one failure
// that would make this property worse than not having it - cannot be produced
// by two templates sharing a field name.
// ---------------------------------------------------------------------------

/** A transition carrying the party machinery, for create-authority. */
function authTransition(overrides = {}) {
  const { signatories, controllers, templates, ...rest } = overrides;
  return transition({
    template: 'Tok',
    choice: 'C',
    signatories: signatories || { refs: [{ path: 'this.admin', presence: T.bool(true) }], exact: true, why: null },
    controllers: controllers || { refs: [{ path: 'arg.actor', presence: T.bool(true) }], exact: true, why: null },
    templateSignatories: new Map(Object.entries(templates || {})),
    ...rest,
  });
}

/** An exactly-walked signatory clause for a created template. */
const sigOf = (...paths) => ({
  refs: paths.map((p) => (typeof p === 'string' ? { path: p, presence: T.bool(true) } : p)),
  exact: true,
  why: null,
});

// ------------------------------------------------- non-negativity: shape

test('non-negative-fields: applicability needs a create with a resolved field', () => {
  assert.match(nonNegativeFields(transition({ creates: [] })).why, /creates nothing/);
  assert.equal(nonNegativeFields(transition({ creates: [] })).notModellable, undefined);

  const noFields = nonNegativeFields(
    transition({ creates: [{ template: 'T', base: null, fields: {}, path: [] }] })
  );
  assert.equal(noFields.applicable, false);
  assert.match(noFields.why, /no create resolves a field/);
});

test('non-negative-fields: only terms with numeric EVIDENCE become obligations', () => {
  // `amount` is arithmetic, so it is numeric by construction. `owner` is a
  // bare projection nothing in the transition uses as a number: it might be a
  // Party, a ContractId or a date, and `owner >= 0` would be a fabricated
  // obligation rather than a weak one - so it is skipped, and SAID to be.
  const t = transition({
    creates: [
      {
        template: 'T',
        base: null,
        fields: {
          amount: T.app('-', [v('this.amount'), v('arg.qty')]),
          owner: v('arg.newOwner'),
        },
        path: [],
      },
    ],
  });
  const inst = nonNegativeFields(t);
  assert.equal(inst.applicable, true);
  assert.deepEqual(inst.coverage, {
    checked: 1,
    total: 2,
    skipped: [inst.coverage.skipped[0]],
    // No declared types on this hand-built transition, so nothing is excluded
    // and the single skip lands in the "read it, cannot type it" class.
    excluded: 0,
    excludedFields: [],
    excludedNestedRecords: 0,
    skippedNumeric: 0,
    skippedUnreadable: 0,
    skippedUnknown: 1,
  });
  assert.match(inst.coverage.skipped[0], /T\.owner is not known to be numeric/);
  assert.equal(termToSmt(inst.goal), '(>= (- |this.amount| |arg.qty|) 0)');
});

test('non-negative-fields: a variable another position types as Real IS evidence', () => {
  // Nothing here is arithmetic, but the transition's own guard compares
  // `arg.qty` with a number, which is the compiled code using the field as a
  // number - the same fact a type would have carried. `label` gets no such
  // position and stays unchecked.
  const t = transition({
    guards: [T.app('>', [v('arg.qty'), T.num('0')])],
    creates: [
      { template: 'T', base: null, fields: { qty: v('arg.qty'), label: v('arg.label') }, path: [] },
    ],
  });
  const inst = nonNegativeFields(t);
  assert.equal(inst.coverage.checked, 1);
  assert.equal(inst.coverage.total, 2);
  assert.equal(termToSmt(inst.goal), '(>= |arg.qty| 0)');

  // ...and a variable pinned to something else is not quietly taken as Real
  const text = nonNegativeFields(
    transition({
      guards: [T.app('=', [v('arg.label'), T.str('x')])],
      creates: [{ template: 'T', base: null, fields: { label: v('arg.label') }, path: [] }],
    })
  );
  assert.equal(text.applicable, false);
  assert.match(text.why, /none of the 1 resolved created field\(s\) is known to be numeric/);
});

test('non-negative-fields: an unreadable field is SKIPPED, never assumed non-negative', () => {
  const t = transition({
    creates: [
      {
        template: 'T',
        base: null,
        fields: {
          good: T.app('+', [v('a'), T.num('1')]),
          bad: T.app('*', [v('b'), T.unsupported('a fetch in the field expression', 'T')]),
        },
        path: [],
      },
    ],
  });
  const inst = nonNegativeFields(t);
  assert.equal(inst.coverage.checked, 1);
  assert.equal(inst.coverage.total, 2);
  assert.match(inst.coverage.skipped.join(' '), /T\.bad is outside the fragment.*fetch/);
  // the skipped field appears nowhere in the goal
  assert.doesNotMatch(termToSmt(inst.goal), /\|b\|/);
});

test('non-negative-fields: every field unreadable is a REFUSAL, not a pass', () => {
  const inst = nonNegativeFields(
    transition({
      creates: [
        { template: 'T', base: null, fields: { x: T.unsupported('outside', 'T') }, path: [] },
      ],
    })
  );
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /all 1 resolved created field\(s\) are unchecked/);
});

test('non-negative-fields: the rounding refusal is exactly DIV_INT64 and MOD_INT64', () => {
  const create = {
    template: 'T',
    base: null,
    fields: { amount: T.app('-', [v('this.amount'), T.num('1')]) },
    path: [],
  };
  // Numeric-scale rounding does NOT refuse: none of those builtins produces a
  // term at all (translateBuiltinApp refuses them), so a field built through
  // one carries an `unsupported` node and is skipped by the coverage split.
  for (const r of ['ROUND_NUMERIC', 'CAST_NUMERIC', 'SHIFT_NUMERIC', 'NUMERIC_TO_INT64']) {
    const inst = nonNegativeFields(transition({ creates: [create], rounding: [r] }));
    assert.equal(inst.applicable, true, `${r} must not refuse`);
    assert.ok(inst.notes.some((n) => n.includes(r)), `${r} must still be disclosed`);
  }
  // The Int64 pair DOES refuse: SMT-LIB's div/mod are Euclidean, Daml's
  // truncate toward zero, and they disagree in sign on negative operands.
  for (const r of ['DIV_INT64', 'MOD_INT64']) {
    const inst = nonNegativeFields(transition({ creates: [create], rounding: [r] }));
    assert.equal(inst.applicable, false, `${r} must refuse`);
    assert.equal(inst.notModellable, true);
    assert.match(inst.why, /Euclidean/);
  }
});

test('non-negative-fields: branch conditions are an IMPLICATION, never a guard', () => {
  // Two creates on opposite sides of an `if`. Asserting both branch conditions
  // as assumptions would make the guard set contradictory and every such
  // transition would come back PROVED having checked nothing - the exact shape
  // of a vacuous proof. Each obligation carries its own antecedent instead.
  const c = T.app('>', [v('arg.qty'), T.num('0')]);
  const inst = nonNegativeFields(
    transition({
      creates: [
        { template: 'T', base: null, fields: { a: T.app('+', [v('arg.qty'), T.num('1')]) }, path: [c] },
        {
          template: 'T',
          base: null,
          fields: { a: T.app('-', [T.num('0'), v('arg.qty')]) },
          path: [T.app('not', [c])],
        },
      ],
    })
  );
  const smt = termToSmt(inst.goal);
  assert.match(smt, /\(or \(not \(> \|arg\.qty\| 0\)\) \(>= \(\+ \|arg\.qty\| 1\) 0\)\)/);
  assert.match(smt, /\(or \(not \(not \(> \|arg\.qty\| 0\)\)\) \(>= \(- 0 \|arg\.qty\|\) 0\)\)/);
  assert.deepEqual(inst.guards, [], 'branch conditions must not become assumptions');
});

test('non-negative-fields: an inherited field is disclosed, not counted as checked', () => {
  const inst = nonNegativeFields(
    transition({
      creates: [
        { template: 'Tok', base: 'this', fields: { amount: T.app('-', [v('this.amount'), T.num('1')]) }, path: [] },
      ],
    })
  );
  assert.equal(inst.coverage.total, 1, 'only the ASSIGNED field is an obligation');
  assert.ok(
    inst.notes.some((n) => /inherit every field they do not name/.test(n)),
    `expected an inheritance disclosure, got ${JSON.stringify(inst.notes)}`
  );
});

// ------------------------------- field types threaded from the package to the IR

/**
 * A package whose records carry real types, so the projection paths a choice
 * builds can be walked back to a declared sort:
 *
 *   data TokenData = TokenData with rate : Numeric 10; name : Text
 *   data SetArg    = SetArg    with newAmount : Numeric 10; memo : Text
 *   template Token with owner : Party; amount : Numeric 10; fee : Numeric 10;
 *                       info : TokenData
 *     choice Set : SetArg
 *       do create Token with owner = this.owner, amount = arg.newAmount,
 *                            fee = this.info.rate, info = this.info
 */
function buildTypedTemplateDalf() {
  const strings = [
    'Mod', 'Token', 'TokenData', 'SetArg', 'Set', 'this', 'arg',
    'owner', 'amount', 'fee', 'info', 'rate', 'name', 'newAmount', 'memo',
    'pkg', '1.0.0',
  ];
  const SI = Object.fromEntries(strings.map((x, i) => [x, i]));
  const dnameOrder = ['Mod', 'Token', 'TokenData', 'SetArg'];
  const DN = Object.fromEntries(dnameOrder.map((n, i) => [n, i]));
  const dnameMsgs = dnameOrder.map((n) =>
    bf(S.Package.internedDottedNames, bf(S.InternedDottedName.segmentsInternedStr, varint(SI[n])))
  );

  const BT = S.ENUMS.BuiltinType;
  const builtinType = (code) => bf(S.Type.builtin, vf(S.TypeBuiltin.builtin, code));
  // `Numeric 10` as the applied shape a compiler actually emits.
  const numericType = bf(
    S.Type.tapp,
    msg(bf(S.TypeApp.lhs, builtinType(BT.NUMERIC)), bf(S.TypeApp.rhs, vf(S.Type.nat, 10)))
  );
  const selfModule = msg(
    bf(S.ModuleId.packageId, bf(S.SelfOrImportedPackageId.selfPackageId, Buffer.alloc(0))),
    vf(S.ModuleId.moduleNameInternedDname, DN.Mod)
  );
  const tyconOf = (dn) =>
    msg(bf(S.TypeConId.module, selfModule), vf(S.TypeConId.nameInternedDname, dn));
  const conType = (dn) => bf(S.Type.con, bf(S.TypeCon.tycon, tyconOf(dn)));

  const field = (nameSi, typeBuf) =>
    bf(
      S.DataTypeFields.fields,
      msg(bf(S.FieldWithType.type, typeBuf), vf(S.FieldWithType.fieldInternedStr, nameSi))
    );
  const record = (dn, ...fields) =>
    bf(
      S.Module.dataTypes,
      msg(vf(S.DefDataType.nameInternedDname, dn), bf(S.DefDataType.record, msg(...fields)))
    );

  const proj = (recordExpr, fieldSi) =>
    msg(
      bf(
        S.Expr.recProj,
        msg(vf(S.RecProj.fieldInternedStr, fieldSi), bf(S.RecProj.record, recordExpr))
      )
    );
  const RECCON = S.message('Expr.RecCon');
  const FWE = S.message('FieldWithExpr');
  const recField = (nameSi, expr) =>
    bf(RECCON.fields, msg(bf(FWE.expr, expr), vf(FWE.fieldInternedStr, nameSi)));
  const thisVar = msg(vf(S.Expr.varInternedStr, SI.this));
  const argVar = msg(vf(S.Expr.varInternedStr, SI.arg));

  const createExpr = bf(
    S.Expr.update,
    bf(
      S.Update.create,
      msg(
        bf(S.message('Update.Create').template, tyconOf(DN.Token)),
        bf(
          S.message('Update.Create').expr,
          msg(
            bf(
              S.Expr.recCon,
              msg(
                bf(RECCON.tycon, tyconOf(DN.Token)),
                recField(SI.owner, proj(thisVar, SI.owner)),
                recField(SI.amount, proj(argVar, SI.newAmount)),
                recField(SI.fee, proj(proj(thisVar, SI.info), SI.rate)),
                recField(SI.info, proj(thisVar, SI.info))
              )
            )
          )
        )
      )
    )
  );

  const choice = msg(
    vf(S.TemplateChoice.nameInternedStr, SI.Set),
    vf(S.TemplateChoice.consuming, 1),
    bf(
      S.TemplateChoice.argBinder,
      msg(bf(S.VarWithType.type, conType(DN.SetArg)), vf(S.VarWithType.varInternedStr, SI.arg))
    ),
    bf(S.TemplateChoice.update, createExpr)
  );

  const module = msg(
    vf(S.Module.nameInternedDname, DN.Mod),
    record(DN.TokenData, field(SI.rate, numericType), field(SI.name, builtinType(BT.TEXT))),
    record(DN.SetArg, field(SI.newAmount, numericType), field(SI.memo, builtinType(BT.TEXT))),
    record(
      DN.Token,
      field(SI.owner, builtinType(BT.PARTY)),
      field(SI.amount, numericType),
      field(SI.fee, numericType),
      field(SI.info, conType(DN.TokenData))
    ),
    bf(
      S.Module.templates,
      msg(
        vf(S.DefTemplate.tyconInternedDname, DN.Token),
        vf(S.DefTemplate.paramInternedStr, SI.this),
        bf(S.DefTemplate.choices, choice)
      )
    )
  );

  const pkg = msg(
    bf(S.Package.modules, module),
    ...strings.map((x) => sf(S.Package.internedStrings, x)),
    ...dnameMsgs,
    bf(
      S.Package.metadata,
      msg(
        vf(S.PackageMetadata.nameInternedStr, SI.pkg),
        vf(S.PackageMetadata.versionInternedStr, SI['1.0.0'])
      )
    )
  );
  const payload = msg(sf(S.ArchivePayload.minor, '3'), bf(S.ArchivePayload.damlLf2, pkg));
  return msg(bf(S.Archive.payload, payload), sf(S.Archive.hash, 'typedtpl'));
}

test('field types reach the IR: symbols carry the sort the package declares', () => {
  const [t] = extractTransitions(decodeDalfRaw(buildTypedTemplateDalf()));
  assert.equal(`${t.template}.${t.choice}`, 'Token.Set');
  assert.deepEqual(Object.fromEntries(t.symbolTypes), {
    'this.owner': 'party',
    // rooted at the choice ARGUMENT's own record, via the binder's type
    'arg.newAmount': 'numeric',
    // a NESTED path, walked one hop through the declared record field
    'this.info.rate': 'numeric',
    'this.info': 'record',
  });
});

test('the CREATED record\'s own declared field sorts are attached to each create', () => {
  // The value side (symbolTypes) cannot answer for a field whose assigned
  // expression left the fragment - there is no symbol to consult. The created
  // record's declaration can, and this is where it comes from.
  const [t] = extractTransitions(decodeDalfRaw(buildTypedTemplateDalf()));
  assert.deepEqual(t.creates[0].fieldSorts, {
    owner: 'party',
    amount: 'numeric',
    fee: 'numeric',
    info: 'record',
  });
});

test('field types reach the property: the party field is excluded, the numerics checked', () => {
  // End to end: nothing in this choice USES any field as a number, so before
  // the declared types every one of the four assignments was "not known to be
  // numeric" and the transition was a refusal over four unanswered questions.
  const [t] = extractTransitions(decodeDalfRaw(buildTypedTemplateDalf()));
  const inst = nonNegativeFields(t);
  assert.equal(inst.applicable, true);
  assert.deepEqual(
    { checked: inst.coverage.checked, total: inst.coverage.total, excluded: inst.coverage.excluded },
    { checked: 2, total: 2, excluded: 2 }
  );
  assert.deepEqual(inst.coverage.excludedFields.sort(), ['Token.info (record)', 'Token.owner (party)']);
  const smt = termToSmt(inst.goal);
  assert.match(smt, /\(>= \|arg\.newAmount\| 0\)/);
  assert.match(smt, /\(>= \|this\.info\.rate\| 0\)/);
  assert.doesNotMatch(smt, /owner/, 'a Party must never reach a `>= 0`');
});

test('field types are absent, not guessed, where the path cannot be walked', () => {
  // No `dataTypes` on the context at all (a hand-built fake package): every
  // symbol is simply untyped, and the property falls back to positional
  // evidence exactly as it did before the types were decoded.
  const ctx = makeCtx(fakePkg(['this', 'amount']), {
    selfParam: 'this',
    argParam: null,
    label: 't',
  });
  const term = translateExpr(decodeMessage(exprProj(exprVar(0), 1)), ctx);
  assert.equal(term.name, 'this.amount', 'the symbol is still registered');
  assert.equal(ctx.symbolTypes.size, 0, 'no root type means no entry, never a default');

  // ...and a root type that IS known but whose path the records cannot be
  // walked along records nothing either: half a walk is not evidence.
  const withRoot = makeCtx(
    { ...fakePkg(['this', 'amount']), fieldSort: () => null },
    { selfParam: 'this', argParam: null, label: 't', selfType: { pkg: null, module: 'M', name: 'T' } }
  );
  withRoot.rootTypes.set('this', { pkg: { fieldSort: () => null }, module: 'M', name: 'T' });
  translateExpr(decodeMessage(exprProj(exprVar(0), 1)), withRoot);
  assert.equal(withRoot.symbolTypes.size, 0);
});

// ------------------------------------ non-negativity: the DECLARED field types
//
// Before the package's `DefDataType` records were decoded, a Party field and a
// Numeric field whose value the translation could not read were indistinguishable:
// both came back "not known to be numeric" and both were counted as unchecked
// obligations. These tests pin the three-way split that replaced that, and in
// particular pin the two directions it must not confuse - a declared
// non-numeric field is NOT an obligation, while a declared numeric field with
// an unreadable value IS one and is still skipped.

/** A transition whose symbols carry declared sorts, as lfir.js attaches them. */
const typed = (symbolTypes, overrides) =>
  transition({ symbolTypes: new Map(Object.entries(symbolTypes)), ...overrides });

test('non-negative-fields: a declared NUMERIC field is an obligation without positional evidence', () => {
  // `this.amount` is a bare projection: no arithmetic, no comparison, nothing
  // in the transition uses it as a number. Before the types it was skipped.
  // The package declares it Numeric, and that is the same fact the positional
  // evidence was standing in for - so it is checked.
  const inst = nonNegativeFields(
    typed(
      { 'this.amount': 'numeric' },
      { creates: [{ template: 'T', base: null, fields: { amount: v('this.amount') }, path: [] }] }
    )
  );
  assert.equal(inst.applicable, true);
  assert.equal(inst.coverage.checked, 1);
  assert.equal(inst.coverage.total, 1);
  assert.equal(termToSmt(inst.goal), '(>= |this.amount| 0)');
});

test('non-negative-fields: a declared NON-numeric field is EXCLUDED, not skipped', () => {
  // The distinction that matters: a Party field is not an obligation that went
  // unanswered, it is not an obligation. It must not appear in the coverage
  // denominator, or a transition assigning one party and one amount reports as
  // half-checked when it was in fact fully checked.
  const inst = nonNegativeFields(
    typed(
      {
        'this.amount': 'numeric',
        'arg.newOwner': 'party',
        'this.label': 'text',
        'this.when': 'time',
        'this.ref': 'cid',
        'this.flag': 'bool',
        'this.data': 'record',
      },
      {
        creates: [
          {
            template: 'T',
            base: null,
            fields: {
              amount: v('this.amount'),
              owner: v('arg.newOwner'),
              label: v('this.label'),
              when: v('this.when'),
              ref: v('this.ref'),
              flag: v('this.flag'),
              data: v('this.data'),
            },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(inst.applicable, true);
  assert.deepEqual(
    { checked: inst.coverage.checked, total: inst.coverage.total, excluded: inst.coverage.excluded },
    { checked: 1, total: 1, excluded: 6 },
    'the six non-numeric fields are excluded from the denominator, not counted as skipped'
  );
  assert.deepEqual(inst.coverage.skipped, [], 'nothing was skipped: nothing went unanswered');
  assert.deepEqual(inst.coverage.excludedFields.sort(), [
    'T.data (record)',
    'T.flag (bool)',
    'T.label (text)',
    'T.owner (party)',
    'T.ref (cid)',
    'T.when (time)',
  ]);
  // ...and the exclusion is DISCLOSED rather than silent.
  assert.ok(inst.notes.some((n) => /NOT obligations of this property/.test(n)));
  // None of the excluded symbols may appear in the goal: asserting `>= 0` of a
  // Party is a fabricated obligation, which is the failure this guards.
  assert.equal(termToSmt(inst.goal), '(>= |this.amount| 0)');
});

test('non-negative-fields: a declared numeric field with an unreadable value is skipped AND counted', () => {
  // Still skipped - an unreadable value is an unanswered question and is never
  // assumed non-negative - but counted apart from the unknowns, because here we
  // KNOW it was a question.
  const inst = nonNegativeFields(
    typed(
      { 'this.amount': 'numeric', 'this.rate': 'numeric' },
      {
        creates: [
          {
            template: 'T',
            base: null,
            fields: {
              amount: v('this.amount'),
              rate: T.ite(v('c'), v('this.rate'), T.unsupported('a fetch in the field expression', 'T')),
            },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(inst.applicable, true);
  assert.deepEqual(
    {
      checked: inst.coverage.checked,
      total: inst.coverage.total,
      numeric: inst.coverage.skippedNumeric,
      unreadable: inst.coverage.skippedUnreadable,
      unknown: inst.coverage.skippedUnknown,
      excluded: inst.coverage.excluded,
    },
    { checked: 1, total: 2, numeric: 1, unreadable: 0, unknown: 0, excluded: 0 }
  );
  assert.match(inst.coverage.skipped.join(' '), /T\.rate is declared numeric.*outside the fragment.*fetch/);
  assert.ok(inst.notes.some((n) => /declares NUMERIC could not be checked/.test(n)));
  assert.doesNotMatch(termToSmt(inst.goal), /this\.rate/);
});

test('non-negative-fields: an unreadable field DECLARED numeric is skipped and counted as a gap', () => {
  // This is the case only the created record's declaration can decide: the
  // value left the fragment, so there is no symbol carrying a sort, but the
  // field it lands in is declared Numeric all the same. It stays SKIPPED - an
  // unreadable value is never assumed non-negative - and it is counted apart
  // from the unknowns, because here we know a question went unanswered.
  const inst = nonNegativeFields(
    transition({
      creates: [
        {
          template: 'T',
          base: null,
          fieldSorts: { amount: 'numeric', info: 'record', memo: 'text' },
          fields: {
            amount: T.unsupported('a fetch in the field expression', 'T'),
            info: T.unsupported('a fetch in the field expression', 'T'),
            memo: T.unsupported('a fetch in the field expression', 'T'),
            ok: T.app('+', [v('x'), T.num('1')]),
          },
          path: [],
        },
      ],
    })
  );
  assert.equal(inst.applicable, true);
  assert.deepEqual(
    {
      checked: inst.coverage.checked,
      total: inst.coverage.total,
      numeric: inst.coverage.skippedNumeric,
      unreadable: inst.coverage.skippedUnreadable,
      unknown: inst.coverage.skippedUnknown,
      excluded: inst.coverage.excluded,
      nested: inst.coverage.excludedNestedRecords,
    },
    // `info` and `memo` are excluded although their values are unreadable too:
    // whether we could read a Text field's value does not make `>= 0` a
    // question about it.
    { checked: 1, total: 2, numeric: 1, unreadable: 0, unknown: 0, excluded: 2, nested: 1 }
  );
  assert.match(inst.coverage.skipped.join(' '), /T\.amount is declared numeric by the package/);
  // ...and the one exclusion that hides something is disclosed.
  assert.ok(
    inst.notes.some((n) => /does not descend into them/.test(n)),
    'a nested record assigned whole must carry the caveat that its own fields were not examined'
  );
});

test('non-negative-fields: the created record\'s declaration is preferred over the value\'s', () => {
  // Both are reads of the same package and agree in practice; where only one
  // answers, that one decides. Here only the created record does.
  const inst = nonNegativeFields(
    typed(
      { 'this.mystery': 'text' },
      {
        creates: [
          {
            template: 'T',
            base: null,
            fieldSorts: { amount: 'numeric' },
            fields: { amount: v('this.mystery') },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(inst.coverage.checked, 1, 'the field a contract is GIVEN is what the property is about');
  assert.equal(termToSmt(inst.goal), '(>= |this.mystery| 0)');
});

test('non-negative-fields: every assigned field non-numeric is NOT-APPLICABLE, not a refusal', () => {
  // The property does not concern this transition at all, and saying
  // NOT-MODELLABLE would claim something was refused when nothing was asked.
  const inst = nonNegativeFields(
    typed(
      { 'this.admin': 'party', 'this.label': 'text' },
      {
        creates: [
          {
            template: 'T',
            base: null,
            fields: { admin: v('this.admin'), label: v('this.label') },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, undefined, 'nothing was refused here');
  assert.match(inst.why, /declared NON-numeric type.*T\.admin \(party\).*T\.label \(text\)/);
});

test('non-negative-fields: an UNREADABLE field is still a refusal, never non-applicability', () => {
  // The NOT-MODELLABLE / NOT-APPLICABLE line must survive the new split: a
  // field whose value we could not read is a question we refused, and it must
  // not be folded into the "nothing here was a number" answer.
  const unreadable = nonNegativeFields(
    typed(
      {},
      { creates: [{ template: 'T', base: null, fields: { x: T.unsupported('outside', 'T') }, path: [] }] }
    )
  );
  assert.equal(unreadable.applicable, false);
  assert.equal(unreadable.notModellable, true, 'unreadable is a REFUSAL');

  // ...even mixed with a readable-but-untypable one.
  const mixed = nonNegativeFields(
    typed(
      {},
      {
        creates: [
          {
            template: 'T',
            base: null,
            fields: { x: T.unsupported('outside', 'T'), y: v('this.mystery') },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(mixed.notModellable, true);

  // ...while readable-but-untypable ALONE stays non-applicable, as before.
  const untypable = nonNegativeFields(
    typed({}, { creates: [{ template: 'T', base: null, fields: { y: v('this.mystery') }, path: [] }] })
  );
  assert.equal(untypable.applicable, false);
  assert.equal(untypable.notModellable, undefined);
  assert.match(untypable.why, /none of the 1 resolved created field\(s\) is known to be numeric/);
});

test('non-negative-fields: disagreeing branch declarations exclude nothing and check nothing', () => {
  // A conditional assignment whose two branches carry DIFFERENT declared sorts
  // cannot occur in well-typed Daml, so it means the walk read something wrong.
  // The direction that must not happen is EXCLUSION: dropping an obligation on
  // a disagreement would lose a real check silently. So a disagreement answers
  // nothing at all, and the field falls back to positional evidence - which
  // here finds none, so it is reported unchecked.
  const disagreeing = nonNegativeFields(
    typed(
      { 'this.a': 'party', 'this.b': 'text' },
      {
        creates: [
          { template: 'T', base: null, fields: { f: T.ite(v('c'), v('this.a'), v('this.b')) }, path: [] },
        ],
      }
    )
  );
  assert.equal(disagreeing.applicable, false);
  assert.match(disagreeing.why, /none of the 1 resolved created field\(s\) is known to be numeric/);
  assert.doesNotMatch(disagreeing.why, /NON-numeric/, 'a disagreement must not EXCLUDE the field');

  // Branches that AGREE do decide, in both directions.
  const agreeingNumeric = nonNegativeFields(
    typed(
      { 'this.a': 'numeric', 'this.b': 'numeric' },
      {
        creates: [
          { template: 'T', base: null, fields: { f: T.ite(v('c'), v('this.a'), v('this.b')) }, path: [] },
        ],
      }
    )
  );
  assert.equal(agreeingNumeric.coverage.checked, 1);

  const agreeingParty = nonNegativeFields(
    typed(
      { 'this.a': 'party', 'this.b': 'party' },
      {
        creates: [
          {
            template: 'T',
            base: null,
            fields: {
              f: T.ite(v('c'), v('this.a'), v('this.b')),
              amount: T.app('+', [v('x'), T.num('1')]),
            },
            path: [],
          },
        ],
      }
    )
  );
  assert.equal(agreeingParty.coverage.excluded, 1);
  assert.equal(agreeingParty.coverage.total, 1);
});

test('inferSorts: declared seeds fill only classes no position pinned', () => {
  // The seeding is what lets a field assigned from a declared-Numeric symbol
  // resolve to Real. It must be unable to MOVE an answer, which is what makes
  // it safe to add without changing a single emitted query.
  const positioned = T.app('=', [v('this.id'), T.str('x')]); // pins this.id to String
  const seeded = inferSorts([{ term: positioned, sort: 'Bool' }], [
    ['this.id', 'Real'],      // contradicts the position: the position wins
    ['this.unseen', 'Real'],  // not mentioned by any term: not declared at all
  ]);
  assert.equal(seeded.sorts.get('this.id'), 'String', 'a position always beats a declaration');
  assert.equal(seeded.sorts.has('this.unseen'), false, 'seeds never add variables');

  // An unpinned class is where a seed pays off: without it the class defaults
  // to Real but is NOT pinned, so it is not evidence of anything.
  const bare = { term: v('this.amount'), sort: 'field$0' };
  assert.equal(inferSorts([bare]).pinned.has('this.amount'), false);
  assert.equal(inferSorts([bare], [['this.amount', 'Real']]).pinned.has('this.amount'), true);
});

test('non-negative-fields: cvc5 proves what the guards imply and refutes what they do not', { skip: !SOLVER }, () => {
  const create = (term) => ({ template: 'T', base: null, fields: { amount: term }, path: [] });
  const provable = nonNegativeFields(
    transition({
      guards: [T.app('>=', [v('this.amount'), v('arg.qty')]), T.app('>=', [v('arg.qty'), T.num('0')])],
      creates: [create(T.app('-', [v('this.amount'), v('arg.qty')]))],
    })
  );
  assert.match(runSolver(buildQuery(provable.guards, provable.goal).script), /^unsat/m);

  const refutable = nonNegativeFields(
    transition({
      guards: [T.app('>=', [v('this.amount'), T.num('0')])],
      creates: [create(T.app('-', [v('this.amount'), v('arg.qty')]))],
    })
  );
  const out = runSolver(buildQuery(refutable.guards, refutable.goal).script);
  assert.match(out, /^sat/m);
  assert.match(out, /arg\.qty/);
});

// ------------------------------------------------------- create-authority

test('create-authority: applicability and the two refusals about the target', () => {
  assert.match(createAuthority(authTransition({ creates: [] })).why, /creates nothing/);

  const create = { template: 'Other', base: null, fields: { admin: v('this.admin') }, path: [] };

  // the target is not in this package: refuse, never assume it needs nothing
  const missing = createAuthority(authTransition({ creates: [create], templates: {} }));
  assert.equal(missing.applicable, false);
  assert.equal(missing.notModellable, true);
  assert.match(missing.why, /no template of that name is declared in this package/);

  // two templates share the name: refuse rather than pick one
  const ambiguous = createAuthority(
    authTransition({
      creates: [create],
      templates: { Other: { refs: [], exact: false, ambiguous: true, why: 'two templates named `Other`' } },
    })
  );
  assert.match(ambiguous.why, /two templates named/);

  // the target's clause was only partly walked: the required set is not known
  // to be complete, so proving the recovered part would claim too much
  const inexact = createAuthority(
    authTransition({
      creates: [create],
      templates: { Other: { refs: [{ path: 'this.admin', presence: T.bool(true) }], exact: false, why: 'a helper' } },
    })
  );
  assert.equal(inexact.applicable, false);
  assert.match(inexact.why, /only partly walked/);
});

test('create-authority: no recoverable authority at all is a refusal', () => {
  const inst = createAuthority(
    authTransition({
      creates: [{ template: 'Other', base: null, fields: { admin: v('this.admin') }, path: [] }],
      signatories: { refs: [], exact: false, why: 'a computed signatory list' },
      controllers: { refs: [], exact: false, why: 'an interface view' },
      templates: { Other: sigOf('this.admin') },
    })
  );
  assert.equal(inst.applicable, false);
  assert.equal(inst.notModellable, true);
  assert.match(inst.why, /no party reference could be recovered/);
});

test('create-authority: a linked signatory is related ONLY through the field assignment', () => {
  const inst = createAuthority(
    authTransition({
      creates: [{ template: 'Other', base: null, fields: { boss: v('this.admin') }, path: [] }],
      templates: { Other: sigOf('this.boss') },
    })
  );
  assert.equal(inst.applicable, true, inst.why);
  // `Other.boss` became `this.admin` because the create assigned it so - not
  // because the two are both called `boss`.
  const smt = termToSmt(inst.goal);
  assert.match(smt, /\|party:this\.admin\|/);
  assert.doesNotMatch(smt, /party:this\.boss/);
  assert.equal(inst.coverage.checked, 1);
});

test('create-authority: an UNLINKED party can never yield PROVED', { skip: !SOLVER }, () => {
  // THE security-critical case. `Other.boss` is assigned an expression the
  // translation cannot relate to any party of the creating contract. It must
  // not be assumed equal to `this.admin` (a false PROVED, which is the lie
  // this property exists to avoid) and it must not be assumed distinct
  // either. The create is left UNCHECKED, with the reason.
  const unlinked = createAuthority(
    authTransition({
      creates: [
        {
          template: 'Other',
          base: null,
          fields: { boss: T.uf('Shared:pickApprover', [v('this.admin')], null, null) },
          path: [],
        },
      ],
      templates: { Other: sigOf('this.boss') },
    })
  );
  assert.equal(unlinked.applicable, false, 'an unlinkable party must not produce a query at all');
  assert.equal(unlinked.notModellable, true);
  assert.match(unlinked.why, /two field names are NOT assumed to denote the same ledger Party/);

  // ...and with a second, linkable create alongside it the verdict is PARTIAL,
  // which verify.js prints as PROVED-PARTIAL and never as PROVED.
  const mixed = createAuthority(
    authTransition({
      creates: [
        {
          template: 'Other',
          base: null,
          fields: { boss: T.uf('Shared:pickApprover', [v('this.admin')], null, null) },
          path: [],
        },
        { template: 'Plain', base: null, fields: { boss: v('this.admin') }, path: [] },
      ],
      templates: { Other: sigOf('this.boss'), Plain: sigOf('this.boss') },
    })
  );
  assert.equal(mixed.applicable, true);
  assert.equal(mixed.coverage.checked, 1);
  assert.equal(mixed.coverage.total, 2);
  assert.ok(mixed.coverage.checked < mixed.coverage.total, 'must print as PROVED-PARTIAL');
  assert.match(runSolver(buildQuery(mixed.guards, mixed.goal).script), /^unsat/m);
});

test('create-authority: cvc5 proves a covered create and refutes an uncovered one', { skip: !SOLVER }, () => {
  const covered = createAuthority(
    authTransition({
      creates: [{ template: 'Other', base: null, fields: { boss: v('arg.actor') }, path: [] }],
      templates: { Other: sigOf('this.boss') },
    })
  );
  assert.match(runSolver(buildQuery(covered.guards, covered.goal).script), /^unsat/m);

  // the created contract needs a party the choice does not act with: the
  // constants are unrelated, so the goal is refuted with a model naming them
  const uncovered = createAuthority(
    authTransition({
      creates: [{ template: 'Other', base: null, fields: { boss: v('this.outsider') }, path: [] }],
      templates: { Other: sigOf('this.boss') },
    })
  );
  const out = runSolver(buildQuery(uncovered.guards, uncovered.goal).script);
  assert.match(out, /^sat/m);
  assert.match(out, /party:this\.outsider/);
});

test('create-authority: a CONDITIONAL signatory is carried with its condition', { skip: !SOLVER }, () => {
  // `[this.admin] <> optionalParty this.gov.approver` is what compiled Daml
  // produces, and the second party is a signatory only when the Optional is
  // set. Because the create copies `gov` wholesale, the created contract's
  // presence flag IS the creating contract's presence flag - the same symbol -
  // so the obligation `present(s) => covered(s)` discharges. Dropping the
  // condition instead would either over-state the required set (a spurious
  // DISPROVED) or over-state the authority (a false PROVED).
  const some = (p) => T.varRef(`${p}.$some`, 'Bool');
  const inst = createAuthority(
    authTransition({
      creates: [
        { template: 'Other', base: null, fields: { admin: v('this.admin'), gov: v('this.gov') }, path: [] },
      ],
      signatories: {
        refs: [
          { path: 'this.admin', presence: T.bool(true) },
          { path: 'this.gov.approver.$value', presence: some('this.gov.approver') },
        ],
        exact: true,
        why: null,
      },
      controllers: { refs: [], exact: false, why: 'none recovered' },
      templates: {
        Other: {
          refs: [
            { path: 'this.admin', presence: T.bool(true) },
            { path: 'this.gov.approver.$value', presence: some('this.gov.approver') },
          ],
          exact: true,
          why: null,
        },
      },
    })
  );
  assert.equal(inst.applicable, true, inst.why);
  const { script } = buildQuery(inst.guards, inst.goal);
  assert.match(script, /\(declare-const \|this\.gov\.approver\.\$some\| Bool\)/);
  assert.match(runSolver(script), /^unsat/m);
  // the missing controllers are disclosed as an under-approximation
  assert.ok(inst.notes.some((n) => /UNDER-approximation/.test(n)), JSON.stringify(inst.notes));
});

test('create-authority: `create this with ...` inherits only within the same template', () => {
  // A RecUpd over `this` only type-checks against the same template, so the
  // un-overridden signatory field is the pre-state's. A target name that does
  // NOT match means the walk mis-identified the record: refuse rather than
  // inherit a field from a different template.
  const same = createAuthority(
    authTransition({
      creates: [{ template: 'Tok', base: 'this', fields: { amount: T.num('1') }, path: [] }],
      templates: { Tok: sigOf('this.admin') },
    })
  );
  assert.equal(same.applicable, true, same.why);
  assert.match(termToSmt(same.goal), /\(= \|party:this\.admin\| \|party:this\.admin\|\)/);

  const crossed = createAuthority(
    authTransition({
      creates: [{ template: 'Other', base: 'this', fields: { amount: T.num('1') }, path: [] }],
      templates: { Other: sigOf('this.admin') },
    })
  );
  assert.equal(crossed.applicable, false);
  assert.match(crossed.why, /left unchecked/);
});

// ----------------------------------------------------------- the Party sort

test('the Party sort is uninterpreted, declared on demand, and never arithmetic', () => {
  const goal = T.app('=', [T.party('this.admin'), T.party('arg.actor')]);
  const { script, vars } = buildQuery([], goal);
  assert.match(script, /\(declare-sort Party 0\)/);
  assert.match(script, /\(declare-const \|party:this\.admin\| Party\)/);
  assert.match(script, /\(declare-const \|party:arg\.actor\| Party\)/);
  assert.deepEqual(vars.sort(), ['party:arg.actor', 'party:this.admin']);

  // an arithmetic query does not grow a sort declaration it never uses
  assert.doesNotMatch(buildQuery([], T.app('>', [v('x'), T.num('0')])).script, /declare-sort/);

  // a party in a numeric position is a CONFLICT, not a silent coercion
  assert.throws(
    () => buildQuery([], T.app('>', [T.party('this.admin'), T.num('0')])),
    /sort conflicts/
  );

  // T.party namespaces the symbol, so the arithmetic symbol for the same path
  // stays a DIFFERENT constant: a guard can never establish party identity
  assert.equal(T.party('this.admin').name, 'party:this.admin');
  assert.equal(T.party(T.party('this.admin').name).name, 'party:this.admin');
});

test('inferSorts reports which sorts came from a POSITION rather than the default', () => {
  const { sorts, pinned } = inferSorts([
    { term: T.app('>', [v('a'), T.num('1')]), sort: 'Bool' },
    { term: T.app('not', [v('b')]), sort: 'Bool' },
    { term: T.app('=', [v('c'), v('d')]), sort: 'Bool' },
    { term: T.party('this.admin'), sort: 'free$0' },
  ]);
  assert.equal(sorts.get('a'), 'Real');
  assert.ok(pinned.has('a'), 'a comparison operand is pinned');
  assert.ok(pinned.has('b'), 'a Bool position is pinned');
  assert.ok(pinned.has('party:this.admin'), 'a party constant is pinned');
  // `c` and `d` are only known to share a sort; nothing pinned it, so `Real`
  // is the emitter's DEFAULT and must not be read as evidence.
  assert.equal(sorts.get('c'), 'Real');
  assert.equal(pinned.has('c'), false);
  assert.equal(pinned.has('d'), false);
});

// -------------------------------------------- against the compiled package

test(
  'party references recovered from the token DAR: definite, conditional and refused',
  { skip: !HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}` },
  () => {
    const ts = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 });
    const t = ts.find((x) => x.template === 'CollateralUnitToken' && x.choice === 'LockCollateralUnitToken');
    assert.ok(t, 'expected a LockCollateralUnitToken transition');

    // `controller this.admin` is read exactly, with no condition attached
    assert.equal(t.controllers.exact, true, t.controllers.why);
    assert.deepEqual(t.controllers.refs.map((r) => r.path), ['this.admin']);
    assert.deepEqual(t.controllers.refs.map((r) => r.presence.k), ['bool']);

    // The templates' own signatory clause is `[this.admin] <> optionalParty
    // this.governance.approvalParty`, whose tail bottoms out in a Foldable
    // dictionary this walk does not reduce. `this.admin` IS recovered (an
    // element of a cons is contributed whatever the tail turns out to be) and
    // the clause is reported INEXACT, which is what stops it being used as a
    // required-signatory set.
    assert.equal(t.signatories.exact, false);
    assert.deepEqual(t.signatories.refs.map((r) => r.path), ['this.admin']);
    assert.match(t.signatories.why, /cannot reduce to its body/);

    // ...and that inexactness is what create-authority refuses on, by name
    const inst = createAuthority(t);
    assert.equal(inst.applicable, false);
    assert.equal(inst.notModellable, true);
    assert.match(inst.why, /LockedCollateralUnitToken: its signatory clause was only partly walked/);

    // an INTERFACE choice's controllers are over the view: reported, not guessed
    const viaIface = ts.find((x) => x.via && x.controllers);
    assert.equal(viaIface.controllers.exact, false);
    assert.match(viaIface.controllers.why, /interface view/);
  }
);

test(
  'the package signatory table keys templates by name and is shared, not per transition',
  { skip: !HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}` },
  () => {
    const ts = extractTransitions(readDarRaw(TOKENS_DAR), { bound: 3 });
    const table = ts[0].templateSignatories;
    assert.ok(table instanceof Map);
    for (const t of ts) assert.equal(t.templateSignatories, table, 'one table per package');
    assert.ok(table.has('CollateralUnitToken'));
    // every template got an entry, and none of them silently claims an empty
    // signatory set: an empty `refs` always comes with `exact: false`
    for (const [name, a] of table) {
      assert.ok(Array.isArray(a.refs), name);
      if (a.refs.length === 0) assert.equal(a.exact, false, `${name} claims no signatories`);
    }
  }
);

test(
  'the CLI selects each new property on its own and runs all four by default',
  { skip: (!SOLVER && 'no cvc5') || (!HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}`) },
  () => {
    const cli = new URL('../backend/verify.js', import.meta.url).pathname;
    const run = (extra) => {
      let out;
      try {
        out = execFileSync('node', [cli, TOKENS_DAR, '--choice', 'LockCollateralUnitToken', '--json', ...extra], {
          encoding: 'utf8',
          maxBuffer: 1 << 26,
        });
      } catch (e) {
        out = e.stdout;
      }
      return JSON.parse(out).results;
    };
    const one = run(['--property', 'non-negative-fields']);
    assert.deepEqual([...new Set(one.map((r) => r.property))], ['non-negative-fields']);
    const other = run(['--property', 'create-authority']);
    assert.deepEqual([...new Set(other.map((r) => r.property))], ['create-authority']);
    assert.deepEqual(
      [...new Set(run([]).map((r) => r.property))].sort(),
      ['amount-conservation', 'create-authority', 'division-safety', 'non-negative-fields']
    );
    // a partial answer never prints as a bare PROVED, and it carries the split
    const partial = one.find((r) => r.status === 'PROVED-PARTIAL');
    assert.ok(partial, `expected a PROVED-PARTIAL, got ${one.map((r) => r.status).join(', ')}`);
    assert.ok(partial.coverage.checked < partial.coverage.total);
    assert.match(partial.note, /obligation\(s\) checked/);
  }
);

test(
  'the two new properties leave the existing verdicts on the token DAR exactly as they were',
  { skip: (!SOLVER && 'no cvc5') || (!HAVE_TOKENS_DAR && `DAR not present at ${TOKENS_DAR}`) },
  () => {
    // The regression this whole change had to preserve: a shared edit (the
    // Party sort, the `pinned` set) must not move a verdict that was already
    // being produced. Run the two old properties and count.
    const cli = new URL('../backend/verify.js', import.meta.url).pathname;
    let out;
    try {
      out = execFileSync(
        'node',
        [cli, TOKENS_DAR, '--property', 'amount-conservation', '--property', 'division-safety', '--json'],
        { encoding: 'utf8', maxBuffer: 1 << 26 }
      );
    } catch (e) {
      out = e.stdout;
    }
    const counts = {};
    for (const r of JSON.parse(out).results) {
      const k = r.status.split(' (')[0];
      counts[k] = (counts[k] || 0) + 1;
    }
    assert.deepEqual(counts, {
      PROVED: 10,
      'PROVED-BOUNDED': 7,
      DISPROVED: 3,
      'NOT-APPLICABLE': 116,
    });
  }
);
