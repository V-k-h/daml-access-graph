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
import { execFileSync } from 'node:child_process';
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
  assert.match(script, /\(assert \(> \|x\| 0\)\)/);
  assert.match(script, /\(assert \(not \(> \(\+ \|x\| 1\) 1\)\)\)/);
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

// ---------------------------------------------- the real thing, end to end

const TOKENS_DAR =
  '/private/tmp/claude-501/-Users-vijay-Downloads-carbon-core/713989a1-4f06-45ac-823b-b4ec40f8b2b8/scratchpad/canton/dlt-canton-main/daml/canton-tokens.dar';
const HAVE_TOKENS_DAR = existsSync(TOKENS_DAR);

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
