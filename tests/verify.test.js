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
import { writeFileSync, mkdtempSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { T, hasUnsupported, unsupportedReasons, divisors } from '../backend/lfir.js';
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
import { decodeDalfRaw } from '../backend/dalf.js';
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
