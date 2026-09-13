// tests/diff.test.js
//
//   node --test
//
// Graph diffing (src/diff.js) and the CI baseline (src/baseline.js).
//
// The invariant these exist to protect: a gate that cries wolf gets turned off.
// So the round-trip must be exactly clean, edge renumbering must be invisible,
// and a reworded finding message must not read as a new finding.

import test from 'node:test';
import assert from 'node:assert/strict';

import { parseDaml } from '../src/parser.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';
import { diffGraphs, diffFindings, findingFingerprint } from '../src/diff.js';
import { createBaseline, compareToBaseline, BASELINE_VERSION } from '../src/baseline.js';

const graphOf = (src) => buildGraph(parseDaml(src));

const BASE = `module A where
template Token
  with
    issuer : Party
    owner : Party
  where
    signatory issuer
    observer owner

    nonconsuming choice Peek : ()
      controller issuer
      do return ()
`;

const codesOf = (changes) => new Set(changes.map((c) => c.code));
const byDirection = (changes, direction) => changes.filter((c) => c.direction === direction);

test('diff: an identical graph produces no changes', () => {
  const { changes, summary } = diffGraphs(graphOf(BASE), graphOf(BASE));
  assert.deepEqual(changes, []);
  assert.equal(summary.total, 0);
});

test('diff: edge ids are ignored, only (source, kind, target) matters', () => {
  // Renumber every edge id the way an unrelated earlier change would.
  const a = graphOf(BASE);
  const b = graphOf(BASE);
  b.edges = b.edges.map((e, i) => ({ ...e, id: `zzz${b.edges.length - i}` }));
  assert.deepEqual(diffGraphs(a, b).changes, [], 'id churn must not surface as changes');
});

test('diff: a new choice and its controller widen the access structure', () => {
  const after = graphOf(`module A where
template Token
  with
    issuer : Party
    owner : Party
  where
    signatory issuer
    observer owner

    nonconsuming choice Peek : ()
      controller issuer
      do return ()

    choice Seize : ()
      controller owner
      do return ()
`);
  const { changes, summary } = diffGraphs(graphOf(BASE), after);
  const widening = byDirection(changes, 'widening');
  assert.ok(codesOf(widening).has('edge-added-declares'), 'the new choice is new exercisable surface');
  assert.ok(codesOf(widening).has('edge-added-controller'), 'a new party may now exercise');
  assert.equal(summary.byDirection.narrowing, 0);
});

test('diff: adding an observer widens, adding a signatory narrows', () => {
  const withObserver = graphOf(`module A where
template Token with issuer : Party, owner : Party, auditor : Party where
  signatory issuer
  observer owner, auditor
`);
  const withSignatory = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer, owner
  observer owner
`);

  const obs = diffGraphs(graphOf(BASE), withObserver).changes.filter(
    (c) => c.code === 'edge-added-observer'
  );
  assert.equal(obs.length, 1);
  assert.equal(obs[0].direction, 'widening', 'one more party can see these contracts');

  const sig = diffGraphs(graphOf(BASE), withSignatory).changes.filter(
    (c) => c.code === 'edge-added-signatory'
  );
  assert.equal(sig.length, 1);
  assert.equal(sig[0].direction, 'narrowing', 'one more party must authorize');
});

test('diff: removing a signatory widens (fewer required authorizers)', () => {
  const before = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer, owner
`);
  const after = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer
`);
  const removed = diffGraphs(before, after).changes.filter((c) => c.code === 'edge-removed-signatory');
  assert.equal(removed.length, 1);
  assert.equal(removed[0].direction, 'widening');
});

test('diff: deleting a template is neutral, not widening', () => {
  // A false-alarm shape that used to fail the gate. README says "removing a
  // signatory widens, for the same reason in reverse", and the differ applied
  // that literally, so deleting a template outright - which removes its
  // signatory edges along with everything else - read as widening even though
  // nothing gained reach: the template is gone and has no contracts left to
  // authorize. A gate that fires on deleting dead code is a gate people switch
  // off.
  //
  // The rule is now that an edge whose SOURCE node also disappeared is
  // neutral, with the neutral node-removed change carrying the report. The
  // ADDED side is treated symmetrically (an edge whose source is itself new is
  // also neutral), because the two halves must agree for the antisymmetry law
  // in tests/property.test.js to hold - diffing in the opposite direction has
  // to flip every direction, and a one-sided rule breaks it.
  const before = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer
  observer owner
template Other with p : Party where
  signatory p
`);
  const after = graphOf(`module A where
template Other with p : Party where
  signatory p
`);
  const { changes, summary } = diffGraphs(before, after);
  const sig = changes.find((c) => c.code === 'edge-removed-signatory');
  assert.ok(sig, 'the deleted template took its signatory edge with it');
  assert.equal(sig.direction, 'neutral', 'the source is gone, so no access widened');
  assert.match(sig.message, /with Token itself/);
  assert.ok(
    changes.some((c) => c.code === 'node-removed-template' && c.direction === 'neutral'),
    'the deletion itself is reported, and is neutral'
  );
  assert.equal(summary.byDirection.widening, 0, 'a pure deletion must not fail the gate');

  // The mirror: adding that template back is also neutral, which is what keeps
  // the diff antisymmetric.
  const back = diffGraphs(after, before);
  assert.equal(back.summary.byDirection.widening, 0);
  assert.equal(back.summary.byDirection.narrowing, 0);
});

test('diff: removing a signatory from a SURVIVING template still widens', () => {
  // The rule above must not swallow the real case: when the template lives on,
  // dropping one of its signatories genuinely means fewer parties must
  // authorize, and that is the thing the gate exists to catch.
  const before = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer, owner
`);
  const after = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer
`);
  const removed = diffGraphs(before, after).changes.filter(
    (c) => c.code === 'edge-removed-signatory'
  );
  assert.equal(removed.length, 1);
  assert.equal(removed[0].direction, 'widening');
});

test('diff: a choice becoming consuming widens', () => {
  const after = graphOf(BASE.replace('nonconsuming choice Peek', 'choice Peek'));
  const change = diffGraphs(graphOf(BASE), after).changes.find(
    (c) => c.code === 'choice-consuming-changed'
  );
  assert.ok(change);
  assert.equal(change.direction, 'widening');
  assert.match(change.message, /can archive the contract/);

  // and the reverse narrows
  const back = diffGraphs(after, graphOf(BASE)).changes.find(
    (c) => c.code === 'choice-consuming-changed'
  );
  assert.equal(back.direction, 'narrowing');
});

test('diff: a new implements edge widens, being a whole interface surface', () => {
  const after = graphOf(`module A where
template Token with issuer : Party, owner : Party where
  signatory issuer
  observer owner
  nonconsuming choice Peek : ()
    controller issuer
    do return ()
  interface instance Holding for Token where
    view = HoldingView with owner
`);
  const change = diffGraphs(graphOf(BASE), after).changes.find(
    (c) => c.code === 'edge-added-implements'
  );
  assert.ok(change);
  assert.equal(change.direction, 'widening');
});

test('diff: changed key maintainers are reported as widening', () => {
  const before = graphOf(`module A where
template M with admin : Party, other : Party where
  signatory admin
  key (admin, "x") : (Party, Text)
  maintainer key._1
`);
  const after = graphOf(`module A where
template M with admin : Party, other : Party where
  signatory admin
  key (other, "x") : (Party, Text)
  maintainer key._1
`);
  const change = diffGraphs(before, after).changes.find((c) => c.code === 'key-maintainers-changed');
  assert.ok(change);
  assert.equal(change.direction, 'widening');
  assert.match(change.message, /who may look these contracts up by key/);
});

// ---------------------------------------------------------------------------
// findings
// ---------------------------------------------------------------------------

test('findings: the fingerprint survives a reworded message', () => {
  const a = { code: 'no-observers', subjects: ['tpl:Token'], severity: 'info', message: 'old wording' };
  const b = { code: 'no-observers', subjects: ['tpl:Token'], severity: 'info', message: 'completely new wording' };
  assert.equal(findingFingerprint(a), findingFingerprint(b));
  assert.deepEqual(diffFindings([a], [b]).added, [], 'a rewording is not a new finding');
});

test('findings: subject order does not affect identity', () => {
  const a = { code: 'x', subjects: ['a', 'b'], severity: 'info', message: '' };
  const b = { code: 'x', subjects: ['b', 'a'], severity: 'info', message: '' };
  assert.equal(findingFingerprint(a), findingFingerprint(b));
});

test('findings: a genuinely different subject is a new finding', () => {
  const a = { code: 'no-observers', subjects: ['tpl:Token'], severity: 'info', message: '' };
  const b = { code: 'no-observers', subjects: ['tpl:Other'], severity: 'info', message: '' };
  const d = diffFindings([a], [b]);
  assert.equal(d.added.length, 1);
  assert.equal(d.removed.length, 1);
});

// ---------------------------------------------------------------------------
// baseline
// ---------------------------------------------------------------------------

test('baseline: a round-trip against the same graph is exactly clean', () => {
  // The invariant that matters most: a gate that reports changes on an
  // unchanged tree is worse than no gate.
  const g = graphOf(BASE);
  const a = analyzeAll(g);
  const baseline = createBaseline(g, a);
  assert.equal(baseline.version, BASELINE_VERSION);

  const result = compareToBaseline(baseline, g, a);
  assert.equal(result.graphDiff.summary.total, 0, 'no graph changes');
  assert.deepEqual(result.newFindings, [], 'no new findings');
  assert.deepEqual(result.fixedFindings, [], 'no findings disappeared');
  assert.equal(result.ok, true);
});

test('baseline: round-trip stays clean with interfaces, keys and nonconsuming choices', () => {
  // These are exactly the cases that need node metadata preserved.
  const g = graphOf(`module A where

interface Utxo where
  viewtype UtxoView
  nonconsuming choice Act : ()
    controller (view this).admin
    do return ()

template Tok
  with
    admin : Party
    owner : Party
  where
    signatory admin
    observer owner

    key (admin, "id") : (Party, Text)
    maintainer key._1

    nonconsuming choice Peek : ()
      controller owner
      do return ()

    interface instance Utxo for Tok where
      view = UtxoView with admin

    interface instance Holding for Tok where
      view = HoldingView with owner
`);
  const a = analyzeAll(g);
  const result = compareToBaseline(createBaseline(g, a), g, a);
  assert.equal(result.graphDiff.summary.total, 0, result.graphDiff.changes.map((c) => c.message).join('; '));
  assert.equal(result.ok, true);
});

test('baseline: catches a new finding and a widening change', () => {
  const before = graphOf(BASE);
  const baseline = createBaseline(before, analyzeAll(before));

  const after = graphOf(`module A where
template Token
  with
    issuer : Party
    owner : Party
  where
    signatory issuer
    observer owner

    nonconsuming choice Peek : ()
      controller issuer
      do return ()

    choice Seize : ()
      controller owner
      do return ()
`);
  const result = compareToBaseline(baseline, after, analyzeAll(after));

  assert.equal(result.ok, false);
  assert.ok(result.widening.length > 0, 'the new choice widens the structure');
  assert.ok(
    result.newFindings.some((f) => f.code === 'nonsignatory-consuming'),
    'a non-signatory-controlled consuming choice is a new finding'
  );
});

test('baseline: reports findings that no longer occur', () => {
  const before = graphOf(`module A where
template Token with issuer : Party where
  signatory issuer
  choice C : ()
    do return ()
`);
  const baseline = createBaseline(before, analyzeAll(before));

  const after = graphOf(`module A where
template Token with issuer : Party where
  signatory issuer
  choice C : ()
    controller issuer
    do return ()
`);
  const result = compareToBaseline(baseline, after, analyzeAll(after));
  assert.ok(result.fixedFindings.some((fp) => fp.startsWith('no-controller#')));
});

test('baseline: an unsupported version is rejected rather than half-read', () => {
  const g = graphOf(BASE);
  const baseline = { ...createBaseline(g, analyzeAll(g)), version: 999 };
  assert.throws(() => compareToBaseline(baseline, g, analyzeAll(g)), /Unsupported baseline version/);
});

test('baseline: one without nodeMeta does not invent metadata changes', () => {
  // Forward compatibility for baselines committed before nodeMeta existed.
  const g = graphOf(BASE);
  const a = analyzeAll(g);
  const baseline = createBaseline(g, a);
  delete baseline.graph.nodeMeta;

  const result = compareToBaseline(baseline, g, a);
  assert.equal(
    result.graphDiff.changes.filter((c) => c.scope === 'meta').length,
    0,
    'metadata comparison must be skipped, not guessed'
  );
  assert.equal(result.ok, true);
});

// ---------------------------------------------------------------------------
// Verdict baseline (the CI gate for proofs)
// ---------------------------------------------------------------------------

test('verdict baseline: a round-trip against the same report is clean', async () => {
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const report = {
    package: 'pkg',
    results: [
      { property: 'amount-conservation', transition: 'T.A', status: 'PROVED' },
      { property: 'amount-conservation', transition: 'T.B', status: 'DISPROVED' },
      { property: 'division-safety', transition: 'T.C', status: 'NOT-APPLICABLE' },
    ],
  };
  const b = createVerdictBaseline([report]);
  const cmp = compareVerdicts(b, [report]);
  assert.equal(cmp.regressions.length, 0);
  assert.equal(cmp.improvements.length, 0);
  assert.equal(cmp.unchanged, 3);
  assert.equal(cmp.ok, true);
});

test('verdict baseline: losing a proof is a regression, gaining one is not', async () => {
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const before = {
    package: 'pkg',
    results: [
      { property: 'p', transition: 'T.Lost', status: 'PROVED' },
      { property: 'p', transition: 'T.Gained', status: 'NOT-APPLICABLE' },
    ],
  };
  const after = {
    package: 'pkg',
    results: [
      { property: 'p', transition: 'T.Lost', status: 'NOT-MODELLABLE' },
      { property: 'p', transition: 'T.Gained', status: 'PROVED' },
    ],
  };
  const cmp = compareVerdicts(createVerdictBaseline([before]), [after]);
  assert.equal(cmp.ok, false);
  assert.equal(cmp.regressions.length, 1);
  assert.equal(cmp.regressions[0].kind, 'proof-lost');
  assert.equal(cmp.improvements.length, 1, 'the gain must not be a regression');
});

test('verdict baseline: a bound change is not a regression, a family change is', async () => {
  const { createVerdictBaseline, compareVerdicts, statusFamily } = await import(
    '../src/verdict-baseline.js'
  );
  // the bound is a property of the RUN, not of the code
  assert.equal(statusFamily('PROVED-BOUNDED (lists up to length 3)'), 'PROVED-BOUNDED');
  const b = createVerdictBaseline([
    { package: 'pkg', results: [{ property: 'p', transition: 'T.M', status: 'PROVED-BOUNDED (lists up to length 3)' }] },
  ]);
  const sameFamily = compareVerdicts(b, [
    { package: 'pkg', results: [{ property: 'p', transition: 'T.M', status: 'PROVED-BOUNDED (lists up to length 7)' }] },
  ]);
  assert.equal(sameFamily.ok, true, 'a different bound is the same claim family');

  const lost = compareVerdicts(b, [
    { package: 'pkg', results: [{ property: 'p', transition: 'T.M', status: 'DISPROVED' }] },
  ]);
  assert.equal(lost.ok, false);
});

test('verdict baseline: an untriaged new finding fails the gate', async () => {
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const b = createVerdictBaseline([{ package: 'pkg', results: [] }]);
  const cmp = compareVerdicts(b, [
    { package: 'pkg', results: [{ property: 'p', transition: 'T.New', status: 'DISPROVED' }] },
  ]);
  assert.equal(cmp.ok, false);
  assert.equal(cmp.regressions[0].kind, 'new-finding');
});

test('verdict baseline: a proof that vanishes entirely is caught', async () => {
  // Easy to miss by diffing only what is present: the obligation is gone, so
  // there is no verdict to compare against.
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const b = createVerdictBaseline([
    { package: 'pkg', results: [{ property: 'p', transition: 'T.Gone', status: 'PROVED' }] },
  ]);
  const cmp = compareVerdicts(b, [{ package: 'pkg', results: [] }]);
  assert.equal(cmp.ok, false);
  assert.equal(cmp.regressions[0].kind, 'proof-disappeared');
});

test('verdict baseline: an unsupported version is rejected, not half-read', async () => {
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const b = { ...createVerdictBaseline([{ package: 'p', results: [] }]), version: 99 };
  assert.throws(() => compareVerdicts(b, []), /Unsupported verdict baseline version/);
});

test('verdict baseline: two DARs of the same package do not erase each other', async () => {
  // REGRESSION TEST for a bug the round-trip property in tests/property.test.js
  // found: createVerdictBaseline wrote `packages[name] = entries` per report,
  // so when two DARs carried the same package name (two versions of one
  // package in the scanned directory) the later one ERASED the earlier one's
  // obligations. Comparing the very same, unchanged input against that
  // baseline then reported the erased obligations as proof-disappeared
  // regressions - a red gate on a tree nobody had touched, which
  // --update-baseline could not clear because the refresh reproduced the
  // collapse. Same-named reports are now merged on both sides.
  const { createVerdictBaseline, compareVerdicts } = await import('../src/verdict-baseline.js');
  const v1 = {
    dar: 'tokens-1.0.dar',
    package: 'tokens',
    results: [{ property: 'p', transition: 'T.A', status: 'PROVED' }],
  };
  const v2 = {
    dar: 'tokens-2.0.dar',
    package: 'tokens',
    results: [{ property: 'p', transition: 'T.B', status: 'PROVED' }],
  };

  const baseline = createVerdictBaseline([v1, v2]);
  assert.deepEqual(
    Object.keys(baseline.packages.tokens).sort(),
    ['p::T.A', 'p::T.B'],
    'both DARs contribute their obligations'
  );

  const cmp = compareVerdicts(baseline, [v1, v2]);
  assert.equal(cmp.ok, true, 'an unchanged input must not be a regression');
  assert.deepEqual(cmp.regressions, []);
  assert.deepEqual(cmp.improvements, []);
  assert.equal(cmp.unchanged, 2);

  // and a proof lost in EITHER of them is still caught
  const broken = compareVerdicts(baseline, [
    v1,
    { ...v2, results: [{ property: 'p', transition: 'T.B', status: 'DISPROVED' }] },
  ]);
  assert.equal(broken.ok, false);
  assert.equal(broken.regressions[0].kind, 'proof-lost');
});
