// tests/analysis.test.js
//
//   node --test

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

import { parseDaml } from '../src/parser.js';
import { buildGraph } from '../src/graph.js';
import { parseLfPretty } from '../backend/lf-parser.js';
import {
  analyzeAll,
  analyzeAuthorization,
  analyzeVisibility,
  analyzeInformationFlow,
  analyzeKeys,
  analyzeInterfaces,
} from '../src/analysis.js';

const here = dirname(fileURLToPath(import.meta.url));
const example = (n) => readFileSync(join(here, '..', 'examples', n), 'utf8');
const lf = readFileSync(join(here, 'fixtures', 'Asset.lf.txt'), 'utf8');

const codes = (findings) => new Set(findings.map((f) => f.code));

test('authorization: no-controller flagged', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    do return ()
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(codes(analyzeAuthorization(g)).has('no-controller'));
});

test('authorization: non-signatory consuming choice flagged', () => {
  // owner controls a consuming choice but only issuer is signatory
  const src = `module A where
template T with issuer : Party, owner : Party where
  signatory issuer
  observer owner
  choice Grab : ()
    controller owner
    do return ()
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(codes(analyzeAuthorization(g)).has('nonsignatory-consuming'));
});

test('authorization: cross-template create authority gap flagged (LF graph)', () => {
  // TransferProposal.Accept (acting: from,to) creates Asset (signed by issuer,owner)
  const g = buildGraph(parseLfPretty(lf), { source: 'daml-lf' });
  const auth = analyzeAuthorization(g);
  assert.ok(
    auth.some((f) => f.code === 'create-authority-gap' && /creates Asset/.test(f.message)),
    'expected an authority-gap finding for Accept creating Asset'
  );
});

test('visibility: no-observers flagged', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do return ()
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(codes(analyzeVisibility(g)).has('no-observers'));
});

test('information-flow: cross-party-flow flagged on Transfer->Asset (LF)', () => {
  const g = buildGraph(parseLfPretty(lf), { source: 'daml-lf' });
  const flow = analyzeInformationFlow(g);
  assert.ok(flow.some((f) => f.code === 'cross-party-flow'));
});

test('information-flow: cycle detected', () => {
  // Ping creates Pong, Pong creates Ping
  const src = `module A where
template Ping with p : Party where
  signatory p
  choice ToPong : ()
    controller p
    do
      create Pong with p = p
      return ()
template Pong with p : Party where
  signatory p
  choice ToPing : ()
    controller p
    do
      create Ping with p = p
      return ()
`;
  const g = buildGraph(parseDaml(src));
  const flow = analyzeInformationFlow(g);
  assert.ok(flow.some((f) => f.code === 'lifecycle-cycle'));
});

test('analyzeAll aggregates every family and carries a summary', () => {
  const g = buildGraph(parseDaml(example('Iou.daml')));
  const res = analyzeAll(g);
  for (const k of ['authorization', 'visibility', 'informationFlow', 'keys', 'interfaces']) {
    assert.ok(Array.isArray(res[k]), `${k} should be an array`);
  }
  assert.equal(
    res.all.length,
    res.authorization.length + res.visibility.length + res.informationFlow.length +
      res.keys.length + res.interfaces.length
  );
  for (const f of res.all) {
    assert.ok(
      ['authorization', 'visibility', 'information-flow', 'keys', 'interfaces'].includes(f.category)
    );
    assert.ok(['info', 'warning', 'error'].includes(f.severity));
    assert.ok(typeof f.message === 'string' && f.message.length > 0);
  }
  // summary counts match the kept findings
  assert.equal(res.summary.total, res.all.length);
  assert.equal(
    Object.values(res.summary.byCode).reduce((a, b) => a + b, 0),
    res.all.length
  );
});

test('a choice-argument controller is NOT reported as a missing stakeholder', () => {
  // `actor` is a choice ARGUMENT, not a template field. Daml makes it an
  // observer of the exercise; expecting it in `signatory`/`observer` is wrong,
  // and flagging it swamped real findings on factory-style templates.
  const src = `module A where
template Factory
  with
    admin : Party
  where
    signatory admin
    observer admin

    choice Act : ()
      with actor : Party
      controller actor
      do return ()
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(!codes(analyzeVisibility(g)).has('controller-not-stakeholder'));
});

test('`this.field` controller is not reported as a missing stakeholder', () => {
  const src = `module A where
template T
  with
    admin : Party
  where
    signatory admin
    observer admin

    choice C : ()
      controller this.admin
      do return ()
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(!codes(analyzeVisibility(g)).has('controller-not-stakeholder'));
});

test('a real non-stakeholder party field IS still reported', () => {
  const src = `module A where
template T
  with
    admin : Party
    auditor : Party
  where
    signatory admin

    nonconsuming choice Peek : ()
      controller auditor
      do return ()
`;
  const g = buildGraph(parseDaml(src));
  const f = analyzeVisibility(g).find((x) => x.code === 'controller-not-stakeholder');
  assert.ok(f, 'auditor is a declared party field and not a stakeholder');
  assert.match(f.message, /auditor/);
});

test('keys: maintainer that is not a signatory is flagged', () => {
  const src = `module A where
template M
  with
    admin : Party
    other : Party
  where
    signatory admin
    key (other, "x") : (Party, Text)
    maintainer key._1
`;
  const g = buildGraph(parseDaml(src));
  const f = analyzeKeys(g).find((x) => x.code === 'maintainer-not-signatory');
  assert.ok(f);
  assert.match(f.message, /other/);
});

test('keys: a maintainer that IS a signatory produces no finding', () => {
  const src = `module A where
template M
  with
    admin : Party
  where
    signatory admin
    key (admin, "x") : (Party, Text)
    maintainer key._1
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(!codes(analyzeKeys(g)).has('maintainer-not-signatory'));
});

test('keys: lookupAllByKey reads are surfaced as non-unique-key reads', () => {
  const src = `module A where
template T with p : Party where
  signatory p
  choice C : ()
    controller p
    do
      rows <- lookupAllByKey @Other (p, "x")
      return ()
`;
  const g = buildGraph(parseDaml(src));
  const f = analyzeKeys(g).find((x) => x.code === 'non-unique-key-read');
  assert.ok(f);
  assert.match(f.message, /Other/);
});

test('interfaces: an external interface under-reports the exercisable surface', () => {
  const src = `module A where
template Tok with admin : Party where
  signatory admin

  interface instance Holding for Tok where
    view = HoldingView with owner = admin
`;
  const g = buildGraph(parseDaml(src));
  const f = analyzeInterfaces(g).find((x) => x.code === 'external-interface-surface');
  assert.ok(f);
  assert.equal(f.severity, 'warning');
  assert.match(f.message, /UNDER-reported/);
});

test('analyzeAll suppression is explicit and reported, never silent', () => {
  const g = buildGraph(parseDaml(example('Iou.daml')));
  const before = analyzeAll(g);
  const code = Object.keys(before.summary.byCode)[0];
  assert.ok(code, 'the Iou example should produce at least one finding');

  const after = analyzeAll(g, { suppress: [code] });
  assert.ok(!after.all.some((f) => f.code === code));
  assert.equal(after.summary.suppressed[code], before.summary.byCode[code]);
  assert.equal(after.summary.totalBeforeFilter, before.summary.total);
});

test('analyzeAll minSeverity filters below the threshold', () => {
  const g = buildGraph(parseDaml(example('Iou.daml')));
  const res = analyzeAll(g, { minSeverity: 'warning' });
  assert.equal(res.summary.bySeverity.info, 0);
  for (const f of res.all) assert.notEqual(f.severity, 'info');
});

test('interfaces: a view-projected controller resolves to the implementing field', () => {
  const src = `module A where

interface Utxo where
  viewtype UtxoView

  choice Split : ()
    controller (view this).admin
    do return ()

template Tok
  with
    admin : Party
    owner : Party
  where
    signatory admin
    observer owner

    interface instance Utxo for Tok where
      view = UtxoView with admin
`;
  const g = buildGraph(parseDaml(src));
  // the graph carries the resolution as an edge
  const vc = g.edges.find((e) => e.kind === 'view-controller');
  assert.ok(vc, 'a view-controller edge should be emitted');
  assert.equal(vc.source, 'choice:Utxo.Split');
  assert.equal(vc.target, 'party:Tok.admin');

  const f = analyzeInterfaces(g).find((x) => x.code === 'interface-choice-exercisable');
  assert.ok(f);
  assert.match(f.message, /controlled on Tok by \[Tok\.admin\]/);
  assert.match(f.message, /resolved through the view/);
  // admin IS a signatory, so no stakeholder warning
  assert.ok(!codes(analyzeInterfaces(g)).has('interface-controller-not-stakeholder'));
});

test('interfaces: a resolved controller that is not a stakeholder is flagged', () => {
  // `custodian` supplies the interface view's admin but is neither signatory
  // nor observer of Tok, so a consuming interface choice can archive Tok
  // contracts through a path Tok's own declaration never shows.
  const src = `module A where

interface Utxo where
  viewtype UtxoView

  choice Split : ()
    controller (view this).admin
    do return ()

template Tok
  with
    issuer : Party
    custodian : Party
  where
    signatory issuer

    interface instance Utxo for Tok where
      view = UtxoView with admin = custodian
`;
  const g = buildGraph(parseDaml(src));
  const f = analyzeInterfaces(g).find((x) => x.code === 'interface-controller-not-stakeholder');
  assert.ok(f, 'expected a non-stakeholder interface controller finding');
  assert.equal(f.severity, 'warning', 'a consuming choice makes this a warning');
  assert.match(f.message, /Tok\.custodian/);
  assert.match(f.message, /CONSUMING/);
});

test('interfaces: an unbound view projection says so instead of guessing', () => {
  const src = `module A where

interface Utxo where
  viewtype UtxoView

  choice Split : ()
    controller (view this).admin
    do return ()

template Tok
  with
    issuer : Party
  where
    signatory issuer

    interface instance Utxo for Tok where
      view = UtxoView with
        holding = HoldingView with
          owner = issuer
`;
  const g = buildGraph(parseDaml(src));
  assert.ok(!g.edges.some((e) => e.kind === 'view-controller'));
  const f = analyzeInterfaces(g).find((x) => x.code === 'interface-choice-exercisable');
  assert.match(f.message, /not derivable here/);
});
