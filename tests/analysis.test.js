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

test('analyzeAll aggregates all three families', () => {
  const g = buildGraph(parseDaml(example('Iou.daml')));
  const res = analyzeAll(g);
  assert.ok(Array.isArray(res.authorization));
  assert.ok(Array.isArray(res.visibility));
  assert.ok(Array.isArray(res.informationFlow));
  assert.equal(res.all.length, res.authorization.length + res.visibility.length + res.informationFlow.length);
  // every finding carries a category, severity, and message
  for (const f of res.all) {
    assert.ok(['authorization', 'visibility', 'information-flow'].includes(f.category));
    assert.ok(['info', 'warning', 'error'].includes(f.severity));
    assert.ok(typeof f.message === 'string' && f.message.length > 0);
  }
});
