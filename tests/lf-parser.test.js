// tests/lf-parser.test.js
//
// Exercises the Daml-LF text extraction backend against a fixture that mirrors
// `daml damlc inspect` output (Daml-LF 2.x style). Verifies the backend
// produces the same structural model shape as the browser parser, and — unlike
// the browser parser — recovers operation targets SOUNDLY from `@Mod:Tpl`.
//
//   node --test

import test from 'node:test';
import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

import { parseLfPretty } from '../backend/lf-parser.js';
import { buildGraph } from '../src/graph.js';
import { extract } from '../backend/extract-dar.js';

const here = dirname(fileURLToPath(import.meta.url));
const lf = readFileSync(join(here, 'fixtures', 'Asset.lf.txt'), 'utf8');

function tpl(model, name) {
  const t = model.templates.find((x) => x.name === name);
  assert.ok(t, `template ${name} parsed`);
  return t;
}
function choice(t, name) {
  const c = t.choices.find((x) => x.name === name);
  assert.ok(c, `choice ${name} parsed`);
  return c;
}

test('LF: recovers modules and templates', () => {
  const m = parseLfPretty(lf);
  assert.deepEqual(m.modules, ['Asset', 'Transfer']);
  assert.deepEqual(m.templates.map((t) => t.name).sort(), ['Asset', 'TransferProposal']);
});

test('LF: party fields, signatories, observers from projections', () => {
  const asset = tpl(parseLfPretty(lf), 'Asset');
  assert.deepEqual(asset.signatories, ['issuer']);
  assert.deepEqual(asset.observers, ['owner']);
  assert.ok(asset.partyFields.includes('issuer'));
  assert.ok(asset.partyFields.includes('owner'));
  // amount is Numeric, not a party
  assert.ok(!asset.partyFields.includes('amount'));
});

test('LF: consuming vs nonconsuming + controllers', () => {
  const asset = tpl(parseLfPretty(lf), 'Asset');
  const give = choice(asset, 'Give');
  assert.equal(give.consuming, true);
  assert.deepEqual(give.controllers, ['owner']);

  const peek = choice(asset, 'Peek');
  assert.equal(peek.consuming, false);
  assert.deepEqual(peek.controllers, ['issuer']);

  // the auto-generated Archive choice is present and consuming
  const archive = choice(asset, 'Archive');
  assert.equal(archive.consuming, true);
});

test('LF: operation targets recovered SOUNDLY from @Mod:Tpl', () => {
  const m = parseLfPretty(lf);
  const give = choice(tpl(m, 'Asset'), 'Give');
  const create = give.operations.find((o) => o.kind === 'create');
  assert.ok(create, 'create op found');
  assert.equal(create.target, 'Asset'); // sound, unlike the browser `create this`

  const accept = choice(tpl(m, 'TransferProposal'), 'Accept');
  const createAsset = accept.operations.find((o) => o.kind === 'create');
  assert.equal(createAsset.target, 'Asset');
  assert.ok(m.referencedTemplates.includes('Asset'));
});

test('LF: buildGraph emits normalized JSON with source=daml-lf', () => {
  const m = parseLfPretty(lf);
  const g = buildGraph(m, { source: 'daml-lf' });
  assert.equal(g.meta.source, 'daml-lf');

  const ids = new Set(g.nodes.map((n) => n.id));
  for (const e of g.edges) {
    assert.ok(ids.has(e.source), `edge source ${e.source} resolves`);
    assert.ok(ids.has(e.target), `edge target ${e.target} resolves`);
  }
  // cross-template create edge: TransferProposal.Accept -> Asset
  assert.ok(
    g.edges.some((e) => e.kind === 'create' && e.source === 'choice:TransferProposal.Accept' && e.target === 'tpl:Asset'),
    'create edge from Accept to Asset'
  );
});

test('LF: extract() from saved LF text yields the same graph', () => {
  const g = extract({ lfText: lf });
  assert.equal(g.meta.source, 'daml-lf');
  assert.ok(g.nodes.some((n) => n.kind === 'template' && n.label === 'Asset'));
});

test('LF: controller party field named `to` is not swallowed by the `to` update keyword', () => {
  // regression: a `{to}` projection must not be mistaken for the update body.
  const accept = choice(tpl(parseLfPretty(lf), 'TransferProposal'), 'Accept');
  assert.deepEqual(accept.controllers, ['to']);
});

test('LF: empty / unrecognized input is flagged honestly', () => {
  const m = parseLfPretty('some text with no lf structure');
  assert.ok(m.diagnostics.some((d) => d.code === 'lf-no-modules'));
});
