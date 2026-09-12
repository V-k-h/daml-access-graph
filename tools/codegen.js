#!/usr/bin/env node
// tools/codegen.js
//
// Generate `backend/lf2-schema.generated.js` from the vendored .proto files.
//
//   npm run codegen
//
// Every field number the DALF decoder uses comes from here, so none of them is
// hand-copied. That removes a bug class whose failure mode is silence rather
// than an error: `Expr.RecProj` and `Expr.RecUpd` are near-identical messages
// whose `field_interned_str` sit in slots 4 and 2, and reading one with the
// other's number throws nothing, it just yields no party names.
//
// `tests/codegen.test.js` regenerates in memory and fails if the committed
// output differs, so schema drift cannot land unnoticed.

import { readFileSync, writeFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import { dirname, join } from 'node:path';

import { parseProto, fieldNumbers } from './proto-parse.js';

const here = dirname(fileURLToPath(import.meta.url));
const root = join(here, '..');

/** The vendored schemas, in the order their names should win on collision. */
export const SOURCES = [
  { file: 'backend/proto/daml_lf.proto', label: 'daml_lf.proto (envelope)' },
  { file: 'backend/proto/daml_lf2.proto', label: 'daml_lf2.proto' },
];

export const PROVENANCE = {
  repo: 'github.com/digital-asset/daml',
  tag: 'v3.4.11',
  path: 'sdk/daml-lf/archive/src/protobuf/com/digitalasset/daml/lf/archive/',
  license: 'Apache-2.0',
};

/**
 * Parse every vendored proto and merge into one descriptor.
 * @returns {{messages: Map<string, Object>, enums: Map<string, Object>, simple: Map<string, string[]>}}
 */
export function buildDescriptor() {
  const messages = new Map();
  const enums = new Map();

  for (const src of SOURCES) {
    const schema = parseProto(readFileSync(join(root, src.file), 'utf8'));
    for (const [qn, m] of schema.messages) {
      if (messages.has(qn)) {
        throw new Error(`codegen: message ${qn} declared in more than one proto`);
      }
      messages.set(qn, m);
    }
    for (const [qn, e] of schema.enums) enums.set(qn, e);
  }

  // simple name -> every qualified name that shares it
  const simple = new Map();
  for (const [qn, m] of messages) {
    if (!simple.has(m.name)) simple.set(m.name, []);
    simple.get(m.name).push(qn);
  }

  return { messages, enums, simple };
}

/** Render the generated module source. */
export function render() {
  const { messages, enums, simple } = buildDescriptor();

  const lines = [];
  lines.push('// backend/lf2-schema.generated.js');
  lines.push('//');
  lines.push('// GENERATED FILE - DO NOT EDIT.');
  lines.push('// Regenerate with:  npm run codegen');
  lines.push('//');
  lines.push('// Source of truth: the vendored Daml-LF protobuf schemas.');
  lines.push(`//   repo:    ${PROVENANCE.repo}`);
  lines.push(`//   tag:     ${PROVENANCE.tag}`);
  lines.push(`//   path:    ${PROVENANCE.path}`);
  lines.push(`//   license: ${PROVENANCE.license}`);
  lines.push('//');
  lines.push('// See backend/proto/PROVENANCE.md for why these are generated rather than');
  lines.push('// transcribed, and tests/codegen.test.js for the drift check.');
  lines.push('');
  lines.push(`export const PROVENANCE = ${JSON.stringify(PROVENANCE, null, 2)};`);
  lines.push('');
  lines.push('/** Field numbers for every message, keyed by fully qualified name. */');
  lines.push('export const MESSAGES = {');
  for (const qn of [...messages.keys()].sort()) {
    const nums = fieldNumbers(messages.get(qn));
    const entries = Object.entries(nums)
      .sort((a, b) => a[1] - b[1])
      .map(([k, v]) => `${JSON.stringify(k)}: ${v}`);
    lines.push(`  ${JSON.stringify(qn)}: { ${entries.join(', ')} },`);
  }
  lines.push('};');
  lines.push('');
  lines.push('/** Enum values, keyed by fully qualified name. */');
  lines.push('export const ENUMS = {');
  for (const qn of [...enums.keys()].sort()) {
    const entries = Object.entries(enums.get(qn)).map(([k, v]) => `${JSON.stringify(k)}: ${v}`);
    lines.push(`  ${JSON.stringify(qn)}: { ${entries.join(', ')} },`);
  }
  lines.push('};');
  lines.push('');
  lines.push('// Convenience named exports. A simple name is exported only when it is');
  lines.push('// UNIQUE across the schemas; an ambiguous one is reachable through MESSAGES');
  lines.push('// alone, so a decoder can never silently pick the wrong nesting.');

  const ambiguous = [];
  for (const [name, qns] of [...simple.entries()].sort()) {
    if (qns.length > 1) {
      ambiguous.push(`${name} (${qns.join(', ')})`);
      continue;
    }
    lines.push(`export const ${name} = MESSAGES[${JSON.stringify(qns[0])}];`);
  }
  lines.push('');
  if (ambiguous.length) {
    lines.push('// Ambiguous simple names, available via MESSAGES only:');
    for (const a of ambiguous) lines.push(`//   ${a}`);
    lines.push('');
  }
  lines.push('/** Look a message up by qualified name, failing loudly if absent. */');
  lines.push('export function message(qualifiedName) {');
  lines.push('  const m = MESSAGES[qualifiedName];');
  lines.push('  if (!m) throw new Error(`lf2-schema: no such message: ${qualifiedName}`);');
  lines.push('  return m;');
  lines.push('}');
  lines.push('');

  return lines.join('\n');
}

function main() {
  const out = join(root, 'backend/lf2-schema.generated.js');
  const source = render();
  writeFileSync(out, source);
  const { messages, enums } = buildDescriptor();
  process.stderr.write(
    `wrote backend/lf2-schema.generated.js: ${messages.size} messages, ${enums.size} enums\n`
  );
}

if (import.meta.url === `file://${process.argv[1]}`) main();
