#!/usr/bin/env node
// backend/extract-dar.js
//
// Daml-LF extraction backend (production pipeline):
//
//   .daml  --daml build-->  DAR  --[this tool]-->  normalized graph JSON
//                                    │
//                                    ├─ damlc inspect <dar>   (Daml-LF text)
//                                    ├─ parseLfPretty         (backend/lf-parser.js)
//                                    └─ buildGraph            (src/graph.js, shared)
//
// The emitted JSON is the SAME normalized graph schema as the browser parser,
// with meta.source = "daml-lf". Requires the Daml SDK (`daml` / `damlc`) on
// PATH. Usage:
//
//   node backend/extract-dar.js path/to/foo.dar [--out graph.json] [--analyze]
//   node backend/extract-dar.js path/to/foo.dar --damlc   # legacy text-scraping path
//   node backend/extract-dar.js --lf-file dump.lf         # parse a saved LF dump
//
// The DEFAULT path now decodes the DAR's Daml-LF protobuf directly (see
// dalf.js), which needs no SDK and recovers interfaces, contract keys and
// `implements` relationships that the `damlc inspect` text form does not
// expose. `--damlc` keeps the old behaviour for comparison.
//
import { execFileSync } from 'node:child_process';
import { writeFileSync, readFileSync, existsSync } from 'node:fs';

import { parseLfPretty } from './lf-parser.js';
import { readDar } from './dalf.js';
import { readDarManifest } from './dar.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';

function parseArgs(argv) {
  const args = { _: [], out: null, lf: null, lfFile: null, analyze: false, damlc: false };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--out') args.out = argv[++i];
    else if (a === '--lf') args.lf = argv[++i];
    else if (a === '--lf-file') args.lfFile = argv[++i];
    else if (a === '--analyze') args.analyze = true;
    else if (a === '--damlc') args.damlc = true;
    else if (a === '-h' || a === '--help') args.help = true;
    else args._.push(a);
  }
  return args;
}

function which(cmd) {
  try {
    execFileSync('command', ['-v', cmd], { shell: '/bin/sh', stdio: 'ignore' });
    return true;
  } catch (_) {
    return false;
  }
}

function findDamlcInvoker() {
  // Prefer `damlc` directly; otherwise `daml damlc …`.
  if (which('damlc')) return { cmd: 'damlc', prefix: [] };
  if (which('daml')) return { cmd: 'daml', prefix: ['damlc'] };
  return null;
}

/**
 * Get the Daml-LF textual dump for a DAR via the SDK.
 * @returns {string}
 */
export function inspectDar(darPath) {
  const invoker = findDamlcInvoker();
  if (!invoker) {
    throw new ToolchainError(
      'The Daml SDK was not found on PATH (`daml` / `damlc`).\n' +
        'Install it from https://docs.daml.com/getting-started/installation.html\n' +
        'then build your project with `daml build` to produce a DAR.\n\n' +
        'To try the parser without the SDK, pass a saved dump:\n' +
        '  daml damlc inspect foo.dar > dump.lf\n' +
        '  node backend/extract-dar.js --lf-file dump.lf'
    );
  }
  return execFileSync(invoker.cmd, [...invoker.prefix, 'inspect', darPath], {
    encoding: 'utf8',
    maxBuffer: 256 * 1024 * 1024,
  });
}

class ToolchainError extends Error {}

/**
 * Full pipeline: DAR (or saved LF) -> normalized graph JSON.
 * @param {{darPath?: string, lfText?: string}} input
 * @returns {import('../src/graph.js').Graph}
 */
export function extract({ darPath, lfText }) {
  let lf = lfText;
  let manifest = null;
  if (darPath) {
    manifest = readDarManifest(darPath);
    lf = inspectDar(darPath);
  }
  const parsed = parseLfPretty(lf || '');
  const graph = buildGraph(parsed, { source: 'daml-lf' });
  if (manifest && manifest.name) graph.meta.package = manifest.name;
  return graph;
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.help || (!args.lfFile && args._.length === 0)) {
    process.stdout.write(
      'Usage:\n' +
        '  node backend/extract-dar.js <foo.dar> [--out graph.json] [--analyze]\n' +
        '      Decodes the DAR protobuf directly. No Daml SDK required.\n' +
        '  node backend/extract-dar.js <foo.dar> --damlc [--lf dump.lf]\n' +
        '      Legacy path: scrape `damlc inspect` text (needs the SDK on PATH).\n' +
        '  node backend/extract-dar.js --lf-file dump.lf [--out graph.json]\n' +
        '      Parse a previously saved LF text dump.\n'
    );
    process.exit(args.help ? 0 : 1);
  }

  try {
    let graph;
    let diagnostics = [];
    if (args.lfFile) {
      if (!existsSync(args.lfFile)) throw new Error(`No such file: ${args.lfFile}`);
      const lfText = readFileSync(args.lfFile, 'utf8');
      graph = extract({ lfText });
    } else if (args.damlc) {
      // Legacy path: scrape `damlc inspect` text. Kept for comparison, and as
      // a fallback if a package will not decode.
      const darPath = args._[0];
      if (!existsSync(darPath)) throw new Error(`No such DAR: ${darPath}`);
      const lf = inspectDar(darPath);
      if (args.lf) writeFileSync(args.lf, lf);
      graph = extract({ lfText: lf });
      const manifest = readDarManifest(darPath);
      if (manifest.name) graph.meta.package = manifest.name;
    } else {
      // Default: decode the DAR's protobuf directly. No SDK needed, and it
      // sees interfaces, keys and `implements` that the text form does not.
      const darPath = args._[0];
      if (!existsSync(darPath)) throw new Error(`No such DAR: ${darPath}`);
      const pkg = readDar(darPath);
      diagnostics = pkg.diagnostics;
      graph = buildGraph(pkg, { source: 'daml-lf', module: pkg.module });
      graph.meta.package = pkg.name;
      graph.meta.packageVersion = pkg.version;
      graph.meta.packageId = pkg.packageId;
      graph.meta.lfVersion = pkg.lfMinor ? `2.${pkg.lfMinor}` : null;
      graph.meta.sdkVersion = pkg.sdkVersion;
      graph.meta.modules = pkg.modules;
      graph.meta.warnings = [
        ...graph.meta.warnings,
        ...diagnostics.filter((d) => d.severity !== 'info').map((d) => d.message),
      ];
    }

    const payload = args.analyze ? { ...graph, analysis: analyzeAll(graph) } : { ...graph };
    if (diagnostics.length) payload.diagnostics = diagnostics;
    const json = JSON.stringify(payload, null, 2);
    if (args.out) {
      writeFileSync(args.out, json);
      process.stderr.write(`Wrote ${graph.nodes.length} nodes, ${graph.edges.length} edges to ${args.out}\n`);
    } else {
      process.stdout.write(json + '\n');
    }
    // Surface warnings + finding counts to stderr so piped JSON stays clean.
    for (const w of graph.meta.warnings) process.stderr.write(`warning: ${w}\n`);
    if (args.analyze) {
      const { all } = payload.analysis;
      process.stderr.write(`analysis: ${all.length} findings (${all.filter((f) => f.severity === 'warning').length} warnings)\n`);
    }
  } catch (err) {
    if (err instanceof ToolchainError) {
      process.stderr.write('\n' + err.message + '\n');
      process.exit(2);
    }
    process.stderr.write(`error: ${err.message}\n`);
    process.exit(1);
  }
}

// Run only when invoked directly (not when imported by tests).
if (import.meta.url === `file://${process.argv[1]}`) {
  main();
}
