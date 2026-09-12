#!/usr/bin/env node
// backend/extract-project.js
//
// WHOLE-REPOSITORY source extraction:
//
//   a directory of .daml files  --[this tool]-->  normalized graph JSON
//                                    │
//                                    ├─ parseProject   (src/project.js)
//                                    ├─ expandCalls    (src/callgraph.js)
//                                    └─ buildGraph     (src/graph.js, shared)
//
// Unlike extract-dar.js this needs NO Daml SDK, which matters: it is the only
// route that works on a checkout you have not built. It is also the only mode
// that can resolve cross-module references, because those need every module in
// hand at once:
//
//   * `exercise cid Mod.SomeChoice` -> the template declaring SomeChoice
//   * `interface instance I for T`  -> I's real declaration in a sibling module
//   * helper functions that perform the actual create/exercise on behalf of a
//     thin choice body
//
// It is still the HEURISTIC frontend (see src/parser.js) - for a sound graph of
// a built package, use extract-dar.js. Usage:
//
//   node backend/extract-project.js <dir> [<dir> ...] [options]
//
//   --out FILE        write JSON here (default: stdout)
//   --analyze         include static analysis findings under `analysis`
//   --suppress CODES  comma-separated finding codes to filter out
//   --min-severity S  info | warning | error  (default info)
//   --exclude GLOBS   comma-separated path substrings to skip (default: none)
//   --no-tests        shorthand for --exclude /test/,/tests/,Test
//   --dar FILE        also decode this DAR so interfaces it declares resolve
//   --no-dars         do not auto-discover DARs under the roots
//   --stats           print a human-readable summary to stderr
//
// DARs found under the roots are decoded by default. That is what makes an
// `interface instance Holding for X` resolve when Holding is declared in an
// imported package (e.g. the CIP-56 Splice DARs a token repo vendors): without
// it, X's exercisable surface is reported as unknown.
//
import { readdirSync, statSync, readFileSync, writeFileSync } from 'node:fs';
import { join, relative, sep } from 'node:path';

import { parseProject } from '../src/project.js';
import { readDar } from './dalf.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';

const TEST_EXCLUDES = [`${sep}test${sep}`, `${sep}tests${sep}`, 'Test'];

function parseArgs(argv) {
  const args = {
    dirs: [],
    out: null,
    analyze: false,
    suppress: [],
    minSeverity: 'info',
    exclude: [],
    dars: [],
    autoDars: true,
    stats: false,
    help: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--out') args.out = argv[++i];
    else if (a === '--analyze') args.analyze = true;
    else if (a === '--suppress') args.suppress = (argv[++i] || '').split(',').filter(Boolean);
    else if (a === '--min-severity') args.minSeverity = argv[++i];
    else if (a === '--exclude') args.exclude.push(...(argv[++i] || '').split(',').filter(Boolean));
    else if (a === '--no-tests') args.exclude.push(...TEST_EXCLUDES);
    else if (a === '--dar') args.dars.push(argv[++i]);
    else if (a === '--no-dars') args.autoDars = false;
    else if (a === '--stats') args.stats = true;
    else if (a === '-h' || a === '--help') args.help = true;
    else args.dirs.push(a);
  }
  return args;
}

const USAGE = `Usage: node backend/extract-project.js <dir> [<dir> ...] [options]

  --out FILE        write graph JSON here (default: stdout)
  --analyze         include static analysis findings under \`analysis\`
  --suppress CODES  comma-separated finding codes to filter out
  --min-severity S  info | warning | error (default: info)
  --exclude GLOBS   comma-separated path substrings to skip
  --no-tests        shorthand for --exclude /test/,/tests/,Test
  --dar FILE        also decode this DAR (repeatable)
  --no-dars         do not auto-discover DARs under the roots
  --stats           print a summary to stderr

Emits the same normalized graph schema as the browser parser and the Daml-LF
backend, with meta.source = "project-source". Load the file in the web UI via
"Load graph JSON".`;

/** Recursively collect files with a given extension, skipping build output. */
function collectFiles(dir, ext, excludes, out = []) {
  let entries;
  try {
    entries = readdirSync(dir);
  } catch (e) {
    process.stderr.write(`warning: cannot read ${dir}: ${e.message}\n`);
    return out;
  }
  for (const entry of entries) {
    if (entry === '.git' || entry === 'node_modules' || entry === '.daml') continue;
    const p = join(dir, entry);
    let st;
    try {
      st = statSync(p);
    } catch (_) {
      continue;
    }
    if (st.isDirectory()) {
      collectFiles(p, ext, excludes, out);
    } else if (entry.endsWith(ext)) {
      if (excludes.some((x) => p.includes(x))) continue;
      out.push(p);
    }
  }
  return out;
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.help || args.dirs.length === 0) {
    process.stdout.write(`${USAGE}\n`);
    process.exit(args.help ? 0 : 1);
  }

  const paths = [];
  for (const d of args.dirs) {
    let st;
    try {
      st = statSync(d);
    } catch (e) {
      process.stderr.write(`error: ${d}: ${e.message}\n`);
      process.exit(1);
    }
    if (st.isDirectory()) paths.push(...collectFiles(d, '.daml', args.exclude));
    else if (d.endsWith('.daml')) paths.push(d);
    else {
      process.stderr.write(`error: ${d} is neither a directory nor a .daml file\n`);
      process.exit(1);
    }
  }

  if (paths.length === 0) {
    process.stderr.write(
      `error: no .daml files found under [${args.dirs.join(', ')}]` +
        (args.exclude.length ? ` after excluding [${args.exclude.join(', ')}]` : '') +
        '\n'
    );
    process.exit(1);
  }

  const base = args.dirs.length === 1 ? args.dirs[0] : null;
  const files = paths.map((p) => ({
    path: base ? relative(base, p) || p : p,
    source: readFileSync(p, 'utf8'),
  }));

  // Decode bundled DARs so interfaces declared in imported packages resolve.
  const darPaths = [...args.dars];
  if (args.autoDars) {
    for (const d of args.dirs) {
      try {
        if (statSync(d).isDirectory()) darPaths.push(...collectFiles(d, '.dar', []));
      } catch (_) {
        /* already reported above */
      }
    }
  }
  const externalPackages = [];
  const darDiagnostics = [];
  for (const dp of [...new Set(darPaths)]) {
    try {
      const pkg = readDar(dp);
      externalPackages.push(pkg);
      darDiagnostics.push(...pkg.diagnostics);
    } catch (e) {
      darDiagnostics.push({
        severity: 'warning',
        code: 'dar-unreadable',
        message: `Could not decode ${dp}: ${e.message}`,
      });
    }
  }

  const project = parseProject(files, { externalPackages });
  project.diagnostics.unshift(...darDiagnostics);
  const graph = buildGraph(project, { source: 'project-source' });

  const payload = { ...graph };
  payload.meta = {
    ...graph.meta,
    roots: args.dirs,
    files: files.length,
    stats: project.stats,
  };

  let analysis = null;
  if (args.analyze) {
    analysis = analyzeAll(graph, {
      suppress: args.suppress,
      minSeverity: args.minSeverity,
    });
    payload.analysis = analysis;
  }
  payload.diagnostics = project.diagnostics;

  const json = JSON.stringify(payload, null, 2);
  if (args.out) {
    writeFileSync(args.out, `${json}\n`);
    process.stderr.write(`wrote ${args.out}\n`);
  } else {
    process.stdout.write(`${json}\n`);
  }

  if (args.stats) {
    const s = project.stats;
    const byKind = {};
    for (const e of graph.edges) byKind[e.kind] = (byKind[e.kind] || 0) + 1;
    const lines = [
      '',
      `files                ${s.files}  (modules: ${s.modules})`,
      `templates            ${s.templates}`,
      `interfaces           ${s.interfaces}` +
        (s.externalInterfaces
          ? ` (+${s.externalInterfaces} from ${s.externalPackages} bundled DAR(s))`
          : ''),
      `choices              ${s.choices}`,
      `helper functions     ${s.functions || 0}`,
      '',
      `ledger operations    ${s.opsTotal}`,
      `  named at call site ${s.opsResolvedInFile}`,
      `  resolved by projct ${s.opsResolvedByProject}`,
      `  via helper calls   ${s.opsViaHelpers || 0}`,
      `  ambiguous (kept null) ${s.opsAmbiguous}`,
      `  external / unknown ${s.opsExternal}`,
      '',
      `graph                ${graph.nodes.length} nodes, ${graph.edges.length} edges`,
      `edge kinds           ${Object.entries(byKind).map(([k, v]) => `${k}=${v}`).join(' ')}`,
      `diagnostics          ${project.diagnostics.length}`,
    ];
    if (analysis) {
      lines.push(
        `findings             ${analysis.summary.total}` +
          (analysis.summary.total !== analysis.summary.totalBeforeFilter
            ? ` (of ${analysis.summary.totalBeforeFilter} before filtering)`
            : ''),
        `  by severity        ${Object.entries(analysis.summary.bySeverity)
          .filter(([, v]) => v)
          .map(([k, v]) => `${k}=${v}`)
          .join(' ') || 'none'}`,
        `  by code            ${Object.entries(analysis.summary.byCode)
          .sort((a, b) => b[1] - a[1])
          .map(([k, v]) => `${k}=${v}`)
          .join(' ') || 'none'}`
      );
      const sup = Object.entries(analysis.summary.suppressed);
      if (sup.length) {
        lines.push(`  SUPPRESSED         ${sup.map(([k, v]) => `${k}=${v}`).join(' ')}`);
      }
    }
    process.stderr.write(`${lines.join('\n')}\n`);
  }
}

main();
