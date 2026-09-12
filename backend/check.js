#!/usr/bin/env node
// backend/check.js
//
// The CI GATE. Build the access graph for a source tree or a DAR, compare it
// against a committed baseline, and exit nonzero when the change widens the
// access structure or introduces a finding nobody has accepted.
//
//   # accept the current state (commit the result)
//   node backend/check.js daml/ --baseline access-baseline.json --update
//
//   # in CI
//   node backend/check.js daml/ --baseline access-baseline.json
//
//   # compare two graphs directly, no baseline involved
//   node backend/check.js --diff before.json after.json
//
// Exit codes are meant for a pipeline:
//   0  no new findings, no widening
//   1  gate failed (new findings, or the access structure widened)
//   2  usage or input error
//
// Why a gate rather than a report: a real repository starts with dozens of
// legitimate informational findings, so "fail if any findings" is useless.
// What a reviewer wants to know is whether THIS change added something. That
// requires a committed baseline and a diff that knows which direction a change
// points in (see src/diff.js).

import { readFileSync, writeFileSync, existsSync, readdirSync, statSync } from 'node:fs';
import { join } from 'node:path';

import { parseProject } from '../src/project.js';
import { buildGraph } from '../src/graph.js';
import { analyzeAll } from '../src/analysis.js';
import { diffGraphs, diffFindings } from '../src/diff.js';
import { createBaseline, compareToBaseline } from '../src/baseline.js';
import { readDar } from './dalf.js';

const USAGE = `Usage:
  node backend/check.js <dir|file.dar> --baseline FILE [options]
  node backend/check.js --diff BEFORE.json AFTER.json

Options:
  --baseline FILE     the committed baseline to compare against
  --update            write the current state to the baseline and exit 0
  --fail-on WHAT      widening (default) | findings | any | never
  --suppress CODES    comma-separated finding codes to filter out
  --min-severity S    info | warning | error (default: info)
  --no-tests          skip test sources
  --no-dars           do not decode DARs found under the roots
  --json              emit the full report as JSON on stdout
  -h, --help

Exit codes: 0 clean, 1 gate failed, 2 usage/input error.`;

function parseArgs(argv) {
  const args = {
    target: null,
    baseline: null,
    update: false,
    failOn: 'widening',
    suppress: [],
    minSeverity: 'info',
    noTests: false,
    autoDars: true,
    json: false,
    diff: null,
    help: false,
  };
  const positional = [];
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--baseline') args.baseline = argv[++i];
    else if (a === '--update') args.update = true;
    else if (a === '--fail-on') args.failOn = argv[++i];
    else if (a === '--suppress') args.suppress = (argv[++i] || '').split(',').filter(Boolean);
    else if (a === '--min-severity') args.minSeverity = argv[++i];
    else if (a === '--no-tests') args.noTests = true;
    else if (a === '--no-dars') args.autoDars = false;
    else if (a === '--json') args.json = true;
    else if (a === '--diff') args.diff = [argv[++i], argv[++i]];
    else if (a === '-h' || a === '--help') args.help = true;
    else positional.push(a);
  }
  args.target = positional[0] || null;
  return args;
}

function collect(dir, ext, excludes, out = []) {
  for (const entry of readdirSync(dir)) {
    if (entry === '.git' || entry === 'node_modules' || entry === '.daml') continue;
    const p = join(dir, entry);
    let st;
    try {
      st = statSync(p);
    } catch (_) {
      continue;
    }
    if (st.isDirectory()) collect(p, ext, excludes, out);
    else if (entry.endsWith(ext) && !excludes.some((x) => p.includes(x))) out.push(p);
  }
  return out;
}

/** Build graph + analysis for a directory of sources or a single DAR. */
function buildTarget(target, args) {
  if (target.endsWith('.dar')) {
    const pkg = readDar(target);
    const graph = buildGraph(pkg, { source: 'daml-lf', module: pkg.module });
    graph.meta.package = pkg.name;
    return { graph, diagnostics: pkg.diagnostics };
  }

  const excludes = args.noTests ? ['/test/', '/tests/', 'Test'] : [];
  const files = collect(target, '.daml', excludes).map((p) => ({
    path: p,
    source: readFileSync(p, 'utf8'),
  }));
  if (files.length === 0) throw new Error(`no .daml files found under ${target}`);

  const externalPackages = [];
  if (args.autoDars) {
    for (const dp of collect(target, '.dar', [])) {
      try {
        externalPackages.push(readDar(dp));
      } catch (_) {
        /* reported by extract-project; not fatal for the gate */
      }
    }
  }

  const project = parseProject(files, { externalPackages });
  return { graph: buildGraph(project, { source: 'project-source' }), diagnostics: project.diagnostics };
}

function loadGraph(path) {
  const data = JSON.parse(readFileSync(path, 'utf8'));
  if (!Array.isArray(data.nodes) || !Array.isArray(data.edges)) {
    throw new Error(`${path} is not a normalized graph (missing nodes/edges)`);
  }
  return data;
}

function printChanges(changes, stream) {
  const order = { widening: 0, narrowing: 1, neutral: 2 };
  for (const c of [...changes].sort((a, b) => order[a.direction] - order[b.direction])) {
    const mark = c.direction === 'widening' ? 'WIDENS ' : c.direction === 'narrowing' ? 'narrows' : '       ';
    stream.write(`  ${mark}  ${c.message}\n`);
  }
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.help) {
    process.stdout.write(`${USAGE}\n`);
    process.exit(0);
  }

  // ------------------------------------------------------ plain graph diff
  if (args.diff) {
    const [beforePath, afterPath] = args.diff;
    if (!beforePath || !afterPath) {
      process.stderr.write('error: --diff needs two graph JSON files\n');
      process.exit(2);
    }
    const before = loadGraph(beforePath);
    const after = loadGraph(afterPath);
    const graphDiff = diffGraphs(before, after);
    const findingDiff = diffFindings(
      (before.analysis && before.analysis.all) || [],
      (after.analysis && after.analysis.all) || []
    );

    if (args.json) {
      process.stdout.write(`${JSON.stringify({ graphDiff, findingDiff }, null, 2)}\n`);
    } else {
      process.stdout.write(
        `access structure: ${graphDiff.summary.total} change(s) - ` +
          `${graphDiff.summary.byDirection.widening} widening, ` +
          `${graphDiff.summary.byDirection.narrowing} narrowing, ` +
          `${graphDiff.summary.byDirection.neutral} neutral\n`
      );
      printChanges(graphDiff.changes, process.stdout);
      if (findingDiff.added.length) {
        process.stdout.write(`\nnew findings (${findingDiff.added.length}):\n`);
        for (const f of findingDiff.added) process.stdout.write(`  [${f.severity}] ${f.message}\n`);
      }
    }
    const failed = shouldFail(args.failOn, graphDiff.summary.byDirection.widening, findingDiff.added.length);
    process.exit(failed ? 1 : 0);
  }

  // ----------------------------------------------------------- baseline gate
  if (!args.target) {
    process.stdout.write(`${USAGE}\n`);
    process.exit(2);
  }
  if (!args.baseline) {
    process.stderr.write('error: --baseline FILE is required (or use --diff)\n');
    process.exit(2);
  }
  if (!existsSync(args.target)) {
    process.stderr.write(`error: no such path: ${args.target}\n`);
    process.exit(2);
  }

  const { graph } = buildTarget(args.target, args);
  const analysis = analyzeAll(graph, {
    suppress: args.suppress,
    minSeverity: args.minSeverity,
  });

  if (args.update) {
    const baseline = createBaseline(graph, analysis, { note: `from ${args.target}` });
    writeFileSync(args.baseline, `${JSON.stringify(baseline, null, 2)}\n`);
    process.stderr.write(
      `wrote ${args.baseline}: ${baseline.counts.nodes} nodes, ${baseline.counts.edges} edges, ` +
        `${baseline.findings.length} accepted finding(s)\n`
    );
    process.exit(0);
  }

  if (!existsSync(args.baseline)) {
    process.stderr.write(
      `error: baseline ${args.baseline} does not exist.\n` +
        `Create it with:  node backend/check.js ${args.target} --baseline ${args.baseline} --update\n`
    );
    process.exit(2);
  }

  const baseline = JSON.parse(readFileSync(args.baseline, 'utf8'));
  const result = compareToBaseline(baseline, graph, analysis);

  if (args.json) {
    process.stdout.write(`${JSON.stringify(result, null, 2)}\n`);
  } else {
    const w = result.graphDiff.summary.byDirection;
    process.stdout.write(
      `access structure vs baseline: ${result.graphDiff.summary.total} change(s) - ` +
        `${w.widening} widening, ${w.narrowing} narrowing, ${w.neutral} neutral\n`
    );
    if (result.widening.length) {
      process.stdout.write('\nchanges that WIDEN the access structure:\n');
      printChanges(result.widening, process.stdout);
    }
    if (result.newFindings.length) {
      process.stdout.write(`\nfindings not in the baseline (${result.newFindings.length}):\n`);
      for (const f of result.newFindings) {
        process.stdout.write(`  [${f.severity}] ${f.code}: ${f.message}\n`);
      }
    }
    if (result.fixedFindings.length) {
      process.stdout.write(
        `\n${result.fixedFindings.length} baselined finding(s) no longer occur - ` +
          `rerun with --update to shrink the baseline.\n`
      );
    }
    if (result.ok) process.stdout.write('\nOK: no new findings and no widening of the access structure.\n');
  }

  process.exit(shouldFail(args.failOn, result.widening.length, result.newFindings.length) ? 1 : 0);
}

function shouldFail(failOn, wideningCount, newFindingCount) {
  switch (failOn) {
    case 'never':
      return false;
    case 'findings':
      return newFindingCount > 0;
    case 'any':
      return wideningCount > 0 || newFindingCount > 0;
    case 'widening':
    default:
      return wideningCount > 0;
  }
}

try {
  main();
} catch (err) {
  process.stderr.write(`error: ${err.message}\n`);
  process.exit(2);
}
