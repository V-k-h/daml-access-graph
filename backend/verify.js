#!/usr/bin/env node
// backend/verify.js
//
// Prove properties of a compiled Daml package with an SMT solver.
//
//   node backend/verify.js path/to/package.dar [options]
//
//   --property NAME    amount-conservation | division-safety (default: all)
//   --template NAME    restrict to one template
//   --choice NAME      restrict to one choice
//   --solver BIN       solver binary (default: cvc5; z3 also works)
//   --keep DIR         keep the generated .smt2 files here
//   --json             machine-readable report on stdout
//
// The pipeline, and what each stage does to the trust story:
//
//   DAR --readDarRaw--> LF protobuf --lfir--> guarded transitions --smt--> query --cvc5--> verdict
//
// The model is DERIVED from the compiled package, not written by hand, so the
// usual "does the model match the code?" gap is closed for the translated
// fragment - and the fragment's edges are machine-reported, never elided.
//
// Verdict vocabulary, chosen so that silence cannot be mistaken for safety:
//
//   PROVED           unsat: no counterexample exists in the model
//   PROVED-PARTIAL   unsat, but only some of the property's obligations
//                    were inside the fragment; the rest are UNKNOWN, and
//                    the coverage split is printed
//   DISPROVED        sat: a concrete counterexample, printed
//   NOT-MODELLABLE   the transition or property leaves the translated fragment;
//                    the reason is printed
//   NOT-APPLICABLE   the property does not apply (nonconsuming choice, no
//                    divisions, ...)
//   SOLVER-UNKNOWN   the solver gave up
//
// What a PROVED here does NOT mean, stated where it cannot be missed:
//   * Numeric 10 is modelled as exact Real (see smt.js) - rounding-dependent
//     equalities are refused rather than proved wrongly.
//   * Guards that leave the fragment are dropped, which is sound for proving
//     (superset of reachable states) but each drop is listed in the report.
//   * The translator itself (lfir.js) is tested, not verified.

import { execFileSync } from 'node:child_process';
import { writeFileSync, mkdirSync, existsSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { readDarRaw } from './dalf.js';
import { extractTransitions } from './lfir.js';
import { PROPERTIES, buildQuery } from './smt.js';

function parseArgs(argv) {
  const args = {
    dar: null,
    properties: [],
    template: null,
    choice: null,
    solver: 'cvc5',
    keep: null,
    json: false,
    help: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--property') args.properties.push(argv[++i]);
    else if (a === '--template') args.template = argv[++i];
    else if (a === '--choice') args.choice = argv[++i];
    else if (a === '--solver') args.solver = argv[++i];
    else if (a === '--keep') args.keep = argv[++i];
    else if (a === '--json') args.json = true;
    else if (a === '-h' || a === '--help') args.help = true;
    else args.dar = a;
  }
  if (args.properties.length === 0) args.properties = Object.keys(PROPERTIES);
  return args;
}

const USAGE = `Usage: node backend/verify.js <package.dar> [options]

  --property NAME   ${Object.entries(PROPERTIES)
    .map(([k, v]) => `${k}: ${v.describe}`)
    .join('\n                    ')}
  --template NAME   restrict to one template
  --choice NAME     restrict to one choice
  --solver BIN      solver binary (default: cvc5)
  --keep DIR        keep generated .smt2 files
  --json            machine-readable report`;

/** Run one query through the solver. */
function solve(script, solver, keepPath) {
  const dir = keepPath || join(tmpdir(), 'daml-verify');
  mkdirSync(dir, { recursive: true });
  const file = join(dir, `q${Math.abs(hashCode(script))}.smt2`);
  writeFileSync(file, script);
  let out;
  try {
    out = execFileSync(solver, ['--lang', 'smt2', file], {
      encoding: 'utf8',
      timeout: 30_000,
    });
  } catch (e) {
    // solvers exit nonzero on some outputs; the stdout still carries the verdict
    out = `${e.stdout || ''}${e.stderr || ''}`;
    if (!/\b(sat|unsat|unknown)\b/.test(out)) {
      throw new Error(`solver failed: ${e.message.split('\n')[0]}`);
    }
  }
  const verdict = out.match(/^\s*(unsat|sat|unknown)\s*$/m);
  return {
    verdict: verdict ? verdict[1] : 'unknown',
    model: out.includes('(') ? extractModel(out) : null,
    file,
  };
}

/** Pull assignments out of a get-model response, best effort. */
function extractModel(out) {
  const rows = [];
  // value may itself be parenthesized, e.g. `(- 1.0)` - allow one nesting level
  const re = /\(define-fun\s+(\|[^|]+\||\S+)\s*\(\)\s*\S+\s+((?:\([^()]*\)|[^()])+)\)/g;
  let m;
  while ((m = re.exec(out))) rows.push(`${m[1].replace(/\|/g, '')} = ${m[2].trim()}`);
  return rows.length ? rows : null;
}

function hashCode(s) {
  let h = 0;
  for (let i = 0; i < s.length; i++) h = ((h << 5) - h + s.charCodeAt(i)) | 0;
  return h;
}

function main() {
  const args = parseArgs(process.argv.slice(2));
  if (args.help || !args.dar) {
    process.stdout.write(`${USAGE}\n`);
    process.exit(args.help ? 0 : 2);
  }

  const raw = readDarRaw(args.dar);
  let transitions = extractTransitions(raw);
  if (args.template) transitions = transitions.filter((t) => t.template === args.template);
  if (args.choice) transitions = transitions.filter((t) => t.choice === args.choice);

  const results = [];
  for (const propName of args.properties) {
    const prop = PROPERTIES[propName];
    if (!prop) {
      process.stderr.write(`error: unknown property ${propName}\n`);
      process.exit(2);
    }
    for (const t of transitions) {
      const label = `${t.template}.${t.choice}${t.via ? ` (via ${t.via})` : ''}`;
      const loc = t.location
        ? { location: `${t.location.module || t.module}:${t.location.startLine}-${t.location.endLine}` }
        : {};
      const inst = prop.fn(t);
      if (!inst.applicable) {
        // A refusal (the fragment or the abstraction cannot express the check)
        // is reported as NOT-MODELLABLE; NOT-APPLICABLE means the property
        // genuinely does not concern this transition.
        results.push({
          property: propName,
          transition: label,
          status: inst.notModellable ? 'NOT-MODELLABLE' : 'NOT-APPLICABLE',
          why: inst.why,
          ...loc,
        });
        continue;
      }
      let query;
      try {
        query = buildQuery(inst.guards, inst.goal);
      } catch (e) {
        results.push({ property: propName, transition: label, status: 'NOT-MODELLABLE', why: e.message, ...loc });
        continue;
      }
      let solved;
      try {
        solved = solve(query.script, args.solver, args.keep);
      } catch (e) {
        results.push({ property: propName, transition: label, status: 'SOLVER-ERROR', why: e.message, ...loc });
        continue;
      }
      const notes = [];
      if (inst.dropped && inst.dropped.length) {
        notes.push(`${inst.dropped.length} guard(s) dropped (untranslatable ensure/branches) - sound for PROVED, see report`);
      }
      // Parts of the body the walker could not translate are carried onto the
      // verdict: a PROVED here is over the RECOVERED effects, and this note is
      // what keeps that limitation from being invisible.
      if (t.unsupported && t.unsupported.length) {
        notes.push(
          `${t.unsupported.length} untranslated part(s) in the body (effects beyond the recovered creates may exist), e.g.: ${t.unsupported[0].why}`
        );
      }
      // A property checked over only SOME of its obligations (19 of 20
      // division denominators, say, one being untranslatable) must never print
      // as a bare PROVED: the unchecked ones are unknown, not safe.
      // PROVED-PARTIAL is a distinct status carrying the coverage split.
      // A counterexample naming an `elem$N` symbol is about an ARBITRARY list
      // element, not a known one: the fold's real elements may be constrained
      // by validation the translation cannot see. Sound for PROVED (an
      // unconstrained element is the universal statement); for DISPROVED it
      // means "unless every element is constrained elsewhere", so say so.
      const elems = t.symbolicElements || [];
      if (elems.length) {
        const roots = [...new Set(elems.map((e) => e.root))];
        notes.push(
          `${roots.length} symbolic list element(s) (${elems
            .slice(0, 3)
            .map((e) => `${e.root} for \`${e.param}\``)
            .join(', ')}${elems.length > 3 ? ', ...' : ''}): results hold for an ARBITRARY element`
        );
      }

      const cov = inst.coverage;
      const partial = !!(cov && cov.checked < cov.total);
      if (partial) {
        notes.push(
          `${cov.checked} of ${cov.total} obligation(s) checked; ` +
            `${cov.total - cov.checked} outside the fragment: ${cov.skipped.join('; ')}`
        );
      }

      const note = notes.length ? notes.join('; ') : null;
      if (solved.verdict === 'unsat') {
        results.push({
          property: propName, transition: label,
          status: partial ? 'PROVED-PARTIAL' : 'PROVED',
          ...(cov ? { coverage: cov } : {}),
          ...(note ? { note } : {}),
          ...loc,
          smt2: solved.file,
        });
      } else if (solved.verdict === 'sat') {
        results.push({
          property: propName, transition: label, status: 'DISPROVED',
          counterexample: solved.model,
          ...(note ? { note: `${note}; the counterexample may be excluded by a dropped guard` } : {}),
          ...loc,
          smt2: solved.file,
        });
      } else {
        results.push({ property: propName, transition: label, status: 'SOLVER-UNKNOWN', ...loc, smt2: solved.file });
      }
    }
  }

  if (args.json) {
    process.stdout.write(JSON.stringify({ dar: args.dar, package: raw.name, results }, null, 2) + '\n');
  } else {
    const counts = {};
    for (const r of results) counts[r.status] = (counts[r.status] || 0) + 1;
    process.stdout.write(
      `${raw.name} ${raw.version || ''} (LF 2.${raw.lfMinor}) - ${transitions.length} transition(s)\n` +
      `verdicts: ${Object.entries(counts).map(([k, v]) => `${k}=${v}`).join(' ')}\n\n`
    );
    const order = { DISPROVED: 0, PROVED: 1, 'PROVED-PARTIAL': 1.5, 'SOLVER-UNKNOWN': 2, 'SOLVER-ERROR': 3, 'NOT-MODELLABLE': 4, 'NOT-APPLICABLE': 5 };
    for (const r of [...results].sort((a, b) => order[a.status] - order[b.status])) {
      if (r.status === 'NOT-APPLICABLE') continue; // summarized above, noise below
      process.stdout.write(`[${r.status}] ${r.property} :: ${r.transition}\n`);
      if (r.location) process.stdout.write(`    at ${r.location}\n`);
      if (r.why) process.stdout.write(`    ${r.why}\n`);
      if (r.note) process.stdout.write(`    note: ${r.note}\n`);
      if (r.counterexample) for (const row of r.counterexample) process.stdout.write(`    ${row}\n`);
    }
    const na = results.filter((r) => r.status === 'NOT-APPLICABLE').length;
    if (na) process.stdout.write(`\n(${na} not-applicable transition/property pairs omitted; --json lists them)\n`);
  }

  process.exit(results.some((r) => r.status === 'DISPROVED') ? 1 : 0);
}

main();
