#!/usr/bin/env node
// backend/verify.js
//
// Prove properties of a compiled Daml package with an SMT solver.
//
//   node backend/verify.js path/to/package.dar [options]
//
//   --property NAME    amount-conservation | division-safety |
//                      non-negative-fields | create-authority (default: all)
//   --template NAME    restrict to one template
//   --choice NAME      restrict to one choice
//   --bound N          list length to unroll folds and archive loops to
//                      (default 3); see PROVED-BOUNDED below
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
//   PROVED-BOUNDED (lists up to length N)
//                    unsat, but only for lists of at most N elements. A
//                    transition whose arithmetic folds over a list (a merge
//                    summing its inputs) is instantiated at every list length
//                    0..N and one query is emitted per length; all of them
//                    came back unsat. This says NOTHING about a list of N+1
//                    elements - not "probably fine", nothing at all - which is
//                    why it is a status of its own and not a footnote on
//                    PROVED. Raise it with --bound.
//   PROVED-PARTIAL   unsat, but only some of the property's obligations
//                    were inside the fragment; the rest are UNKNOWN, and
//                    the coverage split is printed
//   DISPROVED        sat: a concrete counterexample, printed. For a bounded
//                    check the list length at which it was found is printed
//                    with it: the property fails already at that length. When
//                    the query used an UNINTERPRETED FUNCTION (see below) the
//                    verdict says so, because the counterexample may then be
//                    an artifact of the abstraction rather than a real bug.
//   NOT-MODELLABLE   the transition or property leaves the translated fragment;
//                    the reason is printed
//   NOT-APPLICABLE   the property does not apply (nonconsuming choice, no
//                    divisions, ...)
//   SOLVER-UNKNOWN   the solver gave up
//
// What a PROVED here does NOT mean, stated where it cannot be missed:
//   * Numeric 10 is modelled as exact Real (see smt.js) - rounding-dependent
//     equalities are refused rather than proved wrongly.
//   * Daml's `Int` (Int64) is modelled as the SMT `Int` sort, WITH its
//     integrality. This is the one modelling decision here that SHRINKS the
//     model class rather than enlarging it, so it needs its own justification
//     and it has exactly one: a Daml Int really is an integer, so no reachable
//     state is excluded. It is a faithful refinement, not an assumption about
//     the code - which is why it is the only place a constraint is added at
//     all, and why Int-ness is taken from the DECLARED LF type and from
//     nothing else (never a field's name, never how the code uses it, never a
//     literal that looks integral). Where the declared type cannot be read the
//     symbol stays `Real` and carries no integrality, which is the
//     conservative side: it can only cost a proof, never fabricate one.
//     The failure direction to keep in mind when reading a PROVED is a
//     `Decimal` field wrongly typed `Int`: that would be a FALSE constraint,
//     and a false constraint can make an unsat - and therefore a PROVED -
//     spurious. dalf.js answers `int` only from the Int64 builtin in a
//     `DefDataType` the archive actually carries.
//   * The two numeric sorts are never mixed silently. An Int-sorted term
//     reaching a Real position is either an explicit `to_real` coercion (the
//     translation of Daml's `intToDecimal`) or a SORT CONFLICT that refuses
//     the query with NOT-MODELLABLE. Daml permits no implicit Int/Decimal
//     mixing, so a conflict means the translation got something wrong, and
//     saying so is better than coercing a guess.
//   * Guards that leave the fragment are dropped, which is sound for proving
//     (superset of reachable states) but each drop is listed in the report.
//   * Opaque Text operations are modelled as UNINTERPRETED FUNCTIONS (see the
//     header of smt.js). That too enlarges the model class, so it is sound for
//     PROVED - but it makes a DISPROVED only a CANDIDATE: the solver may have
//     picked an interpretation the real function never takes. Every DISPROVED
//     over a query that declares such a symbol carries that caveat, naming the
//     symbols, and no verdict here ever hides it.
//   * A PROVED-BOUNDED is a statement about short lists only.
//   * The translator itself (lfir.js) is tested, not verified.
//   * PARTIES are UNINTERPRETED CONSTANTS of an uninterpreted sort
//     (create-authority). Two party references are equal in the model exactly
//     when the compiled create assigned one from the other; sharing a FIELD
//     NAME across two templates establishes nothing, which is the limitation
//     src/analysis.js reports rather than asserts. The consequences are
//     asymmetric and both are disclosed on the verdict: an unlinkable party
//     leaves its create UNCHECKED (never PROVED), and the acting authority is
//     an under-approximation, so a DISPROVED there may be an artifact of a
//     controller clause the translation could not read rather than a real
//     authorisation gap.

import { execFileSync } from 'node:child_process';
import { writeFileSync, mkdirSync, existsSync, readFileSync } from 'node:fs';
import { join } from 'node:path';
import { tmpdir } from 'node:os';

import { readDarRaw } from './dalf.js';
import { extractTransitions, DEFAULT_BOUND } from './lfir.js';
import { PROPERTIES, buildQuery } from './smt.js';
import {
  createVerdictBaseline,
  compareVerdicts,
  describeDiff,
} from '../src/verdict-baseline.js';

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
    bound: DEFAULT_BOUND,
    baseline: null,
    updateBaseline: false,
  };
  for (let i = 0; i < argv.length; i++) {
    const a = argv[i];
    if (a === '--property') args.properties.push(argv[++i]);
    else if (a === '--template') args.template = argv[++i];
    else if (a === '--choice') args.choice = argv[++i];
    else if (a === '--bound') args.bound = Number.parseInt(argv[++i], 10);
    else if (a === '--solver') args.solver = argv[++i];
    else if (a === '--keep') args.keep = argv[++i];
    else if (a === '--json') args.json = true;
    else if (a === '--baseline') args.baseline = argv[++i];
    else if (a === '--update-baseline') args.updateBaseline = true;
    else if (a === '-h' || a === '--help') args.help = true;
    else args.dar = a;
  }
  if (args.properties.length === 0) args.properties = Object.keys(PROPERTIES);
  if (!Number.isInteger(args.bound) || args.bound < 0) args.bound = DEFAULT_BOUND;
  return args;
}

const USAGE = `Usage: node backend/verify.js <package.dar> [options]

  --property NAME   ${Object.entries(PROPERTIES)
    .map(([k, v]) => `${k}: ${v.describe}`)
    .join('\n                    ')}
  --template NAME   restrict to one template
  --choice NAME     restrict to one choice
  --bound N         list length folds/archive loops are unrolled to (default ${DEFAULT_BOUND})
  --solver BIN      solver binary (default: cvc5)
  --keep DIR        keep generated .smt2 files
  --json            machine-readable report
  --baseline FILE   compare verdicts against a committed baseline and exit
                    nonzero on a regression (a lost proof or a new finding)
  --update-baseline write the current verdicts to --baseline and exit 0`;

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
  // The bound is fixed at extraction: unrolling a fold reduces its step
  // function inside the translation context, which does not outlive that call.
  let transitions = extractTransitions(raw, { bound: args.bound });
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
      // A BOUNDED property emits one query per list length: the transition's
      // arithmetic is a different term at each length, so there is no single
      // query to ask. All lengths unsat is the bounded verdict; the FIRST sat
      // is a counterexample AND the length at which the property already
      // fails, which is strictly more informative than "somewhere <= N".
      const instances = inst.instances || [{ k: null, guards: inst.guards, goal: inst.goal }];
      let solved = null;
      let failed = null;
      let buildError = null;
      let solverError = null;
      const files = [];
      // Uninterpreted symbols DECLARED IN THE QUERY that decided the verdict.
      // Taken from buildQuery rather than from the transition, so the caveat
      // attaches to the query actually solved: a transition may abstract a
      // symbol in a part of its body this property never looks at.
      let queryUfs = [];
      for (const instance of instances) {
        const at = instance.k === null ? '' : ` at list length ${instance.k}`;
        let query;
        try {
          query = buildQuery(instance.guards, instance.goal);
        } catch (e) {
          buildError = `${e.message}${at}`;
          break;
        }
        queryUfs = query.ufs || [];
        try {
          solved = solve(query.script, args.solver, args.keep);
        } catch (e) {
          solverError = `${e.message}${at}`;
          break;
        }
        files.push(solved.file);
        if (solved.verdict !== 'unsat') {
          failed = instance;
          break;
        }
      }
      if (buildError) {
        results.push({ property: propName, transition: label, status: 'NOT-MODELLABLE', why: buildError, ...loc });
        continue;
      }
      if (solverError) {
        results.push({ property: propName, transition: label, status: 'SOLVER-ERROR', why: solverError, ...loc });
        continue;
      }

      const notes = [];
      // Disclosures the PROPERTY itself wants on the verdict: which parts of
      // its statement it narrowed, and which of its inputs were
      // approximations. verify.js cannot derive these from the transition -
      // only the property knows what it did and did not claim.
      if (inst.notes && inst.notes.length) notes.push(...inst.notes);
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
      // The bounded check's own disclosure: which list, how far, and - the
      // point of the design - that the archived inputs are the SAME symbols
      // the fold produced rather than a second, unrelated family.
      if (inst.bounded) {
        notes.push(
          inst.boundedNote ||
            `bounded: lists instantiated up to length ${inst.bound} only`
        );
      }

      // The abstraction disclosure. It is a note on EVERY verdict that used a
      // UF, not only on DISPROVED, because a reader of a PROVED is entitled to
      // know which operations were replaced by unconstrained symbols - the
      // proof is over a larger model class than the code.
      if (queryUfs.length) {
        const why = new Map((t.uninterpreted || []).map((u) => [u.name, u.why]));
        const shown = queryUfs.slice(0, 3).map((n) => why.get(n) || n);
        notes.push(
          `${queryUfs.length} uninterpreted symbol(s) in the query: ${shown.join('; ')}` +
            `${queryUfs.length > 3 ? `; and ${queryUfs.length - 3} more` : ''}`
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
      if (!failed) {
        // Every instance came back unsat. A bounded run has proved the
        // property only for the lengths it enumerated, and the status says so
        // in words rather than in a footnote.
        const status = partial
          ? 'PROVED-PARTIAL'
          : inst.bounded
            ? `PROVED-BOUNDED (lists up to length ${inst.bound})`
            : 'PROVED';
        results.push({
          property: propName, transition: label,
          status,
          ...(inst.bounded ? { bound: inst.bound, listName: inst.listName, queries: instances.length } : {}),
          ...(cov ? { coverage: cov } : {}),
          ...(queryUfs.length ? { uninterpreted: queryUfs } : {}),
          ...(note ? { note } : {}),
          ...loc,
          smt2: files[files.length - 1],
        });
      } else if (solved.verdict === 'sat') {
        // The abstraction is asymmetric (smt.js): unsat proves, sat does not
        // refute. A counterexample drawn from a query with an uninterpreted
        // symbol may use an interpretation the real function never takes, so
        // it is a CANDIDATE finding and must never read as a confirmed one.
        const spurious = queryUfs.length
          ? `; this counterexample MAY BE AN ARTIFACT of the uninterpreted symbol(s) named ` +
            `above rather than a real behaviour of the code: the solver is free to give them ` +
            `any interpretation, including ones the real functions never take - check it ` +
            `against what those functions actually do before treating it as a finding`
          : '';
        const bounded = failed.k === null ? '' : `; the property already fails at list length ${failed.k}`;
        const disproofNote = note
          ? `${note}${bounded}; the counterexample may be excluded by a dropped guard${spurious}`
          : `${bounded.replace(/^; /, '')}${spurious}`.replace(/^; /, '');
        results.push({
          property: propName, transition: label, status: 'DISPROVED',
          ...(failed.k === null ? {} : { failedAtListLength: failed.k }),
          counterexample: solved.model,
          ...(queryUfs.length ? { uninterpreted: queryUfs } : {}),
          ...(disproofNote ? { note: disproofNote } : {}),
          ...loc,
          smt2: files[files.length - 1],
        });
      } else {
        results.push({
          property: propName, transition: label, status: 'SOLVER-UNKNOWN',
          ...(failed.k === null ? {} : { failedAtListLength: failed.k }),
          ...loc,
          smt2: files[files.length - 1],
        });
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
    const order = {
      DISPROVED: 0,
      PROVED: 1,
      'PROVED-BOUNDED': 1.2,
      'PROVED-PARTIAL': 1.5,
      'SOLVER-UNKNOWN': 2,
      'SOLVER-ERROR': 3,
      'NOT-MODELLABLE': 4,
      'NOT-APPLICABLE': 5,
    };
    // PROVED-BOUNDED carries its bound in the status text, so rank on the
    // part before the parenthesis.
    const rank = (status) => order[status.split(' (')[0]] ?? 9;
    for (const r of [...results].sort((a, b) => rank(a.status) - rank(b.status))) {
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

  // ------------------------------------------------------------- CI gate
  // A baseline turns "are there findings?" (useless: a real package has
  // correct DISPROVEDs from day one) into "did a proof stop holding, or did
  // a finding appear that nobody has triaged?".
  if (args.baseline) {
    const report = { package: raw.name || args.dar, dar: args.dar, results };
    if (args.updateBaseline) {
      const baseline = createVerdictBaseline([report], { note: `from ${args.dar}` });
      writeFileSync(args.baseline, `${JSON.stringify(baseline, null, 2)}\n`);
      process.stderr.write(
        `wrote ${args.baseline}: ${results.length} verdict(s) for ${report.package}\n`
      );
      process.exitCode = 0;
      return;
    }
    if (!existsSync(args.baseline)) {
      process.stderr.write(
        `error: baseline ${args.baseline} does not exist.\n` +
          `Create it with:  node backend/verify.js ${args.dar} --baseline ${args.baseline} --update-baseline\n`
      );
      process.exitCode = 2;
      return;
    }
    const baseline = JSON.parse(readFileSync(args.baseline, 'utf8'));
    const cmp = compareVerdicts(baseline, [report]);
    process.stdout.write(
      `\nbaseline: ${cmp.unchanged} unchanged, ${cmp.improvements.length} improvement(s), ` +
        `${cmp.regressions.length} regression(s)\n`
    );
    for (const d of cmp.regressions) process.stdout.write(`  REGRESSION ${describeDiff(d)}\n`);
    for (const d of cmp.improvements) process.stdout.write(`  improved   ${describeDiff(d)}\n`);
    if (cmp.improvements.length && cmp.ok) {
      process.stdout.write('\nRerun with --update-baseline to accept the improvements.\n');
    }
    process.exitCode = cmp.ok ? 0 : 1;
    return;
  }

  // `process.exitCode`, NOT `process.exit`: when stdout is a PIPE the write
  // above is asynchronous, and exiting immediately truncates it - a --json
  // report with a DISPROVED in it came out cut off at the pipe buffer, which
  // is 8 KB. Setting the code lets node drain stdout and then exit with it.
  process.exitCode = results.some((r) => r.status === 'DISPROVED') ? 1 : 0;
}

main();
