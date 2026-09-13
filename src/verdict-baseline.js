// src/verdict-baseline.js
//
// The committed record of which proofs a package is expected to yield, and
// the rule for deciding whether a change broke one.
//
// This is the verification counterpart to src/baseline.js (which does the same
// job for the access graph). The two answer different questions and are kept
// apart deliberately: that one asks "did the access structure widen?", this
// one asks "did we stop being able to prove something we could prove before?".
//
// WHY A VERDICT BASELINE AND NOT JUST "FAIL ON ANY DISPROVED":
// a real package starts with DISPROVED verdicts that are correct findings
// (mint and burn choices genuinely do not conserve). Failing on their presence
// would mean the gate is red from day one and gets switched off. What matters
// is MOVEMENT: a proof that used to hold and no longer does.
//
// THE ASYMMETRY THAT DEFINES THE RULE. Verdicts are not equally significant:
//
//   * Losing a proof (PROVED -> anything else) is a REGRESSION. Either the
//     code changed so the property stopped holding, or the translator got
//     worse and can no longer see why it holds. Both need a human.
//   * A NEW DISPROVED is a REGRESSION: a finding nobody has triaged.
//   * Gaining a proof, or a refusal becoming a verdict, is an IMPROVEMENT.
//     Never fail on those; report them so the baseline gets refreshed.
//
// A proof lost and a proof gained are therefore not symmetric, and the gate
// must not treat "the counts still add up" as "nothing happened".

/** Verdict statuses that assert the property holds, to whatever extent. */
const PROVING = new Set(['PROVED', 'PROVED-BOUNDED', 'PROVED-PARTIAL']);

export const VERDICT_BASELINE_VERSION = 1;

/**
 * Statuses carry a parenthesised parameter (`PROVED-BOUNDED (lists up to
 * length 3)`). The bound is a property of the RUN, not of the code, so the
 * family is what gets compared; the full status is kept for the report.
 */
export const statusFamily = (status) => String(status).split(' (')[0];

const isProving = (status) => PROVING.has(statusFamily(status));

/** Stable identity of one checked obligation. */
export const verdictKey = (r) => `${r.property}::${r.transition}`;

/**
 * Group a report list by the name the baseline is keyed on.
 *
 * WHY THIS IS NOT JUST `for (const report of reports)`: the API is plural
 * because there is one report per DAR, and two DARs can carry the SAME package
 * name - two versions of one package built into a directory the CI job scans.
 * Writing `packages[name] = entries` per report let the later DAR silently
 * erase the earlier one's obligations from the baseline; the very next
 * comparison of the SAME UNCHANGED input then reported the erased obligations
 * as `proof-disappeared` regressions. The gate went red on a tree nobody had
 * touched, and `--update-baseline` could not clear it, because the refresh
 * reproduced the same collapse. Found by the round-trip property in
 * tests/property.test.js, which generates colliding package names.
 *
 * Same-named reports are therefore MERGED, here and in compareVerdicts, so
 * both sides agree on what one package's obligation set is. A key present in
 * two of them keeps the last verdict seen, which is what the overwriting
 * version did for the keys it did not lose.
 *
 * @param {Array<{dar?: string, package?: string, results?: Array<Object>}>} reports
 * @returns {Map<string, Array<Object>>} package name -> its verdicts, deduped by obligation
 */
function groupByPackage(reports) {
  /** @type {Map<string, Map<string, Object>>} */
  const byName = new Map();
  for (const report of reports || []) {
    const name = report.package || report.dar;
    if (!byName.has(name)) byName.set(name, new Map());
    const into = byName.get(name);
    for (const r of report.results || []) into.set(verdictKey(r), r);
  }
  return new Map([...byName].map(([name, verdicts]) => [name, [...verdicts.values()]]));
}

/**
 * Build a baseline from a verify.js JSON report (or several, keyed by DAR).
 *
 * Only the fields the gate compares are stored. Counterexamples and notes are
 * deliberately omitted: they churn with unrelated improvements to wording and
 * would make every baseline refresh a large diff nobody reads.
 *
 * @param {Array<{dar: string, results: Array<Object>}>} reports
 */
export function createVerdictBaseline(reports, meta = {}) {
  const packages = {};
  for (const [name, results] of groupByPackage(reports)) {
    const entries = {};
    for (const r of results) entries[verdictKey(r)] = statusFamily(r.status);
    packages[name] = entries;
  }
  return {
    version: VERDICT_BASELINE_VERSION,
    note: meta.note || null,
    counts: Object.fromEntries(
      Object.entries(packages).map(([k, v]) => [k, Object.keys(v).length])
    ),
    packages,
  };
}

/**
 * Compare current reports against a baseline.
 *
 * @returns {{regressions: Array, improvements: Array, unchanged: number, ok: boolean}}
 */
export function compareVerdicts(baseline, reports) {
  if (!baseline || baseline.version !== VERDICT_BASELINE_VERSION) {
    throw new Error(
      `Unsupported verdict baseline version ${baseline && baseline.version}; ` +
        `expected ${VERDICT_BASELINE_VERSION}. Regenerate with --update-baseline.`
    );
  }

  const regressions = [];
  const improvements = [];
  let unchanged = 0;

  for (const [name, results] of groupByPackage(reports)) {
    const was = (baseline.packages || {})[name];
    if (!was) {
      improvements.push({
        package: name,
        kind: 'new-package',
        detail: `${results.length} verdict(s) not in the baseline`,
      });
      continue;
    }

    const seen = new Set();
    for (const r of results) {
      const key = verdictKey(r);
      seen.add(key);
      const before = was[key];
      const after = statusFamily(r.status);
      if (before === after) {
        unchanged++;
        continue;
      }

      if (before === undefined) {
        // A new obligation. Only a DISPROVED among them is a regression: it is
        // a finding nobody has looked at yet.
        if (after === 'DISPROVED') {
          regressions.push({ package: name, key, before: '(new)', after, kind: 'new-finding' });
        } else {
          improvements.push({ package: name, key, before: '(new)', after, kind: 'new-verdict' });
        }
        continue;
      }

      if (isProving(before) && !isProving(after)) {
        regressions.push({ package: name, key, before, after, kind: 'proof-lost' });
      } else if (!isProving(before) && after === 'DISPROVED') {
        regressions.push({ package: name, key, before, after, kind: 'new-finding' });
      } else {
        improvements.push({ package: name, key, before, after, kind: 'improved' });
      }
    }

    // An obligation that disappeared entirely: the transition is gone, or the
    // translator stopped producing it. Losing a PROOF this way is as bad as
    // having it flip, and is easy to miss by only diffing what is present.
    for (const [key, before] of Object.entries(was)) {
      if (seen.has(key)) continue;
      if (isProving(before)) {
        regressions.push({ package: name, key, before, after: '(gone)', kind: 'proof-disappeared' });
      } else {
        improvements.push({ package: name, key, before, after: '(gone)', kind: 'obligation-gone' });
      }
    }
  }

  return { regressions, improvements, unchanged, ok: regressions.length === 0 };
}

/** One-line human rendering of a difference. */
export const describeDiff = (d) =>
  `[${d.kind}] ${d.package} :: ${d.key || d.detail}` +
  (d.before ? `  ${d.before} -> ${d.after}` : '');
