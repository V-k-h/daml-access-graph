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
  for (const report of reports) {
    const name = report.package || report.dar;
    const entries = {};
    for (const r of report.results || []) {
      entries[verdictKey(r)] = statusFamily(r.status);
    }
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

  for (const report of reports) {
    const name = report.package || report.dar;
    const was = (baseline.packages || {})[name];
    if (!was) {
      improvements.push({
        package: name,
        kind: 'new-package',
        detail: `${(report.results || []).length} verdict(s) not in the baseline`,
      });
      continue;
    }

    const seen = new Set();
    for (const r of report.results || []) {
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
