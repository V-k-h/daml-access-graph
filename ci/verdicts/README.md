# Committed verdict baselines

One file per package, recording which obligations the verifier is expected to
discharge. `backend/verify.js --baseline <file>` compares against it and exits
nonzero on a REGRESSION.

## What counts as a regression

Verdicts are not symmetric, and the gate encodes that:

| Change | Verdict |
| --- | --- |
| `PROVED*` becomes anything else | **regression** (proof lost) |
| a `PROVED*` obligation disappears entirely | **regression** (easy to miss by diffing only what is present) |
| a new `DISPROVED` appears | **regression** (a finding nobody has triaged) |
| anything becomes `PROVED*` | improvement, never a failure |
| the bound in `PROVED-BOUNDED (lists up to length N)` changes | not a change: the bound is a property of the run, not of the code |

"Fail if there are any findings" would be useless here: a real package has
correct `DISPROVED` verdicts from the first run, because mint and burn choices
genuinely do not conserve. What matters is movement.

## Refreshing

After a legitimate improvement:

    node backend/verify.js path/to/pkg.dar --baseline ci/verdicts/<pkg>.json --update-baseline

Review the diff before committing. A shrinking file is the interesting case:
it means obligations stopped being produced.

## Why the DARs are not in this repository

They are build artifacts of a separate codebase, large, and not ours to
vendor. The CI job runs this gate only where a DAR directory has been made
available (repository variable `DAML_DAR_DIR`) and prints a notice when it has
not, rather than passing silently and looking like coverage that does not
exist.
