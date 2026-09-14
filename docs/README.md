# Documentation

| File | Audience | Contents |
|---|---|---|
| [`verification.pdf`](verification.pdf) | New readers | Guided introduction to the verification pipeline, with a worked example carried end to end. Start here. |
| [`verification.tex`](verification.tex) | Maintainers | Source of the above. |
| [`../formal/SPECIFICATION.md`](../formal/SPECIFICATION.md) | Reference | Definitions and theorems, stated tersely, each cross-referenced to Lean and JavaScript. |
| [`../formal/Correspondence.md`](../formal/Correspondence.md) | Reviewers, auditors | Trust audit: which arrows are machine-checked, which are tested, which are trusted. |

## Building the PDF

The committed `verification.pdf` is current. Rebuild it only after editing the
source:

```bash
npm run docs          # or: tectonic docs/verification.tex
```

[Tectonic](https://tectonic-typesetting.github.io/) is used because it is a
single binary that resolves its own package dependencies, so the document
builds without a full TeX distribution. Any standard LaTeX toolchain works too:

```bash
latexmk -pdf docs/verification.tex
```

The document requires `amsmath`, `amssymb`, `amsthm`, `stmaryrd`, `booktabs`,
`microtype`, `listings`, `tikz`, `hyphenat` and `hyperref`.

A clean build produces no overfull or underfull box warnings. Please keep it
that way when editing.
