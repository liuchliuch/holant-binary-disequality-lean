# Holant with Binary Disequality in Lean

A Lean formalization of **A Dichotomy for Complex Boolean Holant
with Binary Disequality**, by Chenghua Liu and Boning Meng.

The [original paper is available on arXiv](https://arxiv.org/abs/2609.00219).
This repository includes the latest revised manuscript, with simplifications,
revisions and corrections to the original version. The Lean formalization
accompanies this revised manuscript; see the
[manuscript correspondence and corrections](docs/statements.md).

This repository accompanies paper 1, concerning binary disequality. It contains
the three main complexity dichotomies in that paper, uniform recognition
programs on exact algebraic input, the seven-branch tractable evaluation theorem,
and the structural lemmas and exact finite certificates used by the manuscript.

- [Read the manuscript](manuscript/paper.pdf) or [its LaTeX source](manuscript/paper.tex).
- [Read the public statements](Holant/Statements.lean) before [their proofs](Holant/Proofs.lean).
- [Find the manuscript-to-code entry points](docs/statements.md).
- [Reproduce the verification](docs/verification.md).

## Build

Install [elan](https://github.com/leanprover/elan), Git and Python 3.9 or later.
The checked-in toolchain and manifest pin Lean **4.34.1** and every dependency.

```sh
bash scripts/env.sh lake exe cache get
bash scripts/env.sh lake build
```

Do not run `lake update` to reproduce this release. Missing dependencies are
fetched at the revisions in `lake-manifest.json`. The environment wrapper also
checks existing dependency checkouts and selects Command Line Tools on macOS.

This is a large proof library. A full verification should use at least 64 GiB
of RAM; 128 GiB is recommended. Individual Lean compiler processes have a
12 GB memory limit. `HOLANT_BUILD_THREADS` controls concurrent Lean work and
defaults to 4. Build products and downloaded tools stay in ignored directories.

## Statement and proof separation

`Holant/Statements.lean` defines the mathematical propositions from the original
signature, graph, coefficient, complexity and tractability definitions. Its
import closure excludes the main classification and dichotomy assembly.
`Holant/Proofs.lean` supplies proofs of those specifications.

The official [Lean Comparator](https://github.com/leanprover/comparator) checks
the four public complexity/evaluation statements against
`Verification/Challenge.lean` in separate Lean environments. It checks their
referenced definitions, the axiom whitelist, and kernel acceptance. The four
`sorry` placeholders in the challenge are intentional reference holes; the
challenge is never imported by the proof library or solution.

Uniform decision programs are exported separately by `Holant/Decidability.lean`
and included in the complete source and axiom audits. Recognition is asserted
to be decidable, without a polynomial-time recognition claim.

## Verify

A quick source-only check requires only Python:

```sh
python3 scripts/release.py scan
```

For a full check of trusted local sources, including the actual Comparator:

```sh
bash scripts/env.sh python3 scripts/verify.py --trusted-local
```

This mode performs theorem comparison and kernel checking without an operating
system sandbox. On Linux, omitting `--trusted-local` sandboxes Comparator's
build and export steps. The complete release driver still requires trusted
source; see [the prerequisites and trust boundary](docs/verification.md).

GitHub Actions runs the complete library build, axiom audit, fresh-environment
kernel replay and official sandboxed Comparator. Each run retains reports and
source hashes as downloadable artifacts. Local reports are written under
`.lake/release/`. Mechanical checks certify
the recorded formal statements and proof objects. Correspondence with the
English manuscript remains a mathematical review task; the statement guide
identifies the public interfaces and manuscript corrections.

## Repository layout

| Path | Purpose |
| --- | --- |
| `Holant/Statements.lean` | Reviewable public mathematical specifications |
| `Holant/Proofs.lean` | Proofs of the public complexity and evaluation statements |
| `Holant/Decidability.lean` | Uniform exact-input recognition entry points |
| `Holant/Library.lean` | Supplementary manuscript results and finite certificates |
| `Holant/Proofs/` | Proof implementations grouped by mathematical topic |
| `Holant/` | The transitive proof dependency closure |
| `Verification/` | Comparator reference, solution, pinned tool revisions |
| `manuscript/` | Corrected manuscript source, bibliography and PDF |
| `scripts/` | Build, verification and packaging commands |

Only reachable Lean modules are distributed. Internal declaration names are
preserved so that mathematical dependencies remain traceable. Development
logs, unused proof branches, dependency caches and temporary files are excluded.

## Manuscript and licensing

Build the manuscript with a TeX installation providing `latexmk`, pdfLaTeX and
BibTeX:

```sh
bash scripts/build_manuscript.sh
```

Code and repository documentation are licensed under [Apache-2.0](LICENSE).
The manuscript retains the authors' copyright under
[its separate notice](manuscript/LICENSE). See [CITATION.cff](CITATION.cff) for
citation metadata.
