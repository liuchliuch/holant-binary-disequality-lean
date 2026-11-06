# Holant with Binary Disequality in Lean

A Lean formalization of **A Dichotomy for Complex Boolean Holant
with Binary Disequality**, by Chenghua Liu and Boning Meng.

The [original paper is available on arXiv](https://arxiv.org/abs/2609.00219).
This repository includes the November 6, 2026 Overleaf source snapshot of
`stoc2027-DEQ.tex`, with its short submission and embedded full paper. The
exact source digest and export provenance are recorded in
[manuscript/source.json](manuscript/source.json). The Lean formalization
uses this snapshot's reduced criteria and public naming; see the
[manuscript correspondence and corrections](docs/statements.md).

This repository accompanies paper 1, concerning binary disequality. It contains
the three main complexity dichotomies in that paper, uniform recognition
programs on exact algebraic input, the seven-branch tractable evaluation theorem,
and retained structural lemmas and exact finite certificates.
[The structural correspondence review](docs/structural-correspondence.md)
records naming changes and the scope of supplementary results, including the
new successor diagram that has no independent Lean path-exhaustiveness theorem.

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

This is a large proof library. `HOLANT_BUILD_THREADS` controls build concurrency
and defaults to 2; lower it if memory is limited. Build products and downloaded
tools stay in ignored directories. See [CI resources](docs/verification.md#resources-and-continuous-integration)
for the verification configuration.

## Statement and proof separation

`Holant/Statements.lean` defines the mathematical propositions from the original
signature, graph, coefficient, complexity and tractability definitions. Its
import closure excludes the main classification and dichotomy assembly.
`Holant/Proofs.lean` supplies proofs of those specifications.
The direct `ReTract(F union {X})` and native-edge `ReTractX(F)` criteria are
connected to the retained implementations by algebraic equivalences in
`Holant/Tractable/STOC2027.lean`, `ReducedEdgeBridge.lean` and
`QuaternaryAnchor.lean`. The equality-accessible theorem is now F.5.2;
`literalEquality` remains a compatibility alias.

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
python3 scripts/check_manuscript.py
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
| `manuscript/` | Exact Overleaf source with embedded references, provenance and rebuilt PDF |
| `scripts/` | Build, verification and packaging commands |

Only reachable Lean modules are distributed. Internal declaration names are
preserved so that mathematical dependencies remain traceable. Development
logs, unused proof branches, dependency caches and temporary files are excluded.

## Manuscript and licensing

Build the manuscript with a TeX installation providing `latexmk`, pdfLaTeX:

```sh
bash scripts/build_manuscript.sh
```

Code and repository documentation are licensed under [Apache-2.0](LICENSE).
The manuscript retains the authors' copyright under
[its separate notice](manuscript/LICENSE). See [CITATION.cff](CITATION.cff) for
citation metadata.
