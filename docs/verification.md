# Verification

## Pinned inputs

`lean-toolchain` pins Lean 4.34.1. `lake-manifest.json` pins Mathlib and its
transitive dependencies. `Verification/tools.json` pins official Comparator,
lean4export and Landrun commits. The Comparator revision targets the Lean 4.34
series and is built with this project's exact 4.34.1 toolchain.

Use `bash scripts/env.sh COMMAND ...` for Lean and Lake commands. The wrapper
checks already installed dependencies before Lake runs. Fresh installations
may fetch missing dependencies at the locked revisions. Reproduction does not
require `lake update`.

## Full release check

In addition to the Lean build tools, the full check requires `latexmk`,
pdfLaTeX, BibTeX and `qpdf` to rebuild and validate the bundled manuscript.

For previously trusted local source on macOS or Linux:

```sh
bash scripts/env.sh python3 scripts/verify.py --trusted-local
```

The verification driver checks:

1. English-only release text, complete imports, reachability, and absence of
   local machine paths, credential-like content and build artifacts.
2. A real build of the public library and solution.
3. Axiom dependencies of every imported project declaration, allowing only
   `propext`, `Classical.choice` and `Quot.sound`.
4. Kernel replay of the complete `Holant` environment into a fresh environment
   (`leanchecker --fresh`), including all project proof modules and their
   imported dependencies. The preceding audit checks the exact project import set.
5. Official Comparator comparison of the four public theorem statements and
   their referenced definitions, followed by kernel replay of their proofs.
6. Negative integration checks reject a provable `True` replacement, an added
   `False` premise, and an extra axiom for the intended statement.
7. Independent exact arithmetic for the manuscript corrections.
8. PDF integrity and unchanged release-source hashes throughout verification.

The driver writes detailed local logs under `.lake/release/` and a compact,
portable record to `.lake/release/result.json`. CI stores separate build,
kernel and Comparator records in its downloadable artifacts. A successful record names the
verification mode and hashes the source manifest. Packaging refuses to proceed
if the source changed after that record was produced.

## Comparator reference boundary

Read `Holant/Statements.lean` and its definitions first. Its import closure
excludes the main proof and classification assembly. `Verification/Challenge.lean`
contains four theorem holes with the public names and expected types.
`Verification/Solution.lean` imports only the proved public entry.

The challenge's four `sorry` bodies are allowed only in the reference file.
No proof module may import it. The solution and complete library must pass the
three-axiom whitelist, which excludes `sorryAx`. The source scan enforces both
conditions and checks that every distributed Lean module is reachable from a
published entry point.

Trusted-local mode uses the upstream development Landrun shim. The actual
Comparator and kernel checks still run, but this mode supplies **no operating
system sandbox**. It is suitable for checking this already trusted local source,
not for executing adversarial submissions. This distinction is recorded in the
release evidence.

To sandbox Comparator's build and export steps, use Linux with Landlock, a working user systemd manager,
Git, elan, Python and Go 1.24 or later, and run:

```sh
bash scripts/env.sh python3 scripts/verify.py
```

The tool script builds the pinned Landrun source and invokes Comparator inside
`systemd-run` with `RestrictAddressFamilies=~AF_UNIX`, following
[upstream Comparator guidance](https://github.com/leanprover/comparator).
Run as an unprivileged user. The complete driver also rebuilds the paper and
library outside that sandbox, so **the full release check requires trusted
source in both modes**. For a separately supplied untrusted proof, review the
trusted challenge and build configuration and invoke `scripts/comparator.py`
alone on Linux, following upstream's additional assumptions. Additional
external kernels are not enabled in this release.

## Resources and continuous integration

The complete library is large. Use a machine with at least 64 GiB RAM; 128 GiB
is recommended for full replay and comparison. Set `HOLANT_BUILD_THREADS=1`
for sequential compilation if needed. Downloaded dependencies and build output
can occupy tens of gigabytes; they are excluded from the release archive.

GitHub Actions runs on pushes, pull requests and manual dispatches using
Ubuntu 24.04 runners. The build job starts without project compilation products
and audits every project declaration. Two downstream jobs verify the source
and object hashes of that exact build artifact before independently running
the complete environment replay and official Comparator. The Linux jobs use
one Lean worker and additional swap to fit the large library. Comparator
preflight checks enforce read-only files, TCP restrictions and the AF_UNIX guard.
Reports and logs are retained as workflow artifacts; generated records are not
checked into the source repository.

`HOLANT_BUILD_THREADS` controls Lean worker threads. Local full verification
runs the expensive checks sequentially. CI separates them into jobs with
independent time and memory budgets.

## Manuscript

The manuscript directory contains `paper.tex`, `paper1.bib`, and the compiled
`paper.pdf`. Its figures are defined in the LaTeX source. A standard TeX Live
installation with `latexmk`, pdfLaTeX and BibTeX is sufficient:

```sh
bash scripts/build_manuscript.sh
qpdf --check manuscript/paper.pdf
```

The paper's references to Python files under `certificates/` refer to the
[original Python companion](https://github.com/liuchliuch/Holant-X-Dichotomy),
as explained in its Code Availability section. Those files are not required
by the Lean build.

## Packaging

After successful verification, create a deterministic source archive outside
the repository:

```sh
python3 scripts/release.py package --output ../holant-binary-disequality-lean.zip
```

The archive has one `holant-binary-disequality-lean/` root, includes dotfiles and the manuscript,
and excludes `.lake/`, `.tools/`, Git state and local Python caches. The packager checks the successful verification's source manifest and performs
a ZIP CRC check before reporting the archive's SHA-256 digest.
