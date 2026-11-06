# Manuscript provenance

`paper.tex` is the unmodified November 6, 2026 Overleaf source export of
`stoc2027-DEQ.tex`. It contains the STOC short submission, shared embedded
bibliography, and the complete paper. `source.json` records the project URL,
export timestamp, archive digest, exact source digest, and current labels.
The earlier separately maintained `paper1.bib` is no longer needed because
this snapshot embeds its references; the prior bibliography remains in Git
history.

Run `python3 scripts/check_manuscript.py` from the repository root to verify the
source digest. `bash scripts/build_manuscript.sh` rebuilds `paper.pdf` and also
checks the current correspondence numbers against the resulting `.aux` file.
The deterministic PDF timestamp is the export time. No change to the source
is made by either command.

The original publication is arXiv:2609.00219. The November source is the target
of this synchronization; an arXiv version or an older repository PDF must not
be substituted for it. See `docs/statements.md` and
`docs/structural-correspondence.md` for reviewed formalization scope.

The authors' manuscript copyright and the separate manuscript `LICENSE`
remain unchanged. Code and repository documentation use the root Apache-2.0
license.
