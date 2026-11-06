#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/../manuscript"
export SOURCE_DATE_EPOCH="${SOURCE_DATE_EPOCH:-1793974997}"
mkdir -p ../.lake/manuscript
latexmk -g -pdf -interaction=nonstopmode -halt-on-error -outdir=../.lake/manuscript paper.tex
cp ../.lake/manuscript/paper.pdf paper.pdf
python3 ../scripts/check_manuscript.py --aux ../.lake/manuscript/paper.aux
