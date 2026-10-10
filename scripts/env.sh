#!/usr/bin/env bash
# Reproducible environment without upgrading locked dependencies.
set -euo pipefail
cd "$(dirname "$0")/.."
if [[ "$(uname -s)" == Darwin && -d /Library/Developer/CommandLineTools ]]; then
  export DEVELOPER_DIR=/Library/Developer/CommandLineTools
  export PATH="/Library/Developer/CommandLineTools/usr/bin:$HOME/.elan/bin:$PATH"
fi
export MATHLIB_NO_CACHE_ON_UPDATE=1
export LEAN_NUM_THREADS="${HOLANT_BUILD_THREADS:-4}"
python3 scripts/release.py dependencies
exec "$@"
