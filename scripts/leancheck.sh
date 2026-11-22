#!/bin/zsh
# Type-check one Lean file inside this project, one process at a time (8 GB machine).
# Usage: scripts/leancheck.sh GRHCorollaries/Foo.lean      (prints Lean's messages; exit code = lean's)
cd "$(dirname "$0")/.." || exit 2
export PATH="/opt/homebrew/bin:$HOME/.elan/bin:$PATH"
exec lockf -t 3600 .lake/leancheck.lock lake env lean "$@"
