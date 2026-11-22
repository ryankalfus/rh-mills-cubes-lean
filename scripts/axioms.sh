#!/bin/zsh
# Print the axioms of the headline theorems. Usage: scripts/axioms.sh
cd "$(dirname "$0")/.." || exit 2
export PATH="/opt/homebrew/bin:$HOME/.elan/bin:$PATH"
exec lockf -t 3600 .lake/leancheck.lock lake env lean GRHCorollaries/Audit.lean
