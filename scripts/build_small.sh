#!/bin/zsh
# Build everything on a small machine (8 GB RAM): the 24 certificate modules three at a time
# (each Lean process needs about 0.7 GB and 45 s), then the rest. On a machine with 16 GB or
# more, plain `lake build GRHCorollaries Challenge` does the same thing.
cd "$(dirname "$0")/.." || exit 2
export PATH="/opt/homebrew/bin:$HOME/.elan/bin:$PATH"
set -e
for grp in "00 01 02" "03 04 05" "06 07 08" "09 10 11" "12 13 14" "15 16 17" "18 19 20" "21 22 23"; do
  T=()
  for k in ${=grp}; do T+=("GRHCorollaries.Cubes.Certs.S$k"); done
  lake build $T
done
lake build GRHCorollaries Challenge
