#!/bin/zsh
# Run `lake comparator` on Challenge vs the solution library and keep a log.
# macOS has no bubblewrap, so this uses --inadvisably-no-sandbox: fine for checking our own
# project, NOT a substitute for a sandboxed run on Linux. Extra args are passed on (e.g. --paranoid).
cd "$(dirname "$0")/.." || exit 2
export PATH="/opt/homebrew/bin:$HOME/.elan/bin:$PATH"
export PATH="$(lean --print-prefix)/bin:$PATH"     # nanoda_bin, con-leche, lean4lean, leanexport live here
D=$(date -u +%Y-%m-%dT%H%MZ)
LOG="logs/verify/comparator-$D.log"
mkdir -p logs/verify
{
  echo "# lake comparator --inadvisably-no-sandbox $@"
  echo "# started $(date -u); $(lean --version)"
  echo "# comparator.json:"; cat comparator.json
  /usr/bin/time -l lockf -t 7200 .lake/comparator.lock lake comparator --inadvisably-no-sandbox "$@" 2>&1
  echo "comparator exit code: $?"
  echo "# finished $(date -u)"
  df -h "$HOME" | tail -1
} > "$LOG" 2>&1
echo "$LOG"
