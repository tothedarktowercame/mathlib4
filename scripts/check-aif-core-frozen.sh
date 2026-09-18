#!/usr/bin/env bash
# check-aif-core-frozen.sh — the AIF theory core is kept immutable.
#
# Policy (Joe, 2026-09-18): the core Lean is not a scratchpad; agents do not
# write status, permissions, or authority prose into it. Any change to a
# core file fails this check until the pins are deliberately re-generated
# in their own commit (operator-visible event):
#   sha256sum <the five core files> > scripts/aif-core-pins.txt
# (Terms, Institutions, Learning, Certificates, Selection ONLY: the
#  checker and generated witnesses beside them are deliberately NOT
#  frozen -- do not glob the directory)
# New work goes in NEW modules, never edits to frozen ones
# (futon memory: subject-file-freeze-for-admitted-pins).
set -euo pipefail
cd "$(dirname "$0")/.."
status=0
while read -r sha file; do
  actual=$(sha256sum "$file" | cut -d' ' -f1)
  if [ "$actual" != "$sha" ]; then
    echo "FROZEN-CORE VIOLATION: $file (expected ${sha:0:12}..., got ${actual:0:12}...)"
    status=1
  fi
done < scripts/aif-core-pins.txt
[ "$status" -eq 0 ] && echo "aif-core-frozen: OK ($(wc -l < scripts/aif-core-pins.txt) files)"
exit $status
