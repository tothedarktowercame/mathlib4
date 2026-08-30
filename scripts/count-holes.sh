#!/usr/bin/env bash
set -euo pipefail

root=$(cd "$(dirname "$0")/.." && pwd)
holes="$root/DarkTower/WarMachine/Holes.lean"
others=$(find "$root/DarkTower/WarMachine" -maxdepth 1 -name '*.lean' ! -name 'Holes.lean' -print)
records=("P-validated-R5" "P-R9" "delivery-lifecycle")
total_body=0
total_sorry=0

for record in "${records[@]}"; do
  sorry=$(awk -v record="$record" '
    /\/-- HOLE · owner:/ {owned = index($0, "owner: " record) > 0; next}
    owned && /:= sorry/ {count++; owned = 0}
    END {print count + 0}
  ' "$holes")
  declared=$(rg -l "owner: $record" "$holes" $others 2>/dev/null | wc -l)
  declarations=$(rg -c "owner: $record" "$holes" $others 2>/dev/null |
    awk -F: '{sum += $NF} END {print sum + 0}')
  body=$((declarations - sorry))
  total_body=$((total_body + body))
  total_sorry=$((total_sorry + sorry))
  printf '%s declared-with-body: %d  declared-with-sorry: %d\n' "$record" "$body" "$sorry"
  : "$declared"
done

printf 'total declared-with-body: %d  declared-with-sorry: %d\n' "$total_body" "$total_sorry"
