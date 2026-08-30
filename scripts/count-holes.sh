#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
holes_file="$repo_root/DarkTower/WarMachine/Holes.lean"

records=("P-validated-R5" "P-R9" "P-R2" "P-R8" "delivery-lifecycle")
hole_total=0
closed_total=0

for record in "${records[@]}"; do
  holes=$(grep -F -c "HOLE · owner: $record" "$holes_file" || true)
  closed=$(grep -F -c "CLOSED-BY-RECORD · owner: $record" "$holes_file" || true)
  printf '%s declared-with-body: %d\n' "$record" "$closed"
  printf '%s declared-with-sorry: %d\n' "$record" "$holes"
  closed_total=$((closed_total + closed))
  hole_total=$((hole_total + holes))
done

printf 'total declared-with-body: %d\n' "$closed_total"
printf 'total declared-with-sorry: %d\n' "$hole_total"
