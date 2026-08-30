#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
contract="$repo_root/DarkTower/WarMachine/holes-contract.json"
records=("P-validated-R5" "P-R9" "P-R2" "P-R8" "delivery-lifecycle")

for record in "${records[@]}"; do
  bodies=$(jq --arg record "$record" '[.declarations[] | select(.owner | startswith($record)) | select(.kind == "closed")] | length' "$contract")
  holes=$(jq --arg record "$record" '[.declarations[] | select(.owner | startswith($record)) | select(.kind == "hole")] | length' "$contract")
  printf '%s declared-with-body: %d\n' "$record" "$bodies"
  printf '%s declared-with-sorry: %d\n' "$record" "$holes"
done

jq -r '"total declared-with-body: \([.declarations[] | select(.kind == "closed")] | length)\ntotal declared-with-sorry: \([.declarations[] | select(.kind == "hole")] | length)"' "$contract"
