#!/usr/bin/env bash
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"
lake build DarkTower.WarMachine.Holes
tmp="$(mktemp)"
trap 'rm -f "$tmp"' EXIT
lake env lean --run DarkTower/WarMachine/Holes.lean > "$tmp"
# Lean writes source warnings to stdout before `main`; the compact registry is
# the final line, so keep that one JSON value as the artifact.
tail -n 1 "$tmp" > DarkTower/WarMachine/holes-contract.json
