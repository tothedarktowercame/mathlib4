#!/usr/bin/env bash
set -euo pipefail

fixture_dir=${1:?usage: check_apm_trace_fixtures.sh FIXTURE-DIRECTORY}
checker=DarkTower/APMCampaignTraceChecker.lean

lake env lean --run "$checker" "$fixture_dir/valid.json"
lake env lean --run "$checker" "$fixture_dir/partial-frame-series.json"
for mutant in skipped-promotion reordered-phases stale-ledger-reference premature-close \
  duplicate-job-identity unaccepted-activation nonterminal-advancement \
  lost-restart-continuity timeout-as-success wrong-snapshot \
  depositor-is-reviewer reused-student-session campaign-isolation-collision \
  projection-ledger-mismatch missing-receipt-closure conflated-outcome \
  pre-close-analyst duplicate-analyst-wake mutable-series-input early-tenure \
  late-tenure missing-proposal-handoff inflight-regime-mutation; do
  if lake env lean --run "$checker" "$fixture_dir/$mutant.json"; then
    echo "mutation survived: $mutant" >&2
    exit 1
  fi
done
