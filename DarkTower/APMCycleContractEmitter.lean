/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.APMCycleMachine
import Lean.Data.Json

/-!
# Deterministic executable contract emitter for the APM cycle machine

The generated JSON is consumed by the Clojure implementation.  Policy fields
are rendered from the Lean definitions; the runtime is not permitted to carry
an independently maintained phase table.
-/

namespace DarkTower.APMCycleMachine.ContractEmitter

open Lean

def phaseName : Phase → String
  | .preflight => "preflight"
  | .solve => "solve"
  | .verify => "verify"
  | .promoteSolver => "promote-solver"
  | .studentAttempt1 => "student-attempt-1"
  | .guideIntervention1 => "guide-intervention-1"
  | .studentAttempt2 => "student-attempt-2"
  | .guideIntervention2 => "guide-intervention-2"
  | .studentAttempt3 => "student-attempt-3"
  | .scribeReduce => "scribe-reduce"
  | .closeFrame => "close-frame"

def phaseJson (phases : List Phase) : Json :=
  Json.arr (phases.map (Json.str ∘ phaseName)).toArray

def transitionJson (phase : Phase) : Json :=
  Json.mkObj
    [("from", Json.str (phaseName phase)),
     ("to", match nextPhase? phase with
       | some next => Json.str (phaseName next)
       | none => Json.null)]

def contractJson : Json :=
  Json.mkObj
    [("schema-version", Json.num 1),
     ("contract-id", Json.str canonicalContract.id),
     ("phase-order", phaseJson canonicalContract.phases),
     ("transitions", Json.arr
       (canonicalContract.phases.map transitionJson).toArray),
     ("dispatch-policy", Json.mkObj
       [("preannounce-required", Json.bool true),
        ("activation-status", Json.num 202),
        ("idempotent-reactivation", Json.bool true),
        ("terminal-command-own-exit", Json.num 0),
        ("persist-claim", Json.bool true),
        ("persist-receipt", Json.bool true),
        ("restart-same-job", Json.bool true),
        ("typed-terminal-output-required", Json.bool true),
        ("typed-role-submission-tool-required", Json.bool true),
        ("submission-authority-controller-owned", Json.bool true),
        ("submission-persisted-before-advance", Json.bool true),
        ("conversation-is-receipt-authority", Json.bool false),
        ("submission-conflict-policy", Json.str "reject"),
        ("submission-covered-role-count", Json.num 7),
        ("terminal-collection-required", Json.bool true),
        ("terminal-collection-persisted", Json.bool true),
        ("terminal-collection-before-missing-observation", Json.bool true),
        ("terminal-collection-attempts-per-role", Json.num 1),
        ("terminal-repair-attempts-per-role", Json.num 1),
        ("terminal-collection-covered-role-count", Json.num 7),
        ("missing-observation-student-only", Json.bool true),
        ("unbounded-conversational-retries", Json.bool false),
        ("typed-submission-migration-max", Json.num 1),
        ("typed-submission-migration-fresh-session", Json.bool true),
        ("typed-submission-migration-preserves-snapshot", Json.bool true),
        ("activation-supersession-max", Json.num 1),
        ("activation-supersession-requires-cancellation", Json.bool true),
        ("activation-supersession-distinct-job", Json.bool true),
        ("deterministic-job-id-before-announce", Json.bool true),
        ("announce-activate-request-identical", Json.bool true),
        ("queued-job-survives-restart", Json.bool true),
        ("conflicting-job-replay-policy", Json.str "reject"),
        ("terminal-output-repair-attempts", Json.num 1),
        ("repair-feedback-findings-required", Json.bool true),
        ("client-timeout-is-success", Json.bool false)]),
     ("memory-policy", Json.mkObj
       [("content-addressed-snapshot", Json.bool true),
        ("admit-after-solve-verify", Json.bool true),
        ("independent-review", Json.bool true),
        ("student-attempts", Json.num 3),
        ("fresh-student-sessions", Json.bool true),
        ("exact-snapshot-binding", Json.bool true),
        ("student-dispatch-witness-required", Json.bool true),
        ("student-dispatch-required-fields", Json.arr
          #[Json.str "attempt-ordinal", Json.str "promotion-receipt-id",
            Json.str "snapshot-id", Json.str "snapshot-digest",
            Json.str "accessible-memory-ids"])]),
     ("promotion-policy", Json.mkObj
       [("distinct-promotion-proctor", Json.bool true),
        ("base-problem-blob-required", Json.bool true),
        ("problem-path-required", Json.bool true),
        ("solver-final-head-required", Json.bool true),
        ("typed-lanes-required", Json.num 4),
        ("persisted-review-reason-required", Json.bool true),
        ("persisted-review-residual-required", Json.bool true),
        ("student-query-log-required", Json.bool true)]),
     ("isolation-policy", Json.mkObj
       [("campaign-scoped-regulator", Json.bool true),
        ("campaign-scoped-problem-buffer", Json.bool true),
        ("distinct-continuation-session", Json.bool true),
        ("distinct-analyst-session", Json.bool true),
        ("projection-ledger-binding", Json.bool true)]),
     ("terminal-policy", Json.mkObj
       [("certified-phase-receipts", Json.num 11),
        ("separate-problem-frame-outcomes", Json.bool true),
        ("learning-outcome-required", Json.bool true),
        ("solved-partial-bankable", Json.bool true),
        ("bankable-solved-successor-eligible", Json.bool true),
        ("missing-observation-receipt-type",
         Json.str "student-observation-missing"),
        ("missing-observation-author", Json.str "controller"),
        ("missing-observation-may-satisfy-observation-dependency", Json.bool true),
        ("missing-observation-may-impersonate-student", Json.bool false)]),
     ("analyst-policy", Json.mkObj
       [("outside-frame-order", Json.bool true),
        ("wake-after-terminal-only", Json.bool true),
        ("exactly-once-per-frame", Json.bool true),
        ("append-only-series-input", Json.bool true),
        ("tenure-frames", Json.num 2),
        ("successor-handoff-required", Json.bool true),
        ("in-flight-mutation", Json.bool false)]),
     ("bounds", Json.mkObj
       [("solver-max-rounds", Json.num 50),
        ("solver-checkpoint-every", Json.num 10),
        ("student-attempts", Json.num 3),
        ("guide-interventions", Json.num 2),
        ("analyst-tenure-frames", Json.num 2),
        ("seat-turn-timeout-ms", Json.num 3600000),
        ("zai-request-timeout-ms", Json.num 300000)])]

def emit : IO Unit := IO.println contractJson.compress

end DarkTower.APMCycleMachine.ContractEmitter

def main : IO Unit := DarkTower.APMCycleMachine.ContractEmitter.emit
