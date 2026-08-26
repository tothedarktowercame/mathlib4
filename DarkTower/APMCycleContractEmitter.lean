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

def stringArray (values : List String) : Json :=
  Json.arr (values.map Json.str).toArray

def liveRoleName : LiveRole → String
  | .solver => "solver"
  | .student => "student"
  | .guide => "guide"
  | .scribe => "scribe"
  | .zaiScribe => "zai-scribe"
  | .proctor => "proctor"
  | .promotionProctor => "promotion-proctor"
  | .analyst => "analyst"

def phaseIoJson (phase : Phase) : Json :=
  Json.mkObj
    [("requires", stringArray (phaseRequires phase)),
     ("produces", stringArray (phaseProduces phase))]

def phasesJson : Json :=
  Json.mkObj (canonicalContract.phases.map fun phase =>
    (phaseName phase, phaseIoJson phase))

def receiptSchemasJson : Json :=
  Json.mkObj (receiptTypes.map fun receiptType =>
    (receiptType, Json.mkObj
      [("required", stringArray (receiptRequiredFields receiptType))]))

def roleAuthoredFieldsJson : Json :=
  Json.mkObj (allLiveRoles.map fun role =>
    (liveRoleName role, stringArray (roleAuthoredSubmissionFields role)))

def submissionSchemasJson : Json :=
  Json.mkObj
    [("schema-version", Json.num 1),
     ("controller-derived-fields", stringArray controllerDerivedSubmissionFields),
     ("role-authored-fields", roleAuthoredFieldsJson),
     ("student-memory-use", Json.mkObj
       [("role-authored-fields", stringArray ["used-ids"]),
        ("controller-derived-fields", stringArray
          ["receipt-id", "snapshot-id", "snapshot-digest",
           "accessible-memory-ids", "surfaced-ids", "queries"])]),
     ("self-reported-controller-identifiers-are-evidence", Json.bool false)]

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
     ("phases", phasesJson),
     ("receipt-schemas", receiptSchemasJson),
     ("submission-schemas", submissionSchemasJson),
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
        ("submission-covered-role-count", Json.num 8),
        ("terminal-collection-required", Json.bool true),
        ("terminal-collection-persisted", Json.bool true),
        ("terminal-collection-before-missing-observation", Json.bool true),
        ("terminal-collection-attempts-per-role", Json.num 1),
        ("terminal-repair-attempts-per-role", Json.num 1),
        ("terminal-collection-covered-role-count", Json.num 8),
        ("promotion-review-enums-normalized", Json.bool true),
        ("promotion-approved-candidates-accounted", Json.bool true),
        ("promotion-approved-unattached-refused", Json.bool true),
        ("promotion-rejections-explicit", Json.bool true),
        ("role-terminal-budgets", Json.mkObj
          [("solver", Json.mkObj [("collection-attempts", Json.num 1),
                                   ("repair-attempts", Json.num 1)]),
           ("student", Json.mkObj [("collection-attempts", Json.num 1),
                                    ("repair-attempts", Json.num 1)]),
           ("guide", Json.mkObj [("collection-attempts", Json.num 1),
                                  ("repair-attempts", Json.num 1)]),
           ("scribe", Json.mkObj [("collection-attempts", Json.num 1),
                                   ("repair-attempts", Json.num 1)]),
           ("zai-scribe", Json.mkObj [("collection-attempts", Json.num 1),
                                       ("repair-attempts", Json.num 1)]),
           ("proctor", Json.mkObj [("collection-attempts", Json.num 1),
                                    ("repair-attempts", Json.num 1)]),
           ("promotion-proctor", Json.mkObj
             [("collection-attempts", Json.num 1),
              ("repair-attempts", Json.num 1)]),
           ("analyst", Json.mkObj [("collection-attempts", Json.num 1),
                                    ("repair-attempts", Json.num 1)])]),
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
        ("client-timeout-is-success", Json.bool false),
        ("terminal-lifecycle-actions-covered", Json.arr
          #[Json.str "close-block", Json.str "close-campaign"]),
        ("retirement-binds-recorded-terminal-head", Json.bool true),
        ("frame-terminal-persisted-before-retirement", Json.bool true),
        ("retirement-replay-uses-persisted-terminal", Json.bool true),
        ("retired-workspace-absence-is-postcondition", Json.bool true),
        ("terminal-collection-is-supervisor-progress", Json.bool true),
        ("artifact-identity-from-authority-not-observation", Json.bool true),
        ("preflight-requires-positive-sorry-baseline", Json.bool true),
        ("preflight-blocking-warning-count", Json.num 0),
        ("preflight-nonblocking-warning-kinds", Json.arr
          #[Json.str "linter", Json.str "deprecation",
            Json.str "compiler-warning"]),
        ("coordinator-intent-persisted-before-activation", Json.bool true),
        ("coordinator-restart-reconciles-deterministic-job-id", Json.bool true),
        ("coordinator-startup-uses-typed-registry", Json.bool true),
        ("coordinator-one-registration-per-problem", Json.bool true),
        ("coordinator-retries-increment-same-entry", Json.bool true),
        ("coordinator-retry-beyond-maximum-refused", Json.bool true),
        ("coordinator-startup-directory-heuristics", Json.bool false)]),
     ("memory-policy", Json.mkObj
       [("content-addressed-snapshot", Json.bool true),
        ("admit-after-solve-verify", Json.bool true),
        ("independent-review", Json.bool true),
        ("student-attempts", Json.num 3),
        ("fresh-student-sessions", Json.bool true),
        ("fresh-session-rotation-mints-new-id", Json.bool true),
        ("student-session-distinctness-required-for-closed-frame", Json.bool true),
        ("exact-snapshot-binding", Json.bool true),
        ("fresh-attempt-worktree-reset-to-base", Json.bool true),
        ("attempt-state-preserved-before-reset", Json.bool true),
        ("guide-deposits-independent-review", Json.bool true),
        ("guide-union-snapshot-content-addressed", Json.bool true),
        ("next-student-binds-latest-reviewed-snapshot", Json.bool true),
        ("candidate-pattern-binding-required", Json.bool true),
        ("open-reviewed-corpus-search", Json.bool true),
        ("search-capable-roles", Json.arr
          #[Json.str "student", Json.str "scribe",
            Json.str "promotion-proctor"]),
        ("search-query-trace-persisted", Json.bool true),
        ("search-results-content-addressed", Json.bool true),
        ("student-open-search-distinct-from-proactive-snapshot", Json.bool true),
        ("self-reported-query-is-search-evidence", Json.bool false),
        ("student-dispatch-witness-required", Json.bool true),
        ("student-dispatch-required-fields", Json.arr
          #[Json.str "attempt-ordinal", Json.str "promotion-receipt-id",
            Json.str "snapshot-id", Json.str "snapshot-digest",
            Json.str "accessible-memory-ids"])]),
     ("promotion-policy", Json.mkObj
       [("distinct-promotion-proctor", Json.bool true),
        ("review-verdicts", Json.mkObj
          [("judgements", Json.arr
            #[Json.str "approve", Json.str "reassign", Json.str "reject"]),
           ("apparatus-failures", Json.arr #[Json.str "cannot-judge"])]),
        ("promotion-pass-resolution-required", Json.bool true),
        ("exact-pattern-set-required-for", Json.arr #[Json.str "approve"]),
        ("nonapproval-pattern-actions", Json.mkObj
          [("reassign", Json.str "replace"),
           ("reject", Json.str "retain-proposed")]),
        ("completed-pass-required", Json.bool true),
        ("completed-pass-candidate-accounting", Json.str "exactly-once"),
        ("materialized-artifact-required-fields", Json.arr
          #[Json.str "artifact-id", Json.str "content-digest",
            Json.str "persisted-content-digest",
            Json.str "read-back-content-digest",
            Json.str "persistence-receipt-id"]),
        ("materialized-artifact-digests-must-match", Json.bool true),
        ("review-evidence-materialized-before-disposition", Json.bool true),
        ("nonpublishing-dispositions", Json.arr
          #[Json.str "reject"]),
        ("projection-failure-action", Json.str
          "hold-at-review-awaiting-apparatus-repair"),
        ("projection-repair-reuses-persisted-judgement", Json.bool true),
        ("projection-repair-redispatches-reviewer", Json.bool false),
        ("projection-repair-exhaustion-action", Json.str
          "park-frame-and-continue-queue"),
        ("promotion-successor-validation", Json.str
          "before-snapshot-publication-and-certification"),
        ("certified-pass-snapshot-materialized", Json.bool true),
        ("certified-pass-published-candidates-exact", Json.bool true),
        ("review-dispatch-resolution-required", Json.bool true),
        ("review-dispatch-candidate-required", Json.arr
          #[Json.str "persisted", Json.str "fetchable",
            Json.str "parent-pattern-fetchable"]),
        ("review-dispatch-reviewer-inputs-required", Json.arr
          #[Json.str "base-problem-blob-fetchable",
            Json.str "solver-final-head-fetchable",
            Json.str "evidence-job-traces-fetchable"]),
        ("unresolved-review-dispatch-action",
          Json.str "hold-at-deposit-awaiting-apparatus-repair"),
        ("unresolved-review-resume-action", Json.str
          "append-only-successor-after-contract-change"),
        ("resolved-judgements-immutable-on-resume", Json.bool true),
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
        ("unsolved-partial-retry-same-problem", Json.bool true),
        ("retry-requires-retained-solver-head", Json.bool true),
        ("retry-does-not-advance-problem-queue", Json.bool true),
        ("close-result-wire-canonicalization", Json.bool true),
        ("missing-observation-receipt-type",
         Json.str "student-observation-missing"),
        ("missing-observation-author", Json.str "controller"),
        ("missing-observation-may-satisfy-observation-dependency", Json.bool true),
        ("missing-observation-may-impersonate-student", Json.bool false),
        ("recovered-observation-receipt-type",
         Json.str "student-observation-recovered"),
        ("recovered-observation-author", Json.str "controller"),
        ("recovered-observation-satisfies-observation", Json.bool true),
        ("recovered-observation-forces-partial-learning", Json.bool false),
        ("recovered-observation-certifies-rejected-candidate", Json.bool false),
        ("student-terminal-candidate-required", Json.bool true),
        ("student-candidate-content-addressed", Json.bool true),
        ("student-candidate-lean-validated", Json.bool true),
        ("student-candidate-persisted-before-receipt", Json.bool true),
        ("student-candidate-replay-idempotent", Json.bool true),
        ("rejected-student-candidate-evidence-only", Json.bool true),
        ("missing-observation-records-certified-candidate", Json.bool false),
        ("missing-observation-controller-memory-use-required", Json.bool true),
        ("missing-observation-scribe-compatible", Json.bool true)]),
     ("analyst-policy", Json.mkObj
       [("outside-frame-order", Json.bool true),
        ("wake-after-terminal-only", Json.bool true),
        ("partial-terminal-wakes-analyst", Json.bool true),
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
        ("student-turn-timeout-ms", Json.num 1800000),
        ("zai-request-timeout-ms", Json.num 300000)])]

def emit : IO Unit := IO.println contractJson.compress

end DarkTower.APMCycleMachine.ContractEmitter

def main : IO Unit := DarkTower.APMCycleMachine.ContractEmitter.emit
