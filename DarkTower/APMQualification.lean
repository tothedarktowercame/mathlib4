import DarkTower.APMCycleMachine

/-! Non-vacuity witnesses for the executable APM behavioural bridge. -/

namespace DarkTower.APMQualification

open DarkTower.APMCycleMachine

def modelledInvariantClasses : List String :=
  ["ordering", "ledger-receipts", "dispatch", "memory", "isolation",
   "terminal", "analyst"]

theorem invariant_classes_nonempty : modelledInvariantClasses.length = 7 := by decide

theorem canonical_cycle_has_all_phases : canonicalPhaseOrder.length = 11 := by decide

theorem solved_problem_partial_frame_is_admissible :
    validOutcome .solved .framePartial := by trivial

theorem close_json_wire_boundary_nonvacuous :
    validCloseWireResult "closed" := json_closed_result_is_accepted

theorem partial_json_wire_boundary_nonvacuous :
    validCloseWireResult "partial" := partial_json_result_is_accepted

theorem reused_student_session_mutation_is_killed :
    ¬ validSessionRotation f25ReusedStudentSession :=
  f25_reused_student_session_refused

theorem partial_terminal_analyst_wake_nonvacuous :
    analystWakeEligibleFrameResult "partial" :=
  partial_terminal_frame_wakes_analyst

theorem terminal_lifecycle_handler_set_nonvacuous :
    terminalLifecycleActions.length = 2 :=
  terminal_lifecycle_actions_nonvacuous

theorem stale_base_retirement_mutation_is_killed :
    ¬ validWorkspaceRetirementBinding staleBaseRetirementMutant :=
  stale_base_cannot_substitute_for_terminal_head

theorem collected_terminal_output_cannot_skip_certification :
    supervisorMayAdvance .terminalCollected = false :=
  terminal_collection_is_progress_but_not_certification

def analystWitness : List AnalystWake :=
  [{frameId := "f1", terminal := true, ordinal := 1,
    seriesInputVersion := 1, appendOnly := true,
    proposalType := none, proposalDigest := none,
    successorHandoff := false, mutatesInFlight := false},
   {frameId := "f2", terminal := true, ordinal := 2,
    seriesInputVersion := 2, appendOnly := true,
    proposalType := some "regime-proposal",
    proposalDigest := some "content-addressed-proposal",
    successorHandoff := true, mutatesInFlight := false}]

theorem analyst_tenure_nonvacuous : validAnalystTenure analystWitness := by
  simp [validAnalystTenure, analystWitness]

end DarkTower.APMQualification
