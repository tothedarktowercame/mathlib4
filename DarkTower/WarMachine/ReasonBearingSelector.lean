import DarkTower.WarMachine.MachineAction

/-!
# Reason-bearing strategic-policy selector

This is a new boundary beside the frozen `MachineAction.machineAction`.  It
models the complete reason-bearing policy table described by futon2's row-15
selector specification; it does not relabel the controller-head boundary.
-/

namespace DarkTower.WarMachine.ReasonBearingSelector

open DarkTower.WarMachine.MachineAction

/-- One admitted strategic policy.  The propositions are the retained
admissibility and evidence-support witnesses, rather than names inferred from
the policy id. -/
structure ReasonBearingPolicy where
  policyId : String
  missionIds : List String
  logHabit : ℝ
  predictedG : ℝ
  admissibilityWitness : Prop
  supportWitness : Prop

/-- The complete selector input.  `declaredPolicyOrder` and `declaredSupport`
make order and support independently checkable instead of deriving either from
the table under test. -/
structure ReasonBearingInput where
  candidateDomain : List String
  temperature : ℝ
  policies : List ReasonBearingPolicy
  declaredPolicyOrder : List String
  declaredSupport : List String

/-- The old machine boundary and the distinct reason-bearing boundary. -/
inductive ReasonBearingBoundary
  | machineActionBoundary
  | reasonBearingStrategicPolicy
  deriving DecidableEq, Repr

/-- The result carrier depends on the selected boundary, allowing the old arm
to be definitionally equal to the frozen function at its original type. -/
def ReasonBearingBoundary.Output : ReasonBearingBoundary → Type
  | .machineActionBoundary => Candidate
  | .reasonBearingStrategicPolicy => ReasonBearingPolicy

/-- `ln E_S - G_S / temperature`. -/
noncomputable def policyScore (temperature : ℝ) (policy : ReasonBearingPolicy) : ℝ :=
  policy.logHabit - policy.predictedG / temperature

/-- Prefer the larger score; on equality prefer the lexicographically least
stable policy id. -/
noncomputable def betterPolicy (temperature : ℝ)
    (left right : ReasonBearingPolicy) : ReasonBearingPolicy :=
  if policyScore temperature left < policyScore temperature right then right
  else if policyScore temperature left = policyScore temperature right ∧
      right.policyId < left.policyId then right
  else left

/-- Maximum-score selection, with the tie rule built into the fold. -/
noncomputable def selectPolicy (temperature : ℝ) :
    List ReasonBearingPolicy → Option ReasonBearingPolicy
  | [] => none
  | first :: rest => some (rest.foldl (betterPolicy temperature) first)

/-- Complete input contract.  Empty domains/tables, nonpositive temperature,
incomplete policy order, support mismatch, duplicate ids, empty policies, or a
missing policy witness all fail closed. -/
def WellFormed (input : ReasonBearingInput) : Prop :=
  input.candidateDomain.Nonempty ∧
  0 < input.temperature ∧
  input.policies.Nonempty ∧
  input.policies.map (·.policyId) = input.declaredPolicyOrder ∧
  input.declaredPolicyOrder.Nodup ∧
  input.declaredSupport = input.candidateDomain ∧
  ∀ policy ∈ input.policies,
    policy.missionIds.Nonempty ∧
    (∀ mission ∈ policy.missionIds, mission ∈ input.candidateDomain) ∧
    policy.admissibilityWitness ∧ policy.supportWitness

/-- At the old boundary this delegates without inspecting the extension input.
At the new boundary invalid input is the typed `none` refusal. -/
noncomputable def reasonBearingAction
    (boundary : ReasonBearingBoundary)
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput) :
    Option boundary.Output :=
  match boundary with
  | .machineActionBoundary => machineAction .strategicRecommendation law
      fPiEntered anyHabitPrior ranked scored
  | .reasonBearingStrategicPolicy =>
      if WellFormed input then selectPolicy input.temperature input.policies else none

/-- Frozen-boundary compatibility over the full old argument list. -/
theorem machineActionBoundary_compat
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput) :
    reasonBearingAction .machineActionBoundary law fPiEntered anyHabitPrior
      ranked scored input =
    machineAction .strategicRecommendation law fPiEntered anyHabitPrior ranked scored := by
  rfl

private theorem betterPolicy_either (temperature : ℝ)
    (left right : ReasonBearingPolicy) :
    betterPolicy temperature left right = left ∨
      betterPolicy temperature left right = right := by
  simp only [betterPolicy]
  split <;> simp_all
  split <;> simp_all

private theorem fold_better_mem (temperature : ℝ) (first : ReasonBearingPolicy)
    (rest : List ReasonBearingPolicy) :
    rest.foldl (betterPolicy temperature) first ∈ first :: rest := by
  induction rest generalizing first with
  | nil => simp
  | cons next tail ih =>
      simp only [List.foldl_cons]
      have hmem := ih (betterPolicy temperature first next)
      rcases betterPolicy_either temperature first next with h | h
      · simpa [h] using hmem
      · have : betterPolicy temperature first next ∈ next :: tail := by
          simpa [h] using hmem
        exact List.mem_cons_of_mem first this

private theorem selectPolicy_some_mem {temperature : ℝ}
    {policies : List ReasonBearingPolicy} (hne : policies.Nonempty) :
    ∃ selected, selectPolicy temperature policies = some selected ∧ selected ∈ policies := by
  cases policies with
  | nil => exact (hne []).elim
  | cons first rest =>
      refine ⟨rest.foldl (betterPolicy temperature) first, rfl, ?_⟩
      exact fold_better_mem temperature first rest

/-- A well-formed input selects some declared policy whose ordered missions all
belong to the declared candidate domain. -/
theorem wellFormed_selects_declared_policy
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput)
    (h : WellFormed input) :
    ∃ selected,
      reasonBearingAction .reasonBearingStrategicPolicy law fPiEntered anyHabitPrior
        ranked scored input = some selected ∧
      selected ∈ input.policies ∧
      ∀ mission ∈ selected.missionIds, mission ∈ input.candidateDomain := by
  obtain ⟨selected, hselected, hmem⟩ := selectPolicy_some_mem h.2.2.1
  refine ⟨selected, ?_, hmem, (h.2.2.2.2.2.2 selected hmem).2.1⟩
  simp [reasonBearingAction, h, hselected]

/-- Equal scores resolve to the lexicographically least stable id. -/
theorem equalScore_tie_selects_right
    (temperature : ℝ) (left right : ReasonBearingPolicy)
    (hscore : policyScore temperature left = policyScore temperature right)
    (hid : right.policyId < left.policyId) :
    selectPolicy temperature [left, right] = some right := by
  simp [selectPolicy, betterPolicy, hscore, hid]

/-- Empty candidate domains refuse. -/
theorem emptyDomain_refuses
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput)
    (h : input.candidateDomain = []) :
    reasonBearingAction .reasonBearingStrategicPolicy law fPiEntered anyHabitPrior
      ranked scored input = none := by
  simp [reasonBearingAction, WellFormed, h]

/-- A table whose retained order is incomplete refuses. -/
theorem incompletePolicyTable_refuses
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput)
    (h : input.policies.map (·.policyId) ≠ input.declaredPolicyOrder) :
    reasonBearingAction .reasonBearingStrategicPolicy law fPiEntered anyHabitPrior
      ranked scored input = none := by
  simp [reasonBearingAction, WellFormed, h]

/-- A declared support differing from the candidate domain refuses. -/
theorem supportMismatch_refuses
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput)
    (h : input.declaredSupport ≠ input.candidateDomain) :
    reasonBearingAction .reasonBearingStrategicPolicy law fPiEntered anyHabitPrior
      ranked scored input = none := by
  simp [reasonBearingAction, WellFormed, h]

/-- Shape instantiated by packet 4d: retained identity and ordered missions
must equal the extension output at one pinned complete input. -/
def PositiveSelectionWitness
    (law : StrategicLaw) (fPiEntered anyHabitPrior : Bool)
    (ranked scored : List Candidate) (input : ReasonBearingInput)
    (retainedPolicyId : String) (retainedMissionIds : List String) : Prop :=
  WellFormed input ∧
  ∃ selected,
    reasonBearingAction .reasonBearingStrategicPolicy law fPiEntered anyHabitPrior
      ranked scored input = some selected ∧
    selected.policyId = retainedPolicyId ∧
    selected.missionIds = retainedMissionIds

#print axioms machineActionBoundary_compat
#print axioms wellFormed_selects_declared_policy
#print axioms equalScore_tie_selects_right
#print axioms emptyDomain_refuses
#print axioms incompletePolicyTable_refuses
#print axioms supportMismatch_refuses
#print axioms PositiveSelectionWitness

end DarkTower.WarMachine.ReasonBearingSelector
