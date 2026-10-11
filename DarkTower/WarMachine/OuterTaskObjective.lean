import DarkTower.WarMachine.IncrementalTaskFrontier
import Mathlib.Tactic

/-!
# A pinned outer-task objective

This is the objective seam *before* any target-local cascade exists.  It is
not cascade-policy `G`: channel meanings, observations, and their aggregation
are caller-declared parameters.  The certificate binds that declaration and
its exact inputs to the stable comparison key stored in the incremental task
frontier.
-/

namespace DarkTower.WarMachine.OuterTaskObjective

open DarkTower.WarMachine.IncrementalTaskFrontier

abbrev Id := IncrementalTaskFrontier.Id

structure ChannelObservation where
  channel : Id
  observation : Id
  evidence : Id
  valueDigest : Id
  deriving DecidableEq

/-- Identity/version and evaluator are declared together.  No weights or
channel semantics are selected by this model. -/
structure Objective where
  identity : Id
  version : Nat
  registrationToken : Id
  authority : Id
  evaluate : List ChannelObservation → Nat

/-- External authorization binds labels to the evaluator itself. -/
structure ObjectiveRegistration where
  identity : Id
  version : Nat
  registrationToken : Id
  authority : Id
  evaluate : List ChannelObservation → Nat

def Authorized (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) : Prop :=
  ∃ registration ∈ registry,
    registration.identity = objective.identity ∧
    registration.version = objective.version ∧
    registration.registrationToken = objective.registrationToken ∧
    registration.authority = objective.authority ∧
    registration.evaluate = objective.evaluate ∧
    registration.authority ≠ selectorAuthority

structure TaskInput where
  task : Id
  channels : List ChannelObservation
  dependencies : Finset Id
  freshnessEpoch : Nat
  deriving DecidableEq

structure EvaluationCertificate where
  input : TaskInput
  objectiveIdentity : Id
  objectiveVersion : Nat
  entry : Entry
  deriving DecidableEq

def channelDependencies (channel : ChannelObservation) : Finset Id :=
  {channel.channel, channel.observation, channel.evidence, channel.valueDigest}

/-- Exact invalidation closure: objective registration and every identity that
can change the evaluator input. -/
def requiredDependencies (objective : Objective) (input : TaskInput) : Finset Id :=
  input.channels.foldl (fun dependencies channel =>
    dependencies ∪ channelDependencies channel) {objective.registrationToken}

def EvaluationCertificate.Valid (registry : List ObjectiveRegistration)
    (selectorAuthority : Id) (objective : Objective)
    (c : EvaluationCertificate) : Prop :=
  Authorized registry selectorAuthority objective ∧
  (c.input.channels.map (·.channel)).Nodup ∧
  c.objectiveIdentity = objective.identity ∧
  c.objectiveVersion = objective.version ∧
  c.entry.task = c.input.task ∧
  c.entry.rankingLaw = objective.identity ∧
  c.entry.rankingVersion = objective.version ∧
  c.input.dependencies = requiredDependencies objective c.input ∧
  c.entry.dependencies = c.input.dependencies ∧
  c.entry.freshnessEpoch = c.input.freshnessEpoch ∧
  c.entry.comparisonKey = objective.evaluate c.input.channels ∧
  c.entry.observation = c.input.channels.foldl
    (fun digest x => digest + x.observation + x.valueDigest) 0 ∧
  c.entry.evidence = c.input.channels.foldl
    (fun digest x => digest + x.evidence) 0

/-- One certificate per current entry, in the same order. -/
structure FrontierCertificate where
  refresh : RefreshCertificate
  evaluations : List EvaluationCertificate
  deriving DecidableEq

def FrontierCertificate.Valid (registry : List ObjectiveRegistration)
    (selectorAuthority : Id) (objective : Objective)
    (c : FrontierCertificate) : Prop :=
  c.refresh.Valid ∧
  c.evaluations.map (·.entry) = c.refresh.current ∧
  allIn c.evaluations (EvaluationCertificate.Valid registry selectorAuthority objective)

def objectiveLE (a b : EvaluationCertificate) : Prop :=
  a.entry.comparisonKey < b.entry.comparisonKey ∨
    (a.entry.comparisonKey = b.entry.comparisonKey ∧ a.entry.task ≤ b.entry.task)

instance (a b : EvaluationCertificate) : Decidable (objectiveLE a b) := by
  unfold objectiveLE
  infer_instance

structure SelectionCertificate where
  selected : EvaluationCertificate
  deriving DecidableEq

def SelectionCertificate.Valid (registry : List ObjectiveRegistration)
    (selectorAuthority : Id) (objective : Objective)
    (frontier : FrontierCertificate) (s : SelectionCertificate) : Prop :=
  frontier.Valid registry selectorAuthority objective ∧
  s.selected ∈ frontier.evaluations ∧
  allIn frontier.evaluations (objectiveLE s.selected)

/-- A valid selection is the deterministic minimum under declared objective
value, with stable task identity as the tie law. -/
theorem selected_is_minimum (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) (frontier : FrontierCertificate)
    (selection : SelectionCertificate)
    (h : selection.Valid registry selectorAuthority objective frontier)
    (candidate : EvaluationCertificate) (hc : candidate ∈ frontier.evaluations) :
    objectiveLE selection.selected candidate := by
  exact h.2.2 candidate hc

theorem selected_belongs_to_fully_refreshed_frontier
    (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) (frontier : FrontierCertificate)
    (selection : SelectionCertificate)
    (h : selection.Valid registry selectorAuthority objective frontier) :
    selection.selected.entry ∈ frontier.refresh.current := by
  rw [← h.1.2.1]
  exact List.mem_map.mpr ⟨selection.selected, h.2.1, rfl⟩

/-- Retention needs no global reindexing: when the dependency closure is
unchanged, strict refresh preserves the entire prior entry, including its
objective identity/version and comparison key. -/
theorem retained_objective_entry_is_identical
    (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) (frontier : FrontierCertificate) (entry : Entry)
    (h : frontier.Valid registry selectorAuthority objective)
    (he : entry ∈ frontier.refresh.retained) :
    entry ∈ frontier.refresh.prior ∧ entry ∈ frontier.refresh.current ∧
      ∃ evaluation ∈ frontier.evaluations,
        evaluation.entry = entry ∧
        evaluation.objectiveIdentity = objective.identity ∧
        evaluation.objectiveVersion = objective.version ∧
        evaluation.entry.comparisonKey = objective.evaluate evaluation.input.channels := by
  have hp := unchanged_disjoint_entry_retained_identically
    frontier.refresh entry h.1 he
  have hm : entry ∈ frontier.evaluations.map (·.entry) := by
    rw [h.2.1]
    exact hp.2
  obtain ⟨evaluation, hevaluation, rfl⟩ := List.mem_map.mp hm
  have hv := h.2.2 evaluation hevaluation
  rcases hv with ⟨_, _, hid, hver, _, _, _, _, _, _, hkey, _, _⟩
  exact ⟨hp.1, hp.2, evaluation, hevaluation, rfl, hid, hver, hkey⟩

/-- An affected entry cannot survive as retained evidence under any objective. -/
theorem affected_objective_entry_must_be_recomputed
    (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) (frontier : FrontierCertificate) (entry : Entry)
    (h : frontier.Valid registry selectorAuthority objective)
    (he : entry ∈ frontier.refresh.invalidated) :
    entry.task ∈ taskSet frontier.refresh.recomputed :=
  invalidated_task_cannot_be_omitted frontier.refresh entry h.1 he

/-- Substituting an objective identity invalidates an evaluation even if the
numeric score happens to remain equal. -/
theorem objective_substitution_invalid
    (registry : List ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective) (c : EvaluationCertificate)
    (h : c.objectiveIdentity ≠ objective.identity) :
    ¬ c.Valid registry selectorAuthority objective := by
  intro hv
  exact h hv.2.2.1

theorem evaluator_substitution_invalid
    (registration : ObjectiveRegistration) (selectorAuthority : Id)
    (objective : Objective)
    (hsubstituted : registration.evaluate ≠ objective.evaluate) :
    ¬ Authorized [registration] selectorAuthority objective := by
  intro h
  rcases h with ⟨candidate, hc, _, _, _, _, heval, _⟩
  simp only [List.mem_singleton] at hc
  subst candidate
  exact hsubstituted heval

/-! Closed witnesses: declared channel semantics remain arbitrary. -/

def witnessObjective : Objective where
  identity := 70
  version := 2
  registrationToken := 700
  authority := 8
  evaluate := fun xs => xs.foldl (fun n x => n + x.valueDigest) 0

def witnessRegistration : ObjectiveRegistration where
  identity := 70
  version := 2
  registrationToken := 700
  authority := 8
  evaluate := witnessObjective.evaluate

def witnessInput (task value : Nat) : TaskInput where
  task := task
  channels := [⟨1, task + 10, task + 20, value⟩]
  dependencies := requiredDependencies witnessObjective
    { task := task
      channels := [⟨1, task + 10, task + 20, value⟩]
      dependencies := ∅
      freshnessEpoch := 4 }
  freshnessEpoch := 4

def witnessEvaluation (task value : Nat) : EvaluationCertificate where
  input := witnessInput task value
  objectiveIdentity := 70
  objectiveVersion := 2
  entry := ⟨task, task + 10 + value, task + 20, 70, 2,
    (witnessInput task value).dependencies, value, 4⟩

theorem witnessEvaluation_valid (task value : Nat) :
    (witnessEvaluation task value).Valid [witnessRegistration] 9 witnessObjective := by
  simp [EvaluationCertificate.Valid, Authorized, witnessRegistration, witnessEvaluation,
    witnessInput, witnessObjective, requiredDependencies, channelDependencies]

theorem tie_breaks_by_stable_task_identity :
    objectiveLE (witnessEvaluation 1 5) (witnessEvaluation 2 5) := by
  simp [objectiveLE, witnessEvaluation]

def substitutedWitness : EvaluationCertificate :=
  { witnessEvaluation 1 5 with objectiveIdentity := 71 }

theorem substitutedWitness_invalid :
    ¬ substitutedWitness.Valid [witnessRegistration] 9 witnessObjective := by
  exact objective_substitution_invalid [witnessRegistration] 9 witnessObjective
    substitutedWitness (by decide)

def omittedDependencyWitness : EvaluationCertificate :=
  { witnessEvaluation 1 5 with
    input := { witnessInput 1 6 with dependencies := ∅ }
    entry := { (witnessEvaluation 1 5).entry with dependencies := ∅ } }

theorem changed_channel_with_omitted_dependencies_invalid :
    ¬ omittedDependencyWitness.Valid [witnessRegistration] 9 witnessObjective := by
  intro h
  rcases h with ⟨_, _, _, _, _, _, _, hdeps, _⟩
  have htoken : witnessObjective.registrationToken ∈
      requiredDependencies witnessObjective omittedDependencyWitness.input := by
    simp [requiredDependencies, omittedDependencyWitness, witnessInput,
      channelDependencies, witnessObjective]
  rw [← hdeps] at htoken
  simpa [omittedDependencyWitness] using htoken

def duplicateChannelWitness : EvaluationCertificate :=
  { witnessEvaluation 1 5 with
    input := { witnessInput 1 5 with
      channels := (witnessInput 1 5).channels ++ (witnessInput 1 5).channels } }

theorem duplicate_channel_identity_invalid :
    ¬ duplicateChannelWitness.Valid [witnessRegistration] 9 witnessObjective := by
  intro h
  simpa [duplicateChannelWitness, witnessInput] using h.2.1

end DarkTower.WarMachine.OuterTaskObjective
