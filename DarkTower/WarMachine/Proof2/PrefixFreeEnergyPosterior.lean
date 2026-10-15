import DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

/-!
# W1b's weights at the executed-prefix free energy ([R8 R6])

This module composes the machine's executed-prefix F with its policy weights.
It is a sibling of the prefix and posterior modules: the posterior cannot
import the prefix module, because the prefix already reaches the posterior
through ObservationAtMachine → ActionAtMachine → PolicyPosteriorAtMachine
(W11-D §2). No policy carrier is rebound here.
-/

set_option linter.unusedSectionVars false

namespace DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior

open DarkTower.WarMachine
open DarkTower.WarMachine.Proof2.CascadePolicySet (PolicyKey)
open DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {M P S O : Type*} [DecidableEq M] [DecidableEq P] [Fintype S] [DecidableEq S]

/-! ## F into the posterior -/

section FPosterior

open Classical

/-- Why there are no posterior weights at the prefix F. -/
inductive PrefixWeightsAbsence (M P : Type*) where
  | notSupplied (π : PolicyKey M P)

/-- **The machine's posterior weights with `F` the observed-prefix free energy.**
`machineWeights` (W1/W1b) with `F π := prefixF π (steps π)`, `⊤` at a contradiction (weight
`0`). A policy on the menu with NO admitted history has no `F` and the weights are absent,
naming it: no `0` is stood in. -/
def machineWeightsAtPrefixF (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) : Except (PrefixWeightsAbsence M P) (List ℝ) :=
  match policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => .error (.notSupplied π)
  | none =>
    .ok (machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies)

/-- **The composition.** On the ok arm every menu policy has an admitted history or a
contradiction, and the weights are `machineWeights` at that `F`. -/
theorem machineWeightsAtPrefixF_eq (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    (∀ π ∈ policies, prefixF π (steps π) ≠ .error .noAdmittedSteps) ∧
    ws = machineWeights habit grade
      (fun π => match prefixF π (steps π) with | .ok f => f | .error _ => ⊤) tau policies := by
  unfold machineWeightsAtPrefixF at h
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    refine ⟨fun π hπ hπ' => ?_, (Except.ok.inj h).symm⟩
    have := List.find?_eq_none.mp hf π hπ
    simp [hπ'] at this

/-- **A policy with no admitted history makes the weights absent**, naming a policy: reachable,
and no `F = 0` is stood in. -/
theorem notSuppliedIsAbsence (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (π : PolicyKey M P) (hπ : π ∈ policies)
    (hn : prefixF π (steps π) = .error .noAdmittedSteps) :
    ∃ π', machineWeightsAtPrefixF habit grade steps tau policies = .error (.notSupplied π') := by
  unfold machineWeightsAtPrefixF
  cases hf : policies.find? (fun π => decide (prefixF π (steps π) = .error .noAdmittedSteps)) with
  | some π' => exact ⟨π', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf π hπ
    simp [hn] at this

/-- **A policy whose prefix ended in a contradiction has weight zero.** `F = ⊤`, so W1b's
`infiniteFHasZeroWeight` applies: the code's `:zero-support`. -/
theorem contradictionHasZeroWeight (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (steps : PolicyKey M P → List (Step M P S O)) (tau : ℝ)
    (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtPrefixF habit grade steps tau policies = .ok ws) :
    ∀ p ∈ policies.zip ws, prefixF p.1 (steps p.1) = .error .contradiction → p.2 = 0 := by
  obtain ⟨_, rfl⟩ := machineWeightsAtPrefixF_eq habit grade steps tau policies ws h
  intro p hp hc
  refine infiniteFHasZeroWeight habit grade _ tau policies p hp ?_
  intro hfin
  simp [FiniteF, hc] at hfin

end FPosterior

/-! ## Certified zero history (codex-68 ruling, 2026-10-15)

Missing history and proven-empty history are different findings. `machineWeightsAtPrefixF`
reads a policy's steps and refuses a policy with none. Here the steps come from ONE
authoritative ledger, the run's pinned census of every recorded step, and `complete` says
that census was read in full (every record read, every enactment attributed). When the
complete ledger records no step of `π`, the historical prefix term is outside its domain:
`π` has a positive applicability proof and the posterior omits its `F`. Without that proof an
empty prefix is still `.notSupplied`, and a policy with recorded steps but no admitted prefix
is still an error: certification never applies to it. -/

section Applicability

open Classical

/-- `π`'s recorded history in the authoritative ledger, in ledger order. -/
def historyOf (ledger : List (Step M P S O)) (π : PolicyKey M P) : List (Step M P S O) :=
  ledger.filter (fun s => decide (s.policy = π))

/-- The positive applicability proof: the ledger is the complete census and records no step
of `π`. -/
structure CertifiedZeroHistory (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) : Prop where
  complete : complete = true
  noStep : historyOf ledger π = []

/-- How a policy's historical prefix term enters the posterior. -/
inductive PrefixApplicability where
  /-- The admitted-prefix `F` (`⊤` at a contradiction). -/
  | computed (f : EReal)
  /-- Certified zero history: the term is outside its domain and is omitted. -/
  | notApplicable

/-- The applicability of `π`'s historical prefix term, or the absence that refuses the menu. -/
def prefixApplicability (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) : Except (PrefixWeightsAbsence M P) PrefixApplicability :=
  if complete = true ∧ historyOf ledger π = [] then .ok .notApplicable
  else
    match prefixF π (historyOf ledger π) with
    | .ok f => .ok (.computed f)
    | .error .contradiction => .ok (.computed ⊤)
    | .error .noAdmittedSteps => .error (.notSupplied π)

/-- The `F` the posterior consumes: the computed prefix `F`, or no term (`0` in the exponent)
when the term is not applicable. -/
def consumedF : PrefixApplicability → EReal
  | .computed f => f
  | .notApplicable => 0

/-- `F` at each policy as the weights read it; an absent policy never reaches the weights. -/
def applicabilityF (complete : Bool) (ledger : List (Step M P S O)) (π : PolicyKey M P) :
    EReal :=
  match prefixApplicability complete ledger π with
  | .ok a => consumedF a
  | .error _ => ⊤

/-- Whether `π`'s prefix term refuses the menu. -/
def refusesMenu (complete : Bool) (ledger : List (Step M P S O)) (π : PolicyKey M P) : Bool :=
  match prefixApplicability complete ledger π with
  | .ok _ => false
  | .error _ => true

/-- **The weights at the authoritative ledger.** Absent, naming a policy, when any menu
policy's term is not supplied; otherwise `machineWeights` with each policy's computed `F`, or
with its `F` omitted when certified as never run. -/
def machineWeightsAtApplicability (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (complete : Bool)
    (ledger : List (Step M P S O)) (tau : ℝ) (policies : List (PolicyKey M P)) :
    Except (PrefixWeightsAbsence M P) (List ℝ) :=
  match policies.find? (refusesMenu complete ledger) with
  | some π => .error (.notSupplied π)
  | none => .ok (machineWeights habit grade (applicabilityF complete ledger) tau policies)

/-- **Certified zero history is the positive applicability proof.** -/
theorem certified_isNotApplicable (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) (h : CertifiedZeroHistory complete ledger π) :
    prefixApplicability complete ledger π = .ok .notApplicable := by
  simp [prefixApplicability, h.complete, h.noStep]

/-- **Only certified zero history is not applicable.** -/
theorem notApplicable_iff (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) :
    prefixApplicability complete ledger π = .ok .notApplicable ↔
      CertifiedZeroHistory complete ledger π := by
  constructor
  · intro h
    unfold prefixApplicability at h
    by_cases hc : complete = true ∧ historyOf ledger π = []
    · exact ⟨hc.1, hc.2⟩
    · rw [if_neg hc] at h
      split at h <;> cases h
  · exact certified_isNotApplicable complete ledger π

/-- **Certification is not `.notSupplied`.** -/
theorem certified_ne_notSupplied (complete : Bool) (ledger : List (Step M P S O))
    (π π' : PolicyKey M P) (h : CertifiedZeroHistory complete ledger π) :
    prefixApplicability complete ledger π ≠ .error (.notSupplied π') := by
  rw [certified_isNotApplicable complete ledger π h]
  intro h'; cases h'

/-- **Unknown history stays an error.** An empty history from an incomplete ledger is not a
proof of zero history. -/
theorem incompleteEmpty_isNotSupplied (ledger : List (Step M P S O)) (π : PolicyKey M P)
    (hn : historyOf ledger π = []) :
    prefixApplicability false ledger π = .error (.notSupplied π) := by
  simp [prefixApplicability, hn, prefixF_nil]

/-- **Recorded history without an admitted prefix stays an error**, complete ledger or not:
certification never applies to a policy the ledger records. -/
theorem recordedWithoutF_isNotSupplied (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) (hr : historyOf ledger π ≠ [])
    (hf : prefixF π (historyOf ledger π) = .error .noAdmittedSteps) :
    prefixApplicability complete ledger π = .error (.notSupplied π) := by
  simp [prefixApplicability, hr, hf]

/-- **Recorded history keeps its computed `F`.** -/
theorem recorded_isComputed (complete : Bool) (ledger : List (Step M P S O))
    (π : PolicyKey M P) (hr : historyOf ledger π ≠ []) (f : EReal)
    (hf : prefixF π (historyOf ledger π) = .ok f) :
    prefixApplicability complete ledger π = .ok (.computed f) := by
  simp [prefixApplicability, hr, hf]

/-- **The omitted term.** A certified policy's weight is `exp (ln E − G/τ)`: no `F` term. -/
theorem certified_weight_omitsF (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (complete : Bool)
    (ledger : List (Step M P S O)) (tau : ℝ) (π : PolicyKey M P)
    (h : CertifiedZeroHistory complete ledger π) :
    weight habit grade (applicabilityF complete ledger) tau π =
      Real.exp (Real.log (habit π) - (grade π).value / tau) := by
  simp [weight, applicabilityF, certified_isNotApplicable complete ledger π h, consumedF]

/-- **A not-supplied menu policy makes the weights absent.** -/
theorem applicability_notSupplied_isAbsence (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (complete : Bool)
    (ledger : List (Step M P S O)) (tau : ℝ) (policies : List (PolicyKey M P))
    (π : PolicyKey M P) (hπ : π ∈ policies)
    (hn : prefixApplicability complete ledger π = .error (.notSupplied π)) :
    ∃ π', machineWeightsAtApplicability habit grade complete ledger tau policies =
      .error (.notSupplied π') := by
  unfold machineWeightsAtApplicability
  cases hf : policies.find? (refusesMenu complete ledger) with
  | some π' => exact ⟨π', rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf π hπ
    simp [refusesMenu, hn] at this

/-- **On the ok arm** no menu policy refuses, and the weights are `machineWeights` at the
consumed `F`. -/
theorem machineWeightsAtApplicability_eq (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue) (complete : Bool)
    (ledger : List (Step M P S O)) (tau : ℝ) (policies : List (PolicyKey M P)) (ws : List ℝ)
    (h : machineWeightsAtApplicability habit grade complete ledger tau policies = .ok ws) :
    (∀ π ∈ policies, refusesMenu complete ledger π = false) ∧
    ws = machineWeights habit grade (applicabilityF complete ledger) tau policies := by
  unfold machineWeightsAtApplicability at h
  cases hf : policies.find? (refusesMenu complete ledger) with
  | some π => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    refine ⟨fun π hπ => ?_, (Except.ok.inj h).symm⟩
    have := List.find?_eq_none.mp hf π hπ
    simpa using this

end Applicability

end

#print axioms machineWeightsAtPrefixF
#print axioms machineWeightsAtPrefixF_eq
#print axioms notSuppliedIsAbsence
#print axioms contradictionHasZeroWeight
#print axioms certified_isNotApplicable
#print axioms notApplicable_iff
#print axioms certified_ne_notSupplied
#print axioms incompleteEmpty_isNotSupplied
#print axioms recordedWithoutF_isNotSupplied
#print axioms recorded_isComputed
#print axioms certified_weight_omitsF
#print axioms applicability_notSupplied_isAbsence
#print axioms machineWeightsAtApplicability_eq

end DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior
