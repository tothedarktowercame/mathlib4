import DarkTower.WarMachine.ObservationProcess
import DarkTower.WarMachine.Proof2.ActionAtMachine

/-!
# The observation law after the machine's own action (W3, registry `:observe`, R16→R2)

`ObservationProcess.observationAfter M w u o` is the process's probability
`P(o | s_{t−1} = w, u)`, with the action `u` and the world `w` as free arguments.
Nothing in Lean supplied the MACHINE's action (W2, `ActionAtMachine.machineAction`)
to it. `machineObservationLaw` does: the machine's action, and the process's law for
it from the world. An absent action gives no law.

`observationAfter` is a probability, not an observation. The observation itself is a
realised draw that no function here produces; `BeliefAtMachine` takes it as an input
and checks it against this law.
-/

namespace DarkTower.WarMachine.Proof2.ObservationAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.PolicyRollout
open DarkTower.WarMachine.ObservationProcess
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine
open DarkTower.WarMachine.Proof2.ActionAtMachine

noncomputable section

variable {S O U PolicyIndex : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- Everything `machineAction` reads, at one moment. -/
structure PolicyInputs (PolicyIndex U : Type*) where
  habit : PolicyIndex → ℝ
  grade : PolicyIndex → Holes.ExpectedFreeEnergyValue
  F : PolicyIndex → EReal
  opts : MachineTemperature.TemperatureOpts
  policies : List PolicyIndex
  head : PolicyIndex → U

/-- The machine's action at these inputs: W2's `machineAction`. -/
def actionAt [LinearOrder U] (I : PolicyInputs PolicyIndex U) :
    Except (Absence PolicyIndex) U :=
  machineAction I.habit I.grade I.F I.opts I.policies I.head

/-- **The observation law after the machine's action.** The machine's action `u` and
the process's distribution `o ↦ P(o | world, u)` for it: `u` and the world into
`observationAfter` (R16→R2). An absent action gives no law. -/
def machineObservationLaw [LinearOrder U] (M : ForwardModel S O U)
    (I : PolicyInputs PolicyIndex U) (world : S) :
    Except (Absence PolicyIndex) (U × (O → ℝ)) :=
  match actionAt I with
  | .error a => .error a
  | .ok u => .ok (u, observationAfter M world u)

variable [LinearOrder U]

/-- With an ok action the law is the process's own, at that action. -/
theorem machineObservationLaw_ok (M : ForwardModel S O U)
    (I : PolicyInputs PolicyIndex U) (world : S) (u : U)
    (h : actionAt I = .ok u) :
    machineObservationLaw M I world = .ok (u, observationAfter M world u) := by
  simp [machineObservationLaw, h]

/-- An absent action gives an absent law, with the posterior's own absence. -/
theorem machineObservationLaw_absent (M : ForwardModel S O U)
    (I : PolicyInputs PolicyIndex U) (world : S) (a : Absence PolicyIndex)
    (h : actionAt I = .error a) :
    machineObservationLaw M I world = .error a := by
  simp [machineObservationLaw, h]

/-- **Each law is a distribution over observations.** -/
theorem machineObservationLaw_isDistribution (M : ForwardModel S O U)
    (I : PolicyInputs PolicyIndex U) (world : S) (u : U) (law : O → ℝ)
    (h : machineObservationLaw M I world = .ok (u, law)) :
    (∀ o, 0 ≤ law o) ∧ ∑ o, law o = 1 := by
  unfold machineObservationLaw at h
  cases ha : actionAt I with
  | error a => simp [ha] at h
  | ok v =>
    simp only [ha, Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_, rfl⟩ := h
    exact ⟨observationAfter_nonneg M world v, observationAfter_sum M world v⟩

end

#print axioms PolicyInputs
#print axioms actionAt
#print axioms machineObservationLaw
#print axioms machineObservationLaw_ok
#print axioms machineObservationLaw_absent
#print axioms machineObservationLaw_isDistribution

end DarkTower.WarMachine.Proof2.ObservationAtMachine
