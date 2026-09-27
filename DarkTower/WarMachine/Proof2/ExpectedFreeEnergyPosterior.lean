import DarkTower.WarMachine.MachineQ
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

/-!
# The policy posterior supplied with the machine's expected free energy (P-inst-G)

The source is `MachineQ.machineExpectedFreeEnergy`, including its predictive
reading, preference distribution and explicit positive-preference obligation.
This composition does not replace absent readings or preferences with defaults.
The source is real-valued: its coercion is always finite, so this supply cannot
exercise the consumer's infinite-G arm. The consumer's temperature and F
absences are retained verbatim. Its existing registry placement stays in place;
this sibling composition supplies the missing R5 → R6 import.
-/

namespace DarkTower.WarMachine.Proof2.ExpectedFreeEnergyPosterior

open DarkTower.WarMachine Holes MachineQ
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {Obs : Vertex → Type*} {State Action PolicyIndex : Type*}
variable (model : GenerativeModel Obs State Action PolicyIndex)
    (reading : QReading model) (belief : BeliefState)
    (Cdist : PreferenceDistribution Obs)
    (positivePreference : ∀ π o,
      o ∈ (machinePredictiveOutcomeKernel model reading belief).support π →
        0 < Cdist.mass () o)

/-- The actual machine G, embedded without changing its value. -/
def machineG (π : PolicyIndex) : EReal :=
  ((machineExpectedFreeEnergy model reading belief Cdist positivePreference π).value : EReal)

/-- The existing consumer instantiated at the source declaration, not a free G. -/
def machinePosteriorAtG (habit : PolicyIndex → ℝ) (F : PolicyIndex → EReal)
    (opts : MachineTemperature.TemperatureOpts) (policies : List PolicyIndex) :
    Except (Absence PolicyIndex) (List ℝ) :=
  machinePosteriorE habit (machineG model reading belief Cdist positivePreference) F opts policies

theorem machinePosteriorAtG_eq (habit : PolicyIndex → ℝ) (F : PolicyIndex → EReal)
    (opts : MachineTemperature.TemperatureOpts) (policies : List PolicyIndex) :
    machinePosteriorAtG model reading belief Cdist positivePreference habit F opts policies =
      machinePosteriorE habit
        (fun π => ((machineExpectedFreeEnergy model reading belief Cdist positivePreference π).value : EReal))
        F opts policies := rfl

/-- The source's finiteness is a property of its type, not an infinite-G default. -/
theorem machineG_finite (π : PolicyIndex) :
    machineG model reading belief Cdist positivePreference π ≠ ⊤ ∧
    machineG model reading belief Cdist positivePreference π ≠ ⊥ := by
  simp [machineG]

/-- Every consumer refusal survives the composition with exactly the same payload. -/
theorem refusal_preserved (habit : PolicyIndex → ℝ) (F : PolicyIndex → EReal)
    (opts : MachineTemperature.TemperatureOpts) (policies : List PolicyIndex)
    (a : Absence PolicyIndex)
    (h : machinePosteriorE habit (machineG model reading belief Cdist positivePreference)
      F opts policies = .error a) :
    machinePosteriorAtG model reading belief Cdist positivePreference habit F opts policies =
      .error a := h

/-- Negative control at the actual source: different preference readings which
change machine G change the consumer's unnormalised weight at positive τ.
This does not assert that a common additive shift changes normalised weights. -/
theorem changed_source_changes_weight
    (Cdist' : PreferenceDistribution Obs)
    (positivePreference' : ∀ π o,
      o ∈ (machinePredictiveOutcomeKernel model reading belief).support π →
        0 < Cdist'.mass () o)
    (habit : PolicyIndex → ℝ) (F : PolicyIndex → EReal) (tau : ℝ) (htau : 0 < tau)
    (π : PolicyIndex)
    (hG : (machineExpectedFreeEnergy model reading belief Cdist positivePreference π).value ≠
      (machineExpectedFreeEnergy model reading belief Cdist' positivePreference' π).value) :
    weightE habit (machineG model reading belief Cdist positivePreference) F tau π ≠
      weightE habit (machineG model reading belief Cdist' positivePreference') F tau π := by
  intro h
  unfold weightE at h
  have he := Real.exp_injective h
  simp only [machineG, EReal.toReal_coe] at he
  apply hG
  have hd : (machineExpectedFreeEnergy model reading belief Cdist positivePreference π).value / tau =
      (machineExpectedFreeEnergy model reading belief Cdist' positivePreference' π).value / tau := by
    linarith
  have hm := (div_eq_div_iff htau.ne' htau.ne').mp hd
  nlinarith

/-- Concrete consumer bad case: changing just one policy's finite G from zero
 to ln 3 changes the normalised weights from halves to quarters/three quarters.
 Together with `changed_source_changes_weight`, this distinguishes actual source
 sensitivity from the false claim that every change of G changes the posterior. -/
theorem different_G_changes_normalised_weights :
    machineWeightsE (fun _ : Bool => 1) (fun _ => 0) (fun _ => 0) 1 [true, false] =
      [(1 / 2 : ℝ), 1 / 2] ∧
    machineWeightsE (fun _ : Bool => 1)
      (fun b => if b then ((Real.log 3 : ℝ) : EReal) else 0)
      (fun _ => 0) 1 [true, false] = [(1 / 4 : ℝ), 3 / 4] := by
  norm_num [machineWeightsE, normaliserE, finiteTermPolicies, FiniteTerms, FiniteF,
    weightE, Real.exp_neg, Real.exp_log (by norm_num : (0 : ℝ) < 3)]

#print axioms machineG
#print axioms machinePosteriorAtG
#print axioms different_G_changes_normalised_weights

#print axioms machinePosteriorAtG_eq
#print axioms machineG_finite
#print axioms refusal_preserved
#print axioms changed_source_changes_weight

end
end DarkTower.WarMachine.Proof2.ExpectedFreeEnergyPosterior
