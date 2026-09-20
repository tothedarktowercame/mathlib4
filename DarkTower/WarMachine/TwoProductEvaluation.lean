import DarkTower.WarMachine.MixedTokenObservation

/-!
# Two-product evaluation under a binary common cause

The A programme (futon2 `holes/labs/wm-contract/PLAN-a-programme-2026-09-20.md`,
point 3) notes that the one-common-cause observation model "permits direct
evaluation of a fully specified observation by summing two products", so some
useful queries need neither powerset enumeration nor a completed generic
compiler. This module names that fact: for a binary latent condition the
mixture likelihood at any single (state, observation) pair is exactly the
weighted sum of the two per-component product likelihoods — each of which is
`tokenLikelihood`'s per-token product. Cost: two products over the token set,
no sum over observations.

Queued-transcription item 3 of
`SPEC-a-model-conformance-2026-09-20.md`, discharged.
-/

namespace DarkTower.WarMachine.TwoProductEvaluation

open DarkTower.WarMachine.TokenObservation
open DarkTower.WarMachine.MixedTokenObservation

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- **Two-product evaluation.** Under a binary latent common cause, the
mixture likelihood of any fully specified observation is the weighted sum of
two per-component product likelihoods. -/
theorem mixtureLikelihood_bool (w : Bool → ℝ) (r : Bool → AdjudicationRates V)
    (s o : Finset V) :
    mixtureLikelihood w r s o
      = w true * tokenLikelihood (r true) s o
        + w false * tokenLikelihood (r false) s o := by
  unfold mixtureLikelihood
  rw [Fintype.sum_bool]

/-- The evaluation spelled out to its per-token factors: two products over
the token set, nothing else. -/
theorem mixtureLikelihood_bool_products (w : Bool → ℝ)
    (r : Bool → AdjudicationRates V) (s o : Finset V) :
    mixtureLikelihood w r s o
      = w true * ∏ v, (if v ∈ s then (if v ∈ o then 1 - (r true).falseNeg v
                                      else (r true).falseNeg v)
                       else (if v ∈ o then (r true).falsePos v
                             else 1 - (r true).falsePos v))
        + w false * ∏ v, (if v ∈ s then (if v ∈ o then 1 - (r false).falseNeg v
                                         else (r false).falseNeg v)
                          else (if v ∈ o then (r false).falsePos v
                                else 1 - (r false).falsePos v)) := by
  rw [mixtureLikelihood_bool]
  rfl

end DarkTower.WarMachine.TwoProductEvaluation

#print axioms DarkTower.WarMachine.TwoProductEvaluation.mixtureLikelihood_bool
#print axioms DarkTower.WarMachine.TwoProductEvaluation.mixtureLikelihood_bool_products
