import DarkTower.AIF.Terms
import DarkTower.WarMachine.PolicySelection

/-!
# Tempered policy selection — census correction (T2, 2026-09-18)

**Correction record.** The census first cut (`Terms.lean`) bound the
policy posterior to the base law `OutcomeRiskKL.policyPosterior`
(`σ(ln E − F − G)`, book eq. 4.14 extended with habit). claude-4's T2
testimony, verified against source, showed the tree carries THREE laws:

1. base — `OutcomeRiskKL.policyWeight/policyPosterior`: `E·exp(−G−F)`, no β;
2. tempered — `PolicySelection.selectionWeight/selectionPosterior`:
   `E·exp(−γG−F)` with `γ = PolicyPrecision.policyPrecision = 1/β`
   (book B.2.4, `parr2022.txt:12720`ff: `π₀ = σ(−γG)` and the γ-tempered
   free-energy terms);
3. the census wrapper, which delegated to (1).

**Production implements (2)**: `futon2.aif.cascade-selection/
selection-posterior` cites `selectionPosterior_finite` in its own
docstring, with caller-declared β and a typed refusal on missing or
non-positive β. Both laws are theory-legitimate (eq. 4.14 base; B.2.4
tempered); a census that carries only the base law mis-scores production
as divergent when the divergence is a choice between recorded laws. This
module carries the tempered law over the census types; `Terms.lean`'s
census entry is corrected to point at both.

**Ownership of the β↔γ bridge is on record, not open:**
`Holes.lean` `policyPrecisionIsGammaFromBeta` (PERMANENT EXTERNAL
ATTESTATION, owner wm-organization, H3 from Joe's J1 ruling) requires "a
run record carrying τ together with the β it was derived from" —
production already emits `:beta {:value β :status :declared}`, and the
run-certificate lane (`Certificates.lean`, `betaDeclared`) is the
designed discharge path.
-/

namespace DarkTower.AIF

open DarkTower.WarMachine.PolicyPrecision DarkTower.WarMachine.PolicySelection

variable {P : Type*} [Fintype P]

/-- Tempered weight `E(π)·exp(−γG(π)−F(π))` over the census `Habit`,
delegating to the audited `PolicySelection.selectionWeight`;
`γ = 1/t.beta`. -/
noncomputable def temperedPolicyWeight (t : PolicyTemperature) (E : Habit P)
    (F : P → ℝ) (G : P → EReal) (π : P) : ENNReal :=
  selectionWeight t E.weight F G π

/-- Tempered posterior `σ(ln E − F − γG)` — the law production implements
(`cascade-selection/selection-posterior`). -/
noncomputable def temperedPolicyPosterior (t : PolicyTemperature) (E : Habit P)
    (F : P → ℝ) (G : P → EReal) (π : P) : ENNReal :=
  selectionPosterior t E.weight F G π

theorem temperedPolicyPosterior_def (t : PolicyTemperature) (E : Habit P)
    (F : P → ℝ) (G : P → EReal) (π : P) :
    temperedPolicyPosterior t E F G π =
      selectionPosterior t E.weight F G π := rfl

/-- At `β = 1` (so `γ = 1`) the tempered weight is the base law's weight:
the two recorded laws agree exactly there, which is why a census carrying
only one of them could pass every β=1 fixture while mis-binding
production. -/
theorem temperedPolicyWeight_beta_one (E : Habit P) (F : P → ℝ)
    (G : P → EReal) (π : P) :
    temperedPolicyWeight ⟨1, one_pos⟩ E F G π =
      DarkTower.WarMachine.OutcomeRiskKL.policyWeight E.weight F G π := by
  simp [temperedPolicyWeight, selectionWeight, policyPrecision,
    DarkTower.WarMachine.OutcomeRiskKL.policyWeight]

end DarkTower.AIF
