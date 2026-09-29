import DarkTower.WarMachine.ScanLearning

/-!
# Model reduction for the learned scan observation model

This module states the real, q-weighted evidence calculations and the current
three-way choice rule in `futon2.aif.scan-bmr`.
-/

namespace DarkTower.WarMachine.ScanModelReduction

open scoped BigOperators
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.ScanLearning

noncomputable section

variable {O S : Type*}

/-- `scan_bmr.clj:32-34`, `evidence`: log B(prior + real nonnegative counts)
minus log B(prior). -/
def dirichletLogEvidence [Fintype O] [Nonempty O] (prior counts : O → ℝ)
    (hprior : ∀ o, 0 < prior o) (hcounts : ∀ o, 0 ≤ counts o) : ℝ :=
  logMultivariateBeta (parameters (fun o => prior o + counts o)
    (fun o => add_pos_of_pos_of_nonneg (hprior o) (hcounts o))) -
  logMultivariateBeta (parameters prior hprior)

/-- `scan_bmr.clj:81-90`: sum the status-specific Dirichlet evidence terms. -/
def scanLearnedLogEvidence [Fintype S] [Fintype O] [Nonempty O]
    (prior counts : S → O → ℝ) (hprior : ∀ s o, 0 < prior s o)
    (hcounts : ∀ s o, 0 ≤ counts s o) : ℝ :=
  ∑ s, dirichletLogEvidence (prior s) (counts s) (hprior s) (hcounts s)

/-- `scan_bmr.clj:40-41,91-93`: evidence for one status-tied row, with
uniform prior of total mass kappa and counts pooled across statuses. -/
def scanTiedLogEvidence [Fintype S] [Fintype O] [Nonempty O]
    (kappa : ℝ) (hkappa : 0 < kappa) (counts : S → O → ℝ)
    (hcounts : ∀ s o, 0 ≤ counts s o) : ℝ :=
  dirichletLogEvidence (fun _ => kappa / Fintype.card O) (fun o => ∑ s, counts s o)
    (fun _ => div_pos hkappa (by exact_mod_cast Fintype.card_pos))
    (fun o => Finset.sum_nonneg fun s _ => hcounts s o)

/-- `scan_bmr.clj:93,109-110`: scan Delta-F uses the registry sign,
log-evidence(full) minus log-evidence(reduced). -/
def scanReductionDelta (full reduced : ℝ) : ModelReductionFreeEnergyChange :=
  ⟨full - reduced⟩

/-- For one factor/status, the scan evidence difference is exactly the frozen
registry equation `modelReductionFreeEnergyChange` (`scan_bmr.clj:81-93`). -/
theorem scanReductionDelta_eq_modelReduction
    (fullPrior fullPosterior reducedPrior reducedPosterior : DirichletConcentrations) :
    scanReductionDelta
      (logMultivariateBeta fullPosterior - logMultivariateBeta fullPrior)
      (logMultivariateBeta reducedPosterior - logMultivariateBeta reducedPrior) =
      modelReductionFreeEnergyChange fullPosterior reducedPrior fullPrior reducedPosterior := by
  apply congrArg ModelReductionFreeEnergyChange.mk
  ring

/-- A point row is impossible when positive learned mass lands on an outcome
to which the hand-set row assigns probability zero (`scan_bmr.clj:60-79`). -/
structure PointImpossible (O : Type*) where
  outcome : O

/-- `scan_bmr.clj:60-79`, `point-evidence` and
`categorical-point-evidence`: exact point-model log evidence, with a typed
impossible arm rather than smoothing a zero probability. -/
def scanPointLogEvidence [Fintype O] [DecidableEq O] (counts probability : O → ℝ) :
    Except (PointImpossible O) ℝ :=
  if h : ∃ o, 0 < counts o ∧ probability o = 0 then
    .error ⟨Classical.choose h⟩
  else .ok (∑ o, counts o * Real.log (probability o))

/-- The point evidence refuses exactly for a positive count at zero
probability (`scan_bmr.clj:60-79`). -/
theorem scanPointLogEvidence_isError_iff [Fintype O] [DecidableEq O]
    (counts probability : O → ℝ) :
    (∃ e, scanPointLogEvidence counts probability = .error e) ↔
      ∃ o, 0 < counts o ∧ probability o = 0 := by
  unfold scanPointLogEvidence
  split_ifs with h
  · simp [h]
  · simp [h]

/-- The hand-set comparison arms at `scan_bmr.clj:106-110`. -/
inductive HandSetResult where
  | impossible
  | noRow
  | delta (value : ℝ)
  deriving DecidableEq

/-- The chosen model recorded by `scan_bmr.clj:122-125`. -/
inductive ScanBmrChoice where
  | tied | handSet | learned | inconclusive
  deriving DecidableEq

/-- `scan_bmr.clj:111-125`, the current three-way rule including tied
precedence and the symmetric +3 margin required to choose learned. -/
def scanBmrChoice (deltaTied : ℝ) (hand : HandSetResult) : ScanBmrChoice :=
  if deltaTied ≤ -3 then .tied
  else match hand with
    | .delta d => if d ≤ -3 then .handSet
                  else if 3 ≤ deltaTied ∧ 3 ≤ d then .learned else .inconclusive
    | .impossible => if 3 ≤ deltaTied then .learned else .inconclusive
    | .noRow => if 3 ≤ deltaTied then .learned else .inconclusive

/-- `scan_bmr.clj:126-133`: choice eligibility also requires the exposure
floor and rejects inconclusive comparisons. -/
def scanBmrEligible (floor ticks : ℕ) (choice : ScanBmrChoice) : Prop :=
  floor ≤ ticks ∧ choice ≠ .inconclusive

/-- An impossible hand-set row is evidence against that row, never adoption
of the hand-set model (`scan_bmr.clj:108,118-125`). -/
theorem impossible_handSet_ne_handSet (deltaTied : ℝ) :
    scanBmrChoice deltaTied .impossible ≠ .handSet := by
  simp only [scanBmrChoice]
  split
  · simp
  · split <;> simp

/-- Inside the open (-3,3) evidence band, with no hand-set row, the result is
inconclusive and therefore ineligible (`scan_bmr.clj:114-133`). -/
theorem middle_band_noRow_inconclusive (deltaTied : ℝ)
    (hlo : -3 < deltaTied) (hhi : deltaTied < 3) :
    scanBmrChoice deltaTied .noRow = .inconclusive ∧
      ∀ floor ticks, ¬ scanBmrEligible floor ticks (scanBmrChoice deltaTied .noRow) := by
  have hnotLow : ¬ deltaTied ≤ -3 := not_le.mpr hlo
  have hnotHigh : ¬ 3 ≤ deltaTied := not_le.mpr hhi
  simp [scanBmrChoice, hnotLow, hnotHigh, scanBmrEligible]

#print axioms scanReductionDelta_eq_modelReduction
#print axioms scanPointLogEvidence_isError_iff
#print axioms impossible_handSet_ne_handSet
#print axioms middle_band_noRow_inconclusive

end

end DarkTower.WarMachine.ScanModelReduction
