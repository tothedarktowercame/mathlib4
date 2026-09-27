import DarkTower.WarMachine.Proof2.ChannelIdentity
import DarkTower.WarMachine.Proof2.KernelAtCounts

/-! Production A-S Revision 3: both reference cells must contain >=5 labels;
the explicitly authorised Jeffreys prior supplies the posterior mean. C6 filters
full check identity before counting. Records are validated unique store labels.
Raw counts remain a separate specialisation, not the current production rates. -/
namespace DarkTower.WarMachine.Proof2.Revision3Rates
open AdjudicationCounts ChannelIdentity KernelAtCounts
open DarkTower.WarMachine.TokenObservation
variable {κ V : Type*} [DecidableEq κ]
def denominator (c : κ) (k : TruthKind) (rs : List (Record κ V)) : ℕ :=
  (paired c k rs).length
def numerator (c : κ) (k : TruthKind) (rs : List (Record κ V)) : ℕ :=
  ((paired c k rs).filter fun r => k.isError r.recorded).length
def eligible (c : κ) (rs : List (Record κ V)) : Prop :=
  5 ≤ denominator c .falseNeg rs ∧ 5 ≤ denominator c .falsePos rs
instance (c : κ) (rs : List (Record κ V)) : Decidable (eligible c rs) :=
  inferInstanceAs (Decidable (_ ∧ _))
def jeffreys (n d : ℕ) : ℚ := ((n : ℚ) + 1/2) / ((d : ℚ) + 1)
theorem jeffreys_strict_bounds (n d : ℕ) (h : n ≤ d) :
    0 < jeffreys n d ∧ jeffreys n d < 1 := by
  have hn : (0 : ℚ) ≤ n := Nat.cast_nonneg n
  have hd : (0 : ℚ) ≤ d := Nat.cast_nonneg d
  have hnd : (n : ℚ) ≤ d := by exact_mod_cast h
  constructor
  · exact div_pos (by linarith) (by linarith)
  · apply (div_lt_one (by linarith : (0 : ℚ) < (d : ℚ) + 1)).2
    linarith
def estimate (c : κ) (k : TruthKind) (rs : List (Record κ V)) : ℚ :=
  jeffreys (numerator c k rs) (denominator c k rs)
theorem estimate_bounds (c : κ) (k : TruthKind) (rs : List (Record κ V)) :
    0 < estimate c k rs ∧ estimate c k rs < 1 :=
  jeffreys_strict_bounds _ _ (List.length_filter_le _ _)
/-- The reader excludes BOTH cells before kernelSupply sees an ineligible class. -/
def supply (c : κ) (kind : ClassKind) (rs : List (Record κ V)) : Supply :=
  if eligible c rs then .measured (estimate c .falseNeg rs) (estimate c .falsePos rs)
  else kernelSupply kind .unobserved .unobserved
theorem excludedCheckableIsAbsent (c : κ) (rs : List (Record κ V))
    (h : ¬ eligible c rs) : supply c .checkable rs = .zeroKernelAssumed := by
  simp [supply, h, kernelSupply, Cell.rate]
theorem excludedJudgementRefuses (c : κ) (rs : List (Record κ V))
    (h : ¬ eligible c rs) : supply c .judgement rs = .unsupported := by
  simp [supply, h, kernelSupply, Cell.rate]
noncomputable def rate (c : κ) (k : TruthKind) (rs : List (Record κ V)) : ℝ :=
  if eligible c rs then (estimate c k rs : ℝ) else 0
theorem rate_bounds (c : κ) (k : TruthKind) (rs : List (Record κ V)) :
    rate c k rs ∈ Set.Icc (0 : ℝ) 1 := by
  unfold rate
  split_ifs
  · have h := estimate_bounds c k rs
    constructor
    · exact_mod_cast le_of_lt h.1
    · exact_mod_cast le_of_lt h.2
  · simp
/-- The current-identity/minimum filter feeds tokenLikelihood's actual carrier. -/
noncomputable def machineKernel [Fintype V] [DecidableEq V]
    (loaded : κ → Mechanism) (labels : List (Label κ V))
    (classOf : V → κ) (kindOf : κ → ClassKind) :
    Except (KernelAbsence V) (CountedKernel V) := by
  classical
  let rs := recordsFor loaded labels
  exact match (Finset.univ : Finset V).toList.find?
      (fun v => decide (¬ eligible (classOf v) rs ∧ kindOf (classOf v) = .judgement)) with
    | some v => .error (.unsupported v)
    | none => .ok {
        rates := {falseNeg := fun v => rate (classOf v) .falseNeg rs
                  falsePos := fun v => rate (classOf v) .falsePos rs
                  falseNeg_mem := fun v => rate_bounds (classOf v) .falseNeg rs
                  falsePos_mem := fun v => rate_bounds (classOf v) .falsePos rs}
        assumedZero := Finset.univ.filter (fun v => ¬ eligible (classOf v) rs)}
noncomputable def likelihood [Fintype V] [DecidableEq V]
    (loaded : κ → Mechanism) (labels : List (Label κ V))
    (classOf : V → κ) (kindOf : κ → ClassKind) (s o : Finset V) :
    Except (KernelAbsence V) ℝ :=
  (machineKernel loaded labels classOf kindOf).map (fun k => tokenLikelihood k.rates s o)
theorem kernelRatesAreReaderRates [Fintype V] [DecidableEq V]
    (loaded : κ → Mechanism) (labels : List (Label κ V))
    (classOf : V → κ) (kindOf : κ → ClassKind) (k : CountedKernel V)
    (h : machineKernel loaded labels classOf kindOf = .ok k) :
    ∀ v, k.rates.falseNeg v = rate (classOf v) .falseNeg (recordsFor loaded labels) ∧
         k.rates.falsePos v = rate (classOf v) .falsePos (recordsFor loaded labels) ∧
         (v ∈ k.assumedZero ↔ ¬ eligible (classOf v) (recordsFor loaded labels)) := by
  classical
  unfold machineKernel at h
  dsimp only at h
  split at h
  · cases h
  · cases h
    intro v
    simp

/-- Ten distinct subjects at the actual 5/5 boundary; all checks are correct. -/
def fivePerCell : List (Record Unit Nat) :=
  (List.range 10).map fun i =>
    {tokenClass := (), subject := i, recorded := some (decide (i < 5)),
     admitted := some (if i < 5 then .present else .absent)}
example : supply () .checkable fivePerCell = .measured (1/12) (1/12) := by
  have dfn : denominator () .falseNeg fivePerCell = 5 := by decide
  have dfp : denominator () .falsePos fivePerCell = 5 := by decide
  have nfn : numerator () .falseNeg fivePerCell = 0 := by decide
  have nfp : numerator () .falsePos fivePerCell = 0 := by decide
  norm_num [supply, eligible, estimate, jeffreys, dfn, dfp, nfn, nfp]
example : supply () .checkable (fivePerCell.take 9) = .zeroKernelAssumed := by decide
example : supply () .judgement (fivePerCell.take 9) = .unsupported := by decide
example : recordsFor (fun _ : Unit => {name := "C3", source := "current"})
    (fivePerCell.map fun r => ⟨r, some {name := "C4", source := "current"}⟩) = [] := by decide

#print axioms jeffreys_strict_bounds
#print axioms kernelRatesAreReaderRates
#print axioms excludedCheckableIsAbsent
#print axioms excludedJudgementRefuses
example : jeffreys 0 5 = 1/12 := by norm_num [jeffreys]
example : jeffreys 5 5 = 11/12 := by norm_num [jeffreys]
example : jeffreys 0 5 ≠ (0 : ℚ) / 5 := by norm_num [jeffreys]
end DarkTower.WarMachine.Proof2.Revision3Rates
