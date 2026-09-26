import DarkTower.WarMachine.PolicyRollout
import DarkTower.WarMachine.Proof2.AdjudicationCounts
import DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict

/-!
# The token kernel at the counted rates (W8, registry `:token-likelihood`, R4, from R7)

## What the entries show

The Lean map's [R7 R4] entry is the term `rates`: importer `:token-likelihood` (R4's kernel,
`:lean TokenObservation.tokenLikelihood`, `:imports [:rates]`), source `:adjudication-rates`
(R7, `:lean Proof2.AdjudicationCounts.adjudicationRatesOf`). C2's `AdjudicationCounts` imports
`TokenObservation`, so the Lean dependency ran opposite to the data flow: the counter imports
the kernel's carrier, and nothing applied the kernel to the counter's output.

(The [R7 R3] entry's term is `Pi`, whose importer is `:belief-update`, the Laplace update
`mu <- mu + alpha Pi eps`. It is not the exact update `machineStep` computes, which has no
precision; see `BeliefStepAtMachine.machineStepAtCounts` for what W8 supplies there.)

## What this module supplies

`machineKernel records classOf kindOf` builds the kernel's rate table from the counted
records, token by token, through C2's `kernelSupply` and its three arms:

* `measured`: the rates are the counted rates;
* `zeroKernelAssumed` (a wholly unobserved CHECKABLE class): the zero kernel, AS AN
  ASSUMPTION, and the tokens that took it are RECORDED on the value (`assumedZero`), so a
  consumer can tell it from a measurement of zero (`measuredZeroIsNotRecordedAbsent`);
* `unsupported` (a partially measured class, or an unobserved judgement class): a refusal
  naming a token (`KernelAbsence.unsupported`), never a number
  (`partialMeasurementIsRefusedAtKernel`).

No arm pads a missing cell. The kernel where a partial `o` is scored is C5's restriction to
the checked tokens (`restrictedAtCounts`), and marginalises the full kernel
(`restrictedAtCounts_marginalises`).
-/

set_option linter.unusedSectionVars false

namespace DarkTower.WarMachine.Proof2.KernelAtCounts

open DarkTower.WarMachine
open DarkTower.WarMachine.TokenObservation
open DarkTower.WarMachine.Proof2.AdjudicationCounts
open DarkTower.WarMachine.Proof2.TokenLikelihoodRestrict
open DarkTower.WarMachine.PolicyRollout (ForwardModel)

noncomputable section

variable {κ V : Type*} [DecidableEq κ] [Fintype V] [DecidableEq V]

/-- What `token-likelihood-rates` hands the kernel for token `v`'s class. -/
def supplyOf (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind)
    (v : V) : Supply :=
  kernelSupply (kindOf (classOf v)) (cellOf (classOf v) .falseNeg records)
    (cellOf (classOf v) .falsePos records)

/-- A measured supply carries counted rates, which are probabilities. -/
theorem supply_measured_bounds (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (v : V) {fn fp : ℚ}
    (h : supplyOf records classOf kindOf v = .measured fn fp) :
    fn ∈ Set.Icc (0 : ℚ) 1 ∧ fp ∈ Set.Icc (0 : ℚ) 1 := by
  obtain ⟨h1, h2⟩ := unobservedIsNeverMeasured _ _ _ h
  exact ⟨rate_mem_unitInterval _ _ _ h1, rate_mem_unitInterval _ _ _ h2⟩

/-- The false-negative rate the kernel takes for `v`: the counted rate if measured, `0` on
the assumed-zero arm (recorded, see `CountedKernel.assumedZero`), `0` on the refused arm
(never reached in an ok kernel). -/
def fnOf (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind)
    (v : V) : ℝ :=
  match supplyOf records classOf kindOf v with
  | .measured fn _ => (fn : ℝ)
  | _ => 0

def fpOf (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind)
    (v : V) : ℝ :=
  match supplyOf records classOf kindOf v with
  | .measured _ fp => (fp : ℝ)
  | _ => 0

theorem fnOf_mem (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind)
    (v : V) : fnOf records classOf kindOf v ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fnOf
  cases hs : supplyOf records classOf kindOf v with
  | measured fn fp =>
    have := (supply_measured_bounds records classOf kindOf v hs).1
    dsimp only
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  | zeroKernelAssumed => simp
  | unsupported => simp

theorem fpOf_mem (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind)
    (v : V) : fpOf records classOf kindOf v ∈ Set.Icc (0 : ℝ) 1 := by
  unfold fpOf
  cases hs : supplyOf records classOf kindOf v with
  | measured fn fp =>
    have := (supply_measured_bounds records classOf kindOf v hs).2
    dsimp only
    exact ⟨by exact_mod_cast this.1, by exact_mod_cast this.2⟩
  | zeroKernelAssumed => simp
  | unsupported => simp

/-- The kernel's rate table, WITH the record of which tokens took the unmeasured default. -/
structure CountedKernel (V : Type*) where
  rates : AdjudicationRates V
  /-- Tokens whose class took the zero kernel as an ASSUMPTION (`:measurement :absent`). -/
  assumedZero : Finset V

/-- Why there is no kernel. -/
inductive KernelAbsence (V : Type*) where
  | unsupported (v : V)

open Classical in
/-- **The kernel at the counted rates.** A refusal naming the first token whose class is
`unsupported`; otherwise the rate table and the record of the assumed-zero tokens. -/
def machineKernel (records : List (Record κ V)) (classOf : V → κ) (kindOf : κ → ClassKind) :
    Except (KernelAbsence V) (CountedKernel V) :=
  match (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some v => .error (.unsupported v)
  | none =>
    .ok { rates := { falseNeg := fnOf records classOf kindOf
                     falsePos := fpOf records classOf kindOf
                     falseNeg_mem := fnOf_mem records classOf kindOf
                     falsePos_mem := fpOf_mem records classOf kindOf }
          assumedZero := Finset.univ.filter
            (fun v => supplyOf records classOf kindOf v = .zeroKernelAssumed) }

/-- On the ok arm no token is unsupported. -/
theorem machineKernel_ok_not_unsupported (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (k : CountedKernel V)
    (h : machineKernel records classOf kindOf = .ok k) (v : V) :
    supplyOf records classOf kindOf v ≠ .unsupported := by
  classical
  unfold machineKernel at h
  cases hf : (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some w => rw [hf] at h; cases h
  | none =>
    have := List.find?_eq_none.mp hf v (by simp)
    simpa using this

/-- **A measured class gives exactly its counted rates.** -/
theorem machineKernel_measured (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (k : CountedKernel V)
    (h : machineKernel records classOf kindOf = .ok k) (v : V) (fn fp : ℚ)
    (hs : supplyOf records classOf kindOf v = .measured fn fp) :
    k.rates.falseNeg v = (fn : ℝ) ∧ k.rates.falsePos v = (fp : ℝ) := by
  classical
  unfold machineKernel at h
  cases hf : (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some w => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    have hk := (Except.ok.inj h).symm
    subst hk
    simp [fnOf, fpOf, hs]

/-- **`zeroKernelIsRecordedAbsent`.** A token whose class took the zero-kernel default has
rates zero AND is in `assumedZero`: the default carries its absence on the value. -/
theorem zeroKernelIsRecordedAbsent (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (k : CountedKernel V)
    (h : machineKernel records classOf kindOf = .ok k) (v : V)
    (hs : supplyOf records classOf kindOf v = .zeroKernelAssumed) :
    k.rates.falseNeg v = 0 ∧ k.rates.falsePos v = 0 ∧ v ∈ k.assumedZero := by
  classical
  unfold machineKernel at h
  cases hf : (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some w => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    have hk := (Except.ok.inj h).symm
    subst hk
    simp [fnOf, fpOf, hs]

/-- **A MEASURED zero is not the recorded default**: a token whose class was counted with
zero error rates is not in `assumedZero`. A consumer can tell a measurement of zero from the
assumed zero kernel. -/
theorem measuredZeroIsNotRecordedAbsent (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (k : CountedKernel V)
    (h : machineKernel records classOf kindOf = .ok k) (v : V)
    (hs : supplyOf records classOf kindOf v = .measured 0 0) :
    k.rates.falseNeg v = 0 ∧ k.rates.falsePos v = 0 ∧ v ∉ k.assumedZero := by
  classical
  unfold machineKernel at h
  cases hf : (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some w => rw [hf] at h; cases h
  | none =>
    rw [hf] at h
    have hk := (Except.ok.inj h).symm
    subst hk
    simp [fnOf, fpOf, hs]

/-- **`partialMeasurementIsRefusedAtKernel`.** C2's third arm reaches the kernel as a
REFUSAL: if some token's class has one cell counted and the other unobserved, there is no
kernel, and no number for that class. -/
theorem partialMeasurementIsRefusedAtKernel (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (v : V) (n d : ℕ)
    (hfn : cellOf (classOf v) .falseNeg records = .observed n d)
    (hfp : cellOf (classOf v) .falsePos records = .unobserved) :
    ∃ w, machineKernel records classOf kindOf = .error (.unsupported w) := by
  classical
  have hsup : supplyOf records classOf kindOf v = .unsupported := by
    unfold supplyOf
    rw [hfn, hfp]
    exact (partialMeasurementIsUnsupported _ n d).1
  unfold machineKernel
  cases hf : (Finset.univ : Finset V).toList.find?
      (fun v => decide (supplyOf records classOf kindOf v = .unsupported)) with
  | some w => exact ⟨w, rfl⟩
  | none =>
    exfalso
    have := List.find?_eq_none.mp hf v (by simp)
    simp [hsup] at this

/-! ## The likelihood at the counts -/

/-- **`A(o|s)` at the counted kernel**: `tokenLikelihood` of the counted rates, or the
kernel's absence. -/
def tokenLikelihoodAtCounts (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (s o : Finset V) : Except (KernelAbsence V) ℝ :=
  (machineKernel records classOf kindOf).map fun k => tokenLikelihood k.rates s o

theorem tokenLikelihoodAtCounts_eq (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (s o : Finset V) (x : ℝ)
    (h : tokenLikelihoodAtCounts records classOf kindOf s o = .ok x) :
    ∃ k, machineKernel records classOf kindOf = .ok k ∧ x = tokenLikelihood k.rates s o := by
  unfold tokenLikelihoodAtCounts at h
  cases hk : machineKernel records classOf kindOf with
  | error e => rw [hk] at h; cases h
  | ok k => rw [hk] at h; exact ⟨k, rfl, (Except.ok.inj h).symm⟩

/-- **Where a partial `o` is scored**: C5's restriction to the checked tokens `C`, at the
counted rates. -/
def restrictedAtCounts (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (s C o : Finset V) : Except (KernelAbsence V) ℝ :=
  (machineKernel records classOf kindOf).map fun k => restrictedLikelihood k.rates s C o

/-- **The restricted kernel marginalises the full one** (C5's `tokenLikelihood_restrict`),
at the counted rates. -/
theorem restrictedAtCounts_marginalises (records : List (Record κ V)) (classOf : V → κ)
    (kindOf : κ → ClassKind) (s C o : Finset V) (ho : o ⊆ C) (x : ℝ)
    (h : restrictedAtCounts records classOf kindOf s C o = .ok x) :
    ∃ k, machineKernel records classOf kindOf = .ok k ∧
      x = ∑ u ∈ Cᶜ.powerset, tokenLikelihood k.rates s (o ∪ u) := by
  unfold restrictedAtCounts at h
  cases hk : machineKernel records classOf kindOf with
  | error e => rw [hk] at h; cases h
  | ok k =>
    rw [hk] at h
    exact ⟨k, rfl, by rw [tokenLikelihood_restrict k.rates s C o ho]; exact (Except.ok.inj h).symm⟩

/-! ## The kernel as a model's likelihood -/

variable {U : Type*}

/-- A forward model over token states whose likelihood is replaced by the counted kernel. -/
def withKernel (M : ForwardModel (Finset V) (Finset V) U) (k : CountedKernel V) :
    ForwardModel (Finset V) (Finset V) U :=
  { M with
    A := tokenLikelihood k.rates
    A_nonneg := fun s o => tokenLikelihood_nonneg k.rates s o
    A_colsum := fun s => tokenLikelihood_colsum k.rates s }

end

#print axioms supplyOf
#print axioms supply_measured_bounds
#print axioms fnOf_mem
#print axioms fpOf_mem
#print axioms CountedKernel
#print axioms KernelAbsence
#print axioms machineKernel
#print axioms machineKernel_ok_not_unsupported
#print axioms machineKernel_measured
#print axioms zeroKernelIsRecordedAbsent
#print axioms measuredZeroIsNotRecordedAbsent
#print axioms partialMeasurementIsRefusedAtKernel
#print axioms tokenLikelihoodAtCounts
#print axioms tokenLikelihoodAtCounts_eq
#print axioms restrictedAtCounts
#print axioms restrictedAtCounts_marginalises
#print axioms withKernel

end DarkTower.WarMachine.Proof2.KernelAtCounts
