import DarkTower.WarMachine.TokenObservation

/-!
# Adjudication rates counted from records (C2, registry `:adjudication-rates`)

WM-LEAN-ABSENT-TRIAGE-D (`futon2 57849fb9`) row 18 / entry C2, the Lean side of
the absent edge R2→R7 (`ref-label`). `TokenObservation.AdjudicationRates` is a
STRUCTURE: it carries `falseNeg`, `falsePos` and their `[0,1]` bounds, i.e. the
TYPE of a rate table and nothing about where the numbers come from. The registry
row's `:formal` is a definition by counting — "false-neg := P(recorded verdict =
false | admitted = :present) … as RAW exact-rational counts, numerator over
denominator" — and no declaration counted. That is why the row's `:lean` named
the structure and R2→R7 had no import behind it.

## What is being compared, and why the two sides are independent

`futon3c holes/labs/M-wm-wiring/F1b-D.md` (claude-11) settles the reading, and
this module sits on it: in `tokenLikelihood r s o` the observation `o` is THE
RECORDED VERDICT — what the check reported — and the ADMITTED REFERENCE LABEL is
truth established separately, by a review blinded from that verdict. The rates
compare the two. A rate estimated against the check's own output would measure
nothing, which is what the blinding is for.

## The counting, at the code's own grain

`futon2:src/futon2/aif/observation_rates.clj`:

* `cell` (`:32-48`) keeps the labels matching the conditioning admission AND
  carrying a recorded verdict, denominator = how many are left, numerator = how
  many of those are the error, and returns `{:status :unobserved}` at a zero
  denominator. `cellOf` is that function.
* `rates-by-class` (`:75-107`) groups by `:token-class`, NOT by token. The
  grouping key is part of the definition, so `Record` carries a `tokenClass` and
  `cellOf` takes the class it is counting. Tokens receive their class's rates
  through a `classOf` map, which is `token-likelihood-rates`' `token-classes`.
* The records the code passes are `{:token-class c :recorded r :admitted a}` —
  one label is one subject's pair, which is how "for the same subject" is
  enforced. `Record.subject` is carried here as well, so the row's phrase has a
  referent in the type rather than only in the calling convention.

## What the kernel receives for an unobserved cell

`token-likelihood-rates` (`:156-216`) and `measured-cell` (`:126-152`), read for
this packet, give three outcomes and `kernelSupply` states them:

* both cells observed → the measured rates (`Supply.measured`);
* the class WHOLLY unobserved and CHECKABLE → `{:false-neg 0 :false-pos 0 :basis
  :checkable :measurement :absent}`, the zero kernel as the UNMEASURED DEFAULT.
  `Supply.zeroKernelAssumed` is that arm, and it is not a measurement of zero:
  `tokenLikelihood_checkable` is conditional on the rates being zero, and
  `:measurement :absent` records that the condition was assumed;
* anything else — ONE cell unobserved while the other is measured, or a
  `:judgement` class with no rate → the typed refusal `:unsupported-class`.
  `partialMeasurementIsUnsupported` is that case, and it is the one worth
  naming: a half-measured class is refused, never padded to the measured half.

So an unobserved cell NEVER reaches the kernel as a number.
`unobservedIsNeverMeasured` states it: `Supply.measured` is reachable only when
both cells are observed.

## What this module does not claim

It does not model coverage (`rates-by-class` also returns labels/subjects), the
`:unknown-subject-count` refusal, priors and `:posterior-mean` (the row admits a
prior only with an explicit `:authority`), or `measured-cell`'s third outcome
`:declared-not-measured` — a cell whose declared rate its own counts do not
produce. That last is a check on a rate table arriving from outside; everything
here is counted, so it cannot arise.
-/

namespace DarkTower.WarMachine.Proof2.AdjudicationCounts

open DarkTower.WarMachine.TokenObservation

variable {κ V : Type*}

/-- The admitted reference label: truth as review established it, independently
of the check's own verdict. -/
inductive Admitted where
  | present
  | absent
  deriving DecidableEq, Repr

/-- One adjudication record: a subject in a class, what the check RECORDED, and
what review ADMITTED. Either may be missing, and the row's definition counts
only where both are present. -/
structure Record (κ V : Type*) where
  tokenClass : κ
  subject : V
  recorded : Option Bool
  admitted : Option Admitted

/-- The two conditionals the row defines. -/
inductive TruthKind where
  | falseNeg
  | falsePos
  deriving DecidableEq, Repr

/-- What each kind conditions on: `falseNeg` on an admitted `:present`,
`falsePos` on an admitted `:absent`. -/
def TruthKind.conditionsOn : TruthKind → Admitted
  | .falseNeg => .present
  | .falsePos => .absent

/-- The error each kind counts: a `false` verdict where truth is present, a
`true` verdict where truth is absent (`observation_rates.clj:104-105`). -/
def TruthKind.isError : TruthKind → Option Bool → Bool
  | .falseNeg, v => decide (v = some false)
  | .falsePos, v => decide (v = some true)

/-- One cell: exact counts, or the typed absence. There is no third form, and
in particular no zero-denominator number. -/
inductive Cell where
  | observed (numerator denominator : ℕ)
  | unobserved
  deriving DecidableEq, Repr

/-- The cell's rate as an exact rational, or nothing. The absence PROPAGATES:
an unobserved cell has no rate, rather than a rate of zero. -/
def Cell.rate : Cell → Option ℚ
  | .observed n d => some ((n : ℚ) / (d : ℚ))
  | .unobserved => none

section Counting

variable [DecidableEq κ]

/-- The records a cell counts: in the class, carrying a recorded verdict, AND
carrying the admitted reference this kind conditions on. This conjunction is the
row's "an error count exists only where BOTH a recorded verdict and an admitted
reference are present for the same subject". -/
def paired (c : κ) (k : TruthKind) (records : List (Record κ V)) : List (Record κ V) :=
  records.filter fun r =>
    decide (r.tokenClass = c) && r.recorded.isSome &&
      decide (r.admitted = some k.conditionsOn)

/-- **The cell.** Denominator = the paired records; numerator = those of them
that are the error; `unobserved` at a zero denominator. -/
def cellOf (c : κ) (k : TruthKind) (records : List (Record κ V)) : Cell :=
  if (paired c k records).isEmpty then .unobserved
  else .observed ((paired c k records).filter fun r => k.isError r.recorded).length
        (paired c k records).length

/-- **`onlyPairedRecordsCount`.** Every record a cell counts carries both halves:
a recorded verdict and the admitted reference for this kind. -/
theorem onlyPairedRecordsCount (c : κ) (k : TruthKind) (records : List (Record κ V))
    (r : Record κ V) (hr : r ∈ paired c k records) :
    r.tokenClass = c ∧ r.recorded.isSome ∧ r.admitted = some k.conditionsOn := by
  have h := (List.mem_filter.mp hr).2
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

/-- **`emptyCellIsUnobserved`.** No paired record means the typed absence, not a
zero. -/
theorem emptyCellIsUnobserved (c : κ) (k : TruthKind) (records : List (Record κ V))
    (h : paired c k records = []) : cellOf c k records = .unobserved := by
  simp [cellOf, h]

/-- An observed cell has a positive denominator: the zero-denominator case was
routed to `unobserved`. -/
theorem observed_denominator_pos (c : κ) (k : TruthKind) (records : List (Record κ V))
    {n d : ℕ} (h : cellOf c k records = .observed n d) : 0 < d := by
  unfold cellOf at h
  split_ifs at h with hemp
  simp only [Cell.observed.injEq] at h
  rw [← h.2]
  exact List.length_pos_iff.mpr (by simpa [List.isEmpty_iff] using hemp)

/-- The numerator never exceeds the denominator: the errors are a sublist of the
comparisons. -/
theorem observed_numerator_le (c : κ) (k : TruthKind) (records : List (Record κ V))
    {n d : ℕ} (h : cellOf c k records = .observed n d) : n ≤ d := by
  unfold cellOf at h
  split_ifs at h with hemp
  simp only [Cell.observed.injEq] at h
  rw [← h.1, ← h.2]
  exact List.length_filter_le _ _

/-- **`rate_mem_unitInterval`.** A counted rate is a probability. -/
theorem rate_mem_unitInterval (c : κ) (k : TruthKind) (records : List (Record κ V))
    {q : ℚ} (h : (cellOf c k records).rate = some q) : q ∈ Set.Icc (0 : ℚ) 1 := by
  unfold Cell.rate at h
  split at h
  · rename_i n d hcell
    simp only [Option.some.injEq] at h
    subst h
    have hd : 0 < d := observed_denominator_pos c k records hcell
    have hn : n ≤ d := observed_numerator_le c k records hcell
    have hdq : (0 : ℚ) < (d : ℚ) := by exact_mod_cast hd
    constructor
    · positivity
    · rw [div_le_one hdq]
      exact_mod_cast hn
  · exact absurd h (by simp)

end Counting

/-! ## The bad cases -/

section BadCases

/-- A class of one, and one token. -/
abbrev K := Unit
abbrev T := Unit

/-- A check that said "present" with NO admitted reference behind it. -/
def verdictOnly : Record K T := ⟨(), (), some true, none⟩

/-- **A verdict with no reference contributes to no cell.** This is the row's
"an error count exists only where BOTH …": half a pair is not evidence about a
rate, in either direction. -/
theorem verdictWithoutReferenceCountsNowhere (k : TruthKind) :
    cellOf () k [verdictOnly] = .unobserved := by
  cases k <;> decide

/-- A reference with no check behind it is equally uncounted. -/
def referenceOnly : Record K T := ⟨(), (), none, some .present⟩

theorem referenceWithoutVerdictCountsNowhere (k : TruthKind) :
    cellOf () k [referenceOnly] = .unobserved := by
  cases k <;> decide

/-- Two paired records about one subject: the check was right once and wrong
once, against an admitted `:present` both times. -/
def missed : Record K T := ⟨(), (), some false, some .present⟩
def caught : Record K T := ⟨(), (), some true, some .present⟩

/-- **Two records give a denominator of two, not a last-write.** Both
comparisons are evidence and both are counted; the rate is one half. -/
theorem twoRecordsGiveDenominatorTwo :
    cellOf () .falseNeg [missed, caught] = .observed 1 2 ∧
    (cellOf () .falseNeg [missed, caught]).rate = some (1/2) := by
  constructor
  · decide
  · norm_num [cellOf, paired, Cell.rate, missed, caught, TruthKind.conditionsOn,
      TruthKind.isError]

/-- **A zero denominator is `unobserved`, not a rate of zero.** The cell has no
rate at all, so nothing downstream can read one. -/
theorem allZeroDenominatorIsUnobserved :
    cellOf () TruthKind.falseNeg ([] : List (Record K T)) = .unobserved ∧
    (cellOf () TruthKind.falseNeg ([] : List (Record K T))).rate = none := by
  constructor <;> decide

end BadCases

/-! ## What the kernel receives -/

/-- The observation contract's two class kinds
(`resources/wm/observation-contract.edn`). -/
inductive ClassKind where
  | checkable
  | judgement
  deriving DecidableEq, Repr

/-- What `token-likelihood-rates` hands the kernel for one class. -/
inductive Supply where
  /-- Both cells counted: these are the rates, `:basis :estimated`. -/
  | measured (falseNeg falsePos : ℚ)
  /-- The class is wholly unobserved and checkable: the zero kernel as the
  UNMEASURED DEFAULT, recorded `:measurement :absent`. Not a measurement of
  zero — `tokenLikelihood_checkable` is conditional on the rates being zero and
  this arm records that the condition was assumed. -/
  | zeroKernelAssumed
  /-- `:unsupported-class`. A partial measurement is never padded. -/
  | unsupported
  deriving DecidableEq, Repr

/-- `token-likelihood-rates:156-216`, in its own order: measured first,
the checkable zero kernel only for a WHOLLY unobserved class, refusal otherwise. -/
def kernelSupply (kind : ClassKind) (fnCell fpCell : Cell) : Supply :=
  match fnCell.rate, fpCell.rate with
  | some fnRate, some fpRate => .measured fnRate fpRate
  | _, _ =>
    match fnCell, fpCell, kind with
    | .unobserved, .unobserved, .checkable => .zeroKernelAssumed
    | _, _, _ => .unsupported

/-- **A half-measured class is refused, at either kind and either class kind.**
This is the answer to "what does the kernel receive for an unobserved cell" when
the other cell WAS measured: nothing — the class is `:unsupported-class`, and the
measured half is not kept. -/
theorem partialMeasurementIsUnsupported (kind : ClassKind) (n d : ℕ) :
    kernelSupply kind (.observed n d) .unobserved = .unsupported ∧
    kernelSupply kind .unobserved (.observed n d) = .unsupported := by
  constructor <;> (cases kind <;> rfl)

/-- A wholly unobserved CHECKABLE class takes the zero kernel, as an assumption
on the record rather than a measurement. -/
theorem wholeClassUnobservedCheckableIsAssumedZero :
    kernelSupply .checkable .unobserved .unobserved = .zeroKernelAssumed := rfl

/-- A wholly unobserved JUDGEMENT class is refused: it has no rate to assume. -/
theorem wholeClassUnobservedJudgementIsUnsupported :
    kernelSupply .judgement .unobserved .unobserved = .unsupported := rfl

/-- **`unobservedIsNeverMeasured`.** The kernel reaches a NUMBER only when both
cells were counted. No unobserved cell is ever coerced into a rate — not to
zero, not to anything. -/
theorem unobservedIsNeverMeasured (kind : ClassKind) (fnCell fpCell : Cell)
    {fnRate fpRate : ℚ} (h : kernelSupply kind fnCell fpCell = .measured fnRate fpRate) :
    fnCell.rate = some fnRate ∧ fpCell.rate = some fpRate := by
  unfold kernelSupply at h
  split at h
  · rename_i hfn hfp
    simp only [Supply.measured.injEq] at h
    exact ⟨by rw [hfn, h.1], by rw [hfp, h.2]⟩
  · exact absurd h (by split <;> simp)

/-! ## The tie to `TokenObservation.AdjudicationRates` -/

section Kernel

variable [DecidableEq κ] [Fintype V] [DecidableEq V]

/-- Every token's class is fully counted: the hypothesis under which the kernel
gets a rate table at all. Outside it, `kernelSupply` gives
`zeroKernelAssumed` or `unsupported`, never a table. -/
def FullyMeasured (records : List (Record κ V)) (classOf : V → κ) : Prop :=
  ∀ v, (cellOf (classOf v) .falseNeg records).rate.isSome ∧
       (cellOf (classOf v) .falsePos records).rate.isSome

/-- The counted rate of a token's class, zero where its cell is unobserved. The
zero is NOT a stand-in: `adjudicationRatesOf` below is only ever applied under
`FullyMeasured`, where no cell is unobserved, and `kernelSupply` is what decides
what happens otherwise. -/
noncomputable def rateAt (records : List (Record κ V)) (classOf : V → κ)
    (k : TruthKind) (v : V) : ℝ :=
  ((cellOf (classOf v) k records).rate.getD 0 : ℚ)

/-- **`adjudicationRatesOf`.** With every token's class counted on both cells,
the records produce the kernel's rate table, bounds and all. -/
noncomputable def adjudicationRatesOf (records : List (Record κ V)) (classOf : V → κ)
    (h : FullyMeasured records classOf) : AdjudicationRates V where
  falseNeg := rateAt records classOf .falseNeg
  falsePos := rateAt records classOf .falsePos
  falseNeg_mem := by
    intro v
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h v).1
    have hmem := rate_mem_unitInterval (classOf v) .falseNeg records hq
    simp only [rateAt, hq, Option.getD_some]
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2⟩
  falsePos_mem := by
    intro v
    obtain ⟨q, hq⟩ := Option.isSome_iff_exists.mp (h v).2
    have hmem := rate_mem_unitInterval (classOf v) .falsePos records hq
    simp only [rateAt, hq, Option.getD_some]
    exact ⟨by exact_mod_cast hmem.1, by exact_mod_cast hmem.2⟩

end Kernel

#print axioms Admitted
#print axioms Record
#print axioms TruthKind
#print axioms Cell
#print axioms Cell.rate
#print axioms paired
#print axioms cellOf
#print axioms onlyPairedRecordsCount
#print axioms emptyCellIsUnobserved
#print axioms observed_denominator_pos
#print axioms observed_numerator_le
#print axioms rate_mem_unitInterval
#print axioms verdictWithoutReferenceCountsNowhere
#print axioms referenceWithoutVerdictCountsNowhere
#print axioms twoRecordsGiveDenominatorTwo
#print axioms allZeroDenominatorIsUnobserved
#print axioms ClassKind
#print axioms Supply
#print axioms kernelSupply
#print axioms partialMeasurementIsUnsupported
#print axioms wholeClassUnobservedCheckableIsAssumedZero
#print axioms wholeClassUnobservedJudgementIsUnsupported
#print axioms unobservedIsNeverMeasured
#print axioms FullyMeasured
#print axioms rateAt
#print axioms adjudicationRatesOf

end DarkTower.WarMachine.Proof2.AdjudicationCounts
