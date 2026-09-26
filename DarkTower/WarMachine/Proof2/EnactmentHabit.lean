import DarkTower.WarMachine.Holes

/-!
# The habit prior E, counted from enactment records (C4, registry `:enactment-habit`)

PROOF-2a hole H-E. `Holes.PolicyPriorKernel` is
`abbrev … := ProbabilityKernel Unit PolicyIndex` — the carrier TYPE and no
equation — which is what the registry row's `:lean` named and why its `:latex`
was a typed absence. The row's `:formal` is a counting rule, and
`futon2:src/futon2/aif/enactment_habit.clj` runs it. This module states it.

## The key, and why it is not `MachinePolicySet`'s index

The row's key is the cascade-grain triple `[mission, ordered pattern ids,
semilattice]` (`cascade_prior.clj` `policy-key`). `MachinePolicySet`'s index is
`Candidate`, the FLAT action grain today's production selection ranges over —
the divergence `:policy-set`'s own row already records ("flat `Candidate` grain;
diverges from the approved `CascadePolicy` carrier"). They are different grains,
so `PolicyKey` is stated here rather than reused, and the gap is the one already
on the record, not a new one.

## The three standing absences of the key (A1, A2, A3)

`policy-key-for`'s docstring keeps these as ABSENCES, not defaults, and
`KeyProvenance` carries them onto the key rather than leaving them in a comment:

* **A1** the `:target` slot names an INSTANCE when the target is below the
  mission — the key's `mission` may be finer than a mission;
* **A2** the click carries no precedence, so `shown` is read from the
  CONSTRUCTOR REPLAY, not from the click;
* **A3** no reader maps the click's containment and co-application edges to
  `:semilattice`, so it is always empty. `semilatticeIsAlwaysEmpty` states that.

These are separate from the five REFUSALS `policy-key-for` returns when a slot
is missing (`KeyAbsence`), which is the difference between "recorded as
unmapped" and "no key at all".

## What E is with no data: uniform, not an absence

`cascade_prior.clj` `log-priors` computes
`ln( ((count k + α) / multiplicity k) / Σ_{distinct k} (count k + α) )` with
`default-alpha = 1.0`. With NO records every count is `0`, so every distinct menu
entry gets `α / (|distinct menu| · α) = 1/|distinct menu|`: **uniform over the
menu**. `habitPrior_uniform_of_noRecords` states it. That is a Dirichlet
smoothing, not a typed absence, and it has a consequence worth naming:

**A policy with zero count does NOT have weight zero.** Its mass is
`α / denominator > 0` (`habitPrior_pos`), so under W1b's `machineWeights` —
whose carrier requires `hhabit : ∀ π, 0 < habit π` — an unenacted policy is
scored, not excluded. The row's `:formal` says nothing about zero counts, and
this is what the code does.

The absence is elsewhere: with an EMPTY menu there is no distribution at all
(a sum over no support cannot be one), so `habitPrior` takes the menu's
nonemptiness as a hypothesis.

## The counting, at the code's own grain

* `increment` (`:66-98`): `:delta 1` exactly when the W_c verdict is an EMPTY
  VECTOR. A fail gives `:delta 0` with the failures; a map carrying a `:status`
  is check-c's typed non-verdict, counted `0` with its status kept; anything
  else is `{:status :absent}` — "no verdict is not a pass". An attempt at a
  pattern outside the candidate REFUSES the receipt outright.
* `fold` (`:99-118`): a `:delta 1` receipt counts once per `[click, candidate]`;
  a later one with the same id goes to `:duplicates`. **`:delta 0` receipts are
  skipped WITHOUT registering their id**, so a failing record does not block a
  later passing one at the same occurrence — `zeroDeltaDoesNotClaimTheOccurrence`
  states that, and it is the kind of thing a dedup written from the prose alone
  would get wrong.

## What this module does not claim

Nothing about `attempts` as trials of a pattern's θ (clause 5, which the row
says are NOT trials of E), about the `:deviations` receipts carry, about
recency decay (`:recency-decay :none` today), or about where the W_c verdict
comes from — `check-c` is futon3c's and this row's `:formal` calls the verdict
input data.
-/

namespace DarkTower.WarMachine.Proof2.EnactmentHabit

open DarkTower.WarMachine.Holes

variable {M P : Type*} [DecidableEq M] [DecidableEq P]

/-- The cascade-grain policy key: `[mission, ordered pattern ids, semilattice]`
(`cascade_prior.clj` `policy-key`). Pattern ORDER in `shown` is kept; semilattice
edge order is not. -/
structure PolicyKey (M P : Type*) where
  mission : M
  shown : List P
  semilattice : List (P × P)
  deriving DecidableEq

/-- What `policy-key-for` records ABOUT the key it built: the three standing
absences, carried rather than silently defaulted. -/
structure KeyProvenance where
  /-- A1: the mission slot was filled from a target that may be an INSTANCE
  below the mission. -/
  missionMayBeInstance : Bool
  /-- A2: `shown` came from the constructor replay, because the click carries no
  precedence. -/
  shownFromReplay : Bool
  /-- A3: no reader maps containment and co-application edges, so the
  semilattice is empty. -/
  semilatticeUnmapped : Bool

/-- `policy-key-for`'s five typed refusals (`:34-65`). None of them is a zero
count: a record with no key is EXCLUDED and reported. -/
inductive KeyAbsence where
  | enactmentNamesNoCandidate
  | candidateNotInClick
  | targetAbsent
  | precedenceAbsent (distinctPrecedences : ℕ)
  | noPolicyIdentity
  deriving DecidableEq

/-- The W_c verdict as `increment` reads it: `check-c`'s vector of failure
strings, empty meaning pass. -/
inductive WcVerdict where
  /-- An empty failure vector. The only value that counts. -/
  | pass
  /-- A non-empty failure vector. -/
  | fail (failures : List String)
  /-- `check-c`'s typed non-verdict, e.g. `{:status :join-unverifiable}`:
  counted zero, its status kept. -/
  | typedNonVerdict (status : String)
  /-- No verdict at all. "No verdict is not a pass." -/
  | absent
  deriving DecidableEq

/-- One enactment record. `occurrence` is the `[click, candidate]` pair the
fold deduplicates by. -/
structure Record (M P : Type*) where
  click : String
  candidate : String
  key : Except KeyAbsence (PolicyKey M P)
  provenance : KeyProvenance
  wcVerdict : WcVerdict
  /-- Patterns the attempts named. An attempt outside the candidate refuses the
  receipt (`increment`). -/
  attemptedPatterns : List P

/-- The `[click, candidate]` identity the fold deduplicates by. -/
def Record.occurrence (r : Record M P) : String × String := (r.click, r.candidate)

/-- Every attempt names a pattern of the candidate. `increment` refuses the
receipt otherwise, so this is a precondition of counting, not a filter on it. -/
def Record.attemptsInside (r : Record M P) : Bool :=
  match r.key with
  | .ok k => r.attemptedPatterns.all (fun p => k.shown.contains p)
  | .error _ => false

/-- `increment`'s `:delta`: one exactly when the key resolved, every attempt is
inside the candidate, and the W_c verdict is a PASS. -/
def Record.delta (r : Record M P) : ℕ :=
  match r.key, r.wcVerdict with
  | .ok _, .pass => if r.attemptsInside then 1 else 0
  | _, _ => 0

/-- **A3, stated.** Every key this module builds has an empty semilattice,
because no reader maps the edges. -/
def semilatticeIsAlwaysEmpty (r : Record M P) : Prop :=
  r.provenance.semilatticeUnmapped = true →
    ∀ k, r.key = .ok k → k.semilattice = []

/-! ## The fold -/

/-- `fold`'s traversal: keep the FIRST `:delta 1` record at each occurrence.
A `:delta 0` record is skipped WITHOUT claiming its occurrence, so it cannot
block a later passing record at the same `[click, candidate]`. -/
def countedFrom (seen : List (String × String)) : List (Record M P) → List (Record M P)
  | [] => []
  | r :: rest =>
      if r.delta = 1 ∧ r.occurrence ∉ seen
      then r :: countedFrom (r.occurrence :: seen) rest
      else countedFrom seen rest

/-- The records that contribute a count. -/
def counted (records : List (Record M P)) : List (Record M P) := countedFrom [] records

/-- **`habitCounts`.** One count per counted record, at its candidate's key. -/
def habitCounts (records : List (Record M P)) (k : PolicyKey M P) : ℕ :=
  ((counted records).filter (fun r => r.key = .ok k)).length

/-! ## The bad cases -/

section BadCases

/-- A key with an empty pattern list. -/
def k0 : PolicyKey String String := ⟨"m", [], []⟩

def mkRecord (click candidate : String) (key : Except KeyAbsence (PolicyKey String String))
    (v : WcVerdict) : Record String String :=
  ⟨click, candidate, key, ⟨true, true, true⟩, v, []⟩

/-- A passing record at its own occurrence. -/
def passing : Record String String := mkRecord "c1" "a" (.ok k0) .pass

/-- The same occurrence again. -/
def passingAgain : Record String String := mkRecord "c1" "a" (.ok k0) .pass

/-- The same candidate at a DIFFERENT click. -/
def passingElsewhere : Record String String := mkRecord "c2" "a" (.ok k0) .pass

/-- A W_c fail. -/
def failing : Record String String := mkRecord "c1" "a" (.ok k0) (.fail ["G_c"])

/-- No verdict at all. -/
def unverdicted : Record String String := mkRecord "c1" "a" (.ok k0) .absent

/-- The key refused: the enactment names a candidate the click does not carry. -/
def keyless : Record String String :=
  mkRecord "c1" "a" (.error .candidateNotInClick) .pass

/-- **`oneRecordOneCount`.** -/
theorem oneRecordOneCount : habitCounts [passing] k0 = 1 := by decide

/-- **`failingVerdictAddsNothing`**, and neither does a missing one: "no verdict
is not a pass". -/
theorem failingVerdictAddsNothing :
    habitCounts [failing] k0 = 0 ∧ habitCounts [unverdicted] k0 = 0 := by
  constructor <;> decide

/-- **`duplicateOccurrenceCountsOnce`.** Two receipts at the same
`[click, candidate]` count once; the same candidate at another click counts
again, so the dedup is by OCCURRENCE and not by candidate. -/
theorem duplicateOccurrenceCountsOnce :
    habitCounts [passing, passingAgain] k0 = 1 ∧
    habitCounts [passing, passingElsewhere] k0 = 2 := by
  constructor <;> decide

/-- **`absentKeyIsNotACount`.** A record whose key refused contributes nothing —
and it is not a zero count at `k0` either, since there is no key to count at. -/
theorem absentKeyIsNotACount : habitCounts [keyless] k0 = 0 := by decide

/-- **`zeroDeltaDoesNotClaimTheOccurrence`.** A failing record does not block a
later passing one at the same occurrence: `fold` skips `:delta 0` receipts
WITHOUT registering their id. A dedup written from the prose alone would get
this backwards. -/
theorem zeroDeltaDoesNotClaimTheOccurrence :
    habitCounts [failing, passing] k0 = 1 := by decide

end BadCases

/-! ## The prior -/

/-- The Dirichlet concentration. `cascade_prior.clj` `default-alpha` is `1.0`,
and `coerce-state` refuses a non-positive or non-finite one. -/
structure Concentration where
  alpha : ℝ
  alpha_pos : 0 < alpha

/-- The unnormalised mass of one key: `count + α`. Positive whatever the count,
which is why an unenacted policy is not excluded. -/
noncomputable def weightOf (records : List (Record M P)) (c : Concentration)
    (k : PolicyKey M P) : ℝ :=
  (habitCounts records k : ℝ) + c.alpha

theorem weightOf_pos (records : List (Record M P)) (c : Concentration)
    (k : PolicyKey M P) : 0 < weightOf records c k := by
  unfold weightOf
  have : (0 : ℝ) ≤ (habitCounts records k : ℝ) := Nat.cast_nonneg _
  linarith [c.alpha_pos]

/-- The normaliser over the DISTINCT menu entries, which is `log-priors`'
denominator: duplicate identities split their category mass, so the total at a
key is the same as if it appeared once. -/
noncomputable def normaliser (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) : ℝ :=
  (menu.dedup.map (weightOf records c)).sum

theorem normaliser_pos (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) :
    0 < normaliser records c menu := by
  unfold normaliser
  have hmem : ∃ k, k ∈ menu.dedup := by
    cases hm : menu with
    | nil => exact absurd hm hne
    | cons a as => exact ⟨a, by simp [List.mem_dedup]⟩
  obtain ⟨k, hk⟩ := hmem
  refine List.sum_pos _ (fun x hx => ?_) (by
    intro hnil
    have : (k : PolicyKey M P) ∈ (menu.dedup) := hk
    simp [List.eq_nil_iff_forall_not_mem] at hnil
    exact absurd (hnil k) (by simpa using this))
  obtain ⟨k', _, rfl⟩ := List.mem_map.mp hx
  exact weightOf_pos records c k'

/-- **`habitPrior`.** E over the menu: `(count + α)` normalised over the
distinct entries, as `Holes.PolicyPriorKernel` requires. -/
noncomputable def habitPrior (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) :
    PolicyPriorKernel (PolicyKey M P) where
  support := fun _ => menu.dedup
  mass := fun _ k => if k ∈ menu.dedup then weightOf records c k / normaliser records c menu else 0
  nonnegative := by
    intro _ k
    by_cases h : k ∈ menu.dedup
    · rw [if_pos h]
      exact div_nonneg (weightOf_pos records c k).le (normaliser_pos records c menu hne).le
    · rw [if_neg h]
  normalised := by
    intro _
    have hpos := normaliser_pos records c menu hne
    have hmap : (menu.dedup.map fun k =>
        if k ∈ menu.dedup then weightOf records c k / normaliser records c menu else 0)
        = menu.dedup.map (fun k => weightOf records c k / normaliser records c menu) :=
      List.map_congr_left fun k hk => if_pos hk
    rw [hmap]
    have hsum : (menu.dedup.map (fun k => weightOf records c k / normaliser records c menu)).sum
        = (menu.dedup.map (weightOf records c)).sum / normaliser records c menu := by
      induction menu.dedup with
      | nil => simp
      | cons a as ih => simp only [List.map_cons, List.sum_cons, ih]; ring
    rw [hsum]
    exact div_self hpos.ne'
  support_nodup := fun _ => menu.nodup_dedup
  mass_eq_zero_of_not_mem := by
    intro _ k hk
    exact if_neg (by simpa using hk)

/-- **Every menu policy has positive mass**, count or no count. An unenacted
policy is SCORED, not excluded: under W1b's `machineWeights`, whose carrier
requires `0 < habit π`, this is the hypothesis being met. -/
theorem habitPrior_pos (records : List (Record M P)) (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) (k : PolicyKey M P)
    (hk : k ∈ menu.dedup) :
    0 < (habitPrior records c menu hne).mass () k := by
  show 0 < if k ∈ menu.dedup then _ else _
  rw [if_pos hk]
  exact div_pos (weightOf_pos records c k) (normaliser_pos records c menu hne)

/-- **E with no data is UNIFORM over the menu, not an absence.** Every count is
zero, so every distinct entry has mass `α / (|menu.dedup| · α) = 1/|menu.dedup|`.
This is the α-smoothing `cascade_prior.clj` applies, and it is why "no records"
is not a refusal here. -/
theorem habitPrior_uniform_of_noRecords (c : Concentration)
    (menu : List (PolicyKey M P)) (hne : menu ≠ []) (k : PolicyKey M P)
    (hk : k ∈ menu.dedup) :
    (habitPrior [] c menu hne).mass () k = 1 / (menu.dedup.length : ℝ) := by
  have hzero : ∀ j : PolicyKey M P, weightOf ([] : List (Record M P)) c j = c.alpha := by
    intro j; simp [weightOf, habitCounts, counted, countedFrom]
  have hnorm : normaliser ([] : List (Record M P)) c menu
      = (menu.dedup.length : ℝ) * c.alpha := by
    unfold normaliser
    rw [List.map_congr_left fun j _ => hzero j, List.map_const', List.sum_replicate,
      nsmul_eq_mul]
  show (if k ∈ menu.dedup then _ else _) = _
  rw [if_pos hk, hzero k, hnorm]
  have hlen : (0 : ℝ) < (menu.dedup.length : ℝ) := by
    have : menu.dedup ≠ [] := by
      intro h; rw [h] at hk; simp at hk
    exact_mod_cast List.length_pos_iff.mpr this
  field_simp
  exact div_self c.alpha_pos.ne'

#print axioms PolicyKey
#print axioms KeyProvenance
#print axioms KeyAbsence
#print axioms WcVerdict
#print axioms Record
#print axioms Record.occurrence
#print axioms Record.attemptsInside
#print axioms Record.delta
#print axioms semilatticeIsAlwaysEmpty
#print axioms countedFrom
#print axioms counted
#print axioms habitCounts
#print axioms oneRecordOneCount
#print axioms failingVerdictAddsNothing
#print axioms duplicateOccurrenceCountsOnce
#print axioms absentKeyIsNotACount
#print axioms zeroDeltaDoesNotClaimTheOccurrence
#print axioms Concentration
#print axioms weightOf
#print axioms weightOf_pos
#print axioms normaliser
#print axioms normaliser_pos
#print axioms habitPrior
#print axioms habitPrior_pos
#print axioms habitPrior_uniform_of_noRecords

end DarkTower.WarMachine.Proof2.EnactmentHabit
