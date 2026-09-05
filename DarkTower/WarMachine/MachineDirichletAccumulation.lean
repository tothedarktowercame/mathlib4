import Mathlib
import DarkTower.WarMachine.MachineObservation
import DarkTower.WarMachine.MachineBeliefState

/-!
# The R17 accumulation: what da Costa eq. 21 declares, and what A4a recounts

The registry row `:dirichlet-accumulation` (node R17, `:imports [:o :mu]`,
`:realised false`) declares `a = a + sum_tau o_tau (x) s_tau`.  What runs is
`corpus->concentration` (`futon2:src/futon2/aif/a4a.clj:85-113`): a uniform
`0.1` prior on every capability x mission cell, plus exactly `1.0` per
substrate record.  This module states the four ways the two differ, each as a
proposition about the two functions rather than as a name.

1. **The increment.**  A record moves ONE cell (`machineAppendRaisesItsOwnCell`,
   `machineAppendMovesNoOtherCell`).  A tick whose observation carries mass on
   two channels moves TWO (`softDeclaredUpdateRaisesTwoCells`), and
   `noSingleRecordProducesASoftUpdate` says no record can do that.  The
   machine's rule is the one-hot special case of the declared one
   (`oneHotDeclaredUpdateIsTheUnitIncrement`), so re-sourcing the records would
   not by itself make the two agree.
2. **The recurrence.**  `declaredAccumulation` takes the previous `a`;
   `machineDirichletAccumulation` has no such parameter — its type is
   `List CorpusRecord -> Nat -> Nat -> R`.  That is a fact about the SIGNATURE,
   stated here and not dressed as a theorem; the corresponding fact about
   production is that no public function in `futon2.aif.a4a` takes a previous
   concentration together with new records (every public arglist is measured in
   `futon2:holes/labs/wm-contract/runs/F8-dirichlet-accumulation/review-independent-probe-2.txt`).
   What IS provable is that the recount SHAPE cannot satisfy the declared
   contract whatever it is fed: `recountShapedDoesNotRealise`.
3. **The coordinates.**  The declared rule's indices are the machine's own fixed
   carriers, `Holes.Channel` and `MachineBeliefState.Status`, whose index sets
   differ (`statusIndexDiffersFromChannelIndex`, imported and used in
   `declaredCoordinatesAreFixedAndMachineCoordinatesAreNot`).  The recount's
   outcome coordinate is a POSITION in a re-sorted list of substrate mission ids
   (`futon2:src/futon2/aif/a4a.clj:74-76,102-104`), so the same coordinate names
   a different outcome after the corpus changes (`machineCoordinatesAreNotStable`).
4. **The repair path.**  `RealisesDeclaredAccumulation` is the obligation a
   repaired implementation must discharge.  It is non-vacuous
   (`declaredAccumulationRealisesItself`) and not trivially satisfiable
   (`recountShapedDoesNotRealise`).

NOT CLAIMED HERE: that no code path carries the tick model's `o` or `mu` into
R17's concentrations.  Lean cannot prove the absence of a code path; that claim
is held by-record at `Holes.dirichletAccumulationImportAbsent`
(`Holes.lean:7679`), whose falsifier this module's predicate makes checkable.
-/
namespace DarkTower.WarMachine.MachineDirichletAccumulation

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

/-- Production's uniform cell prior, `(def prior … 0.1)`
(`futon2:src/futon2/aif/a4a.clj:11-13`). -/
noncomputable def a4aPrior : ℝ := 1 / 10

/-- Production's per-record increment: `increment-cell` does
`(update-in matrix [capability outcome-index] + 1.0)`
(`futon2:src/futon2/aif/a4a.clj:78-83`). -/
def a4aIncrement : ℝ := 1

/-- One substrate record.  Both coordinates are POSITIONS — the capability and
outcome axes are sorted id lists indexed by place
(`futon2:src/futon2/aif/a4a.clj:74-76,102-104`). -/
structure CorpusRecord where
  capability : Nat
  mission : Nat
  deriving DecidableEq, BEq, Repr

/-- The cell test inside the reduction over records
(`futon2:src/futon2/aif/a4a.clj:78-83`). -/
def matchesCell (capability mission : Nat) (record : CorpusRecord) : Bool :=
  record.capability == capability && record.mission == mission

/-- A4a's recount (`futon2:src/futon2/aif/a4a.clj:85-113`): every cell starts at
the prior and each record adds the increment to its own cell.  THE SIGNATURE IS
PART OF THE STATEMENT — there is no previous-concentration parameter, so this is
a function of the corpus alone and not the recurrence the registry declares. -/
noncomputable def machineDirichletAccumulation (corpus : List CorpusRecord) :
    Nat → Nat → ℝ := fun capability mission =>
  a4aPrior + a4aIncrement * ((corpus.filter (matchesCell capability mission)).length : ℝ)

/-- Da Costa eq. 21 typed over the machine's own carriers: the previous `a`
plus the sum over ticks of the outer product `o_tau (x) s_tau`
(`futon2:holes/labs/wm-contract/aif-equations.edn`, `:dirichlet-accumulation`). -/
noncomputable def declaredAccumulation (a : Channel → Status → ℝ)
    (ticks : List ((Channel → ℝ) × (Status → ℝ))) : Channel → Status → ℝ :=
  fun channel status => a channel status +
    (ticks.map fun tick => tick.1 channel * tick.2 status).sum

/-- One record raises its own cell by exactly the production increment
(`futon2:src/futon2/aif/a4a.clj:78-83`). -/
theorem machineAppendRaisesItsOwnCell (corpus : List CorpusRecord) (record : CorpusRecord) :
    machineDirichletAccumulation (record :: corpus) record.capability record.mission =
      machineDirichletAccumulation corpus record.capability record.mission + a4aIncrement := by
  simp [machineDirichletAccumulation, matchesCell, a4aIncrement]
  ring

/-- …and moves no other cell.  Together with the theorem above this is the whole
content of "the machine adds a unit count": one record, one cell
(`futon2:src/futon2/aif/a4a.clj:78-83`). -/
theorem machineAppendMovesNoOtherCell (corpus : List CorpusRecord) (record : CorpusRecord)
    (capability mission : Nat)
    (h : ¬ (capability = record.capability ∧ mission = record.mission)) :
    machineDirichletAccumulation (record :: corpus) capability mission =
      machineDirichletAccumulation corpus capability mission := by
  have hfalse : matchesCell capability mission record = false := by
    simp only [matchesCell, Bool.and_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
    by_cases hc : record.capability = capability
    · right
      intro hm
      exact h ⟨hc.symm, hm.symm⟩
    · exact Or.inl hc
  simp [machineDirichletAccumulation, hfalse]

/-- NO SINGLE RECORD MOVES TWO CELLS.  This is what makes the divergence more
than a wiring gap: whatever the records were sourced from, one of them can only
move one cell (`futon2:src/futon2/aif/a4a.clj:78-83`). -/
theorem noSingleRecordProducesASoftUpdate (corpus : List CorpusRecord)
    (record : CorpusRecord) (c₀ m₀ c₁ m₁ : Nat) (hne : ¬ (c₀ = c₁ ∧ m₀ = m₁))
    (h₀ : machineDirichletAccumulation (record :: corpus) c₀ m₀ ≠
      machineDirichletAccumulation corpus c₀ m₀)
    (h₁ : machineDirichletAccumulation (record :: corpus) c₁ m₁ ≠
      machineDirichletAccumulation corpus c₁ m₁) : False := by
  by_cases hit₀ : c₀ = record.capability ∧ m₀ = record.mission
  · by_cases hit₁ : c₁ = record.capability ∧ m₁ = record.mission
    · exact hne ⟨hit₀.1.trans hit₁.1.symm, hit₀.2.trans hit₁.2.symm⟩
    · exact h₁ (machineAppendMovesNoOtherCell corpus record c₁ m₁ hit₁)
  · exact h₀ (machineAppendMovesNoOtherCell corpus record c₀ m₀ hit₀)

/-- THE MACHINE'S RULE IS THE ONE-HOT SPECIAL CASE.  For a Kronecker `o` and
`s` the declared update adds exactly `a4aIncrement` at the joint cell and
nothing anywhere else — the recount's rule, in the declared rule's own terms. -/
theorem oneHotDeclaredUpdateIsTheUnitIncrement (a : Channel → Status → ℝ)
    (c₀ : Channel) (s₀ : Status) :
    declaredAccumulation a [(fun c => if c = c₀ then 1 else 0,
        fun x => if x = s₀ then 1 else 0)] c₀ s₀ = a c₀ s₀ + a4aIncrement ∧
    ∀ c x, ¬ (c = c₀ ∧ x = s₀) →
      declaredAccumulation a [(fun c => if c = c₀ then 1 else 0,
        fun x => if x = s₀ then 1 else 0)] c x = a c x := by
  constructor
  · simp [declaredAccumulation, a4aIncrement]
  · intro c x h
    by_cases hc : c = c₀
    · have hx : x ≠ s₀ := fun hx => h ⟨hc, hx⟩
      simp [declaredAccumulation, hc, hx]
    · simp [declaredAccumulation, hc]

/-- …AND THE SOFT CASE IS OUTSIDE IT.  One tick whose observation carries mass
on two channels raises two cells strictly, which by
`noSingleRecordProducesASoftUpdate` no record can do.  Re-sourcing A4a from the
tick model would therefore still not realise eq. 21. -/
theorem softDeclaredUpdateRaisesTwoCells (a : Channel → Status → ℝ)
    (c₀ c₁ : Channel) (hne : c₀ ≠ c₁) (s₀ : Status) :
    a c₀ s₀ < declaredAccumulation a
        [(fun c => if c = c₀ ∨ c = c₁ then 1 / 2 else 0,
          fun x => if x = s₀ then 1 else 0)] c₀ s₀ ∧
    a c₁ s₀ < declaredAccumulation a
        [(fun c => if c = c₀ ∨ c = c₁ then 1 / 2 else 0,
          fun x => if x = s₀ then 1 else 0)] c₁ s₀ := by
  constructor
  · simp [declaredAccumulation]
  · simp [declaredAccumulation, hne.symm]

/-- The positional outcome lookup that `outcomes-by-id` builds
(`futon2:src/futon2/aif/a4a.clj:102-104`). -/
def outcomePosition (mission : String) (outcomes : List String) : Option Nat :=
  outcomes.idxOf? mission

/-- The recount's coordinates move when the corpus does: `sorted-ids` re-sorts
the mission axis on every call (`futon2:src/futon2/aif/a4a.clj:74-76,102-104`),
so adding one record with an earlier-sorting id shifts `m1` from column 0 to
column 1.  MEASURED in production, same values
(`futon2:holes/labs/wm-contract/runs/F8-dirichlet-accumulation/clojure-readback.txt`). -/
theorem machineCoordinatesAreNotStable :
    outcomePosition "m1" ["m1", "m2"] = some 0 ∧
    outcomePosition "m1" ["aaa", "m1", "m2"] = some 1 := by decide

/-- BOTH ARMS OF THE COORDINATE DIFFERENCE.  The declared rule is indexed by two
FIXED carriers — and they are genuinely two, not one relabelled
(`MachineBeliefState.statusIndexDiffersFromChannelIndex`) — while the recount's
outcome coordinate is a list position that the corpus can move. -/
theorem declaredCoordinatesAreFixedAndMachineCoordinatesAreNot :
    Status.all.length ≠ Channel.all.length ∧
    outcomePosition "m1" ["m1", "m2"] ≠ outcomePosition "m1" ["aaa", "m1", "m2"] :=
  ⟨statusIndexDiffersFromChannelIndex, by decide⟩

/-- THE REPAIR PATH.  An implementation realises the declared accumulation when,
on the machine's own fixed `Channel`/`Status` coordinates, it agrees with
da Costa eq. 21 for every previous concentration and every tick list.  This is
the obligation the falsifier of `Holes.dirichletAccumulationImportAbsent`
(`Holes.lean:7679`) would have to discharge; the hole itself stays open and
untouched. -/
def RealisesDeclaredAccumulation
    (acc : (Channel → Status → ℝ) → List ((Channel → ℝ) × (Status → ℝ)) →
      Channel → Status → ℝ) : Prop :=
  ∀ a ticks, acc a ticks = declaredAccumulation a ticks

/-- The obligation is not empty. -/
theorem declaredAccumulationRealisesItself :
    RealisesDeclaredAccumulation declaredAccumulation := fun _ _ => rfl

/-- The RECOUNT SHAPE: an accumulation that discards whatever concentration it
is given and rebuilds from this tick's data alone.  That is the shape
`corpus->concentration` has — its only parameter is the corpus, and every cell
starts at the prior (`futon2:src/futon2/aif/a4a.clj:85-113`).  This is a shape,
not a function production exports; no public function in `futon2.aif.a4a` takes
a previous concentration together with new records. -/
noncomputable def recountShaped (_previous : Channel → Status → ℝ)
    (ticks : List ((Channel → ℝ) × (Status → ℝ))) : Channel → Status → ℝ :=
  declaredAccumulation (fun _ _ => 0) ticks

/-- The obligation is not trivially satisfiable, and this is the sharp form of
"the machine recounts rather than accumulates": a recount-shaped implementation
FAILS the contract on an empty tick list, before any data is seen.  Whatever
records such an implementation is fed, and wherever they come from, it cannot
realise eq. 21. -/
theorem recountShapedDoesNotRealise : ¬ RealisesDeclaredAccumulation recountShaped := by
  intro h
  have := congrFun (congrFun (h (fun _ _ => 1) []) Channel.loopHealth) Status.spawned
  simp [recountShaped, declaredAccumulation] at this

#print axioms a4aPrior
#print axioms a4aIncrement
#print axioms CorpusRecord
#print axioms matchesCell
#print axioms machineDirichletAccumulation
#print axioms declaredAccumulation
#print axioms machineAppendRaisesItsOwnCell
#print axioms machineAppendMovesNoOtherCell
#print axioms noSingleRecordProducesASoftUpdate
#print axioms oneHotDeclaredUpdateIsTheUnitIncrement
#print axioms softDeclaredUpdateRaisesTwoCells
#print axioms outcomePosition
#print axioms machineCoordinatesAreNotStable
#print axioms declaredCoordinatesAreFixedAndMachineCoordinatesAreNot
#print axioms RealisesDeclaredAccumulation
#print axioms declaredAccumulationRealisesItself
#print axioms recountShaped
#print axioms recountShapedDoesNotRealise

end DarkTower.WarMachine.MachineDirichletAccumulation
