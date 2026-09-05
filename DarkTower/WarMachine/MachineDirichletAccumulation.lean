import Mathlib
import DarkTower.WarMachine.MachineObservation
import DarkTower.WarMachine.MachineBeliefState

/-!
# Machine R17 Dirichlet recount and declared accumulation

The runtime recounts substrate `(capability, mission)` records
(`futon2:src/futon2/aif/a4a.clj:83-113`). The declared equation instead adds
tick-model `o × μ` outer products to a previous concentration. The imported
`statusIndexDiffersFromChannelIndex` records the 7/14 index mismatch; the
by-record absence claim remains `Holes.dirichletAccumulationImportAbsent`.
-/
namespace DarkTower.WarMachine.MachineDirichletAccumulation

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.MachineBeliefState

/-- Production's uniform cell prior (`futon2:src/futon2/aif/a4a.clj:11-13`). -/
noncomputable def a4aPrior : ℝ := 1 / 10

/-- Production's per-record one-cell increment (`futon2:src/futon2/aif/a4a.clj:76-82`). -/
def a4aIncrement : ℝ := 1

/-- A substrate record, whose two coordinates are positional runtime ids
(`futon2:src/futon2/aif/a4a.clj:71-113`). -/
structure CorpusRecord where
  capability : Nat
  mission : Nat
  deriving DecidableEq, BEq, Repr

/-- A4a's pure recount: no previous concentration argument exists
(`futon2:src/futon2/aif/a4a.clj:83-113`). -/
noncomputable def machineDirichletAccumulation (corpus : List CorpusRecord) :
  Nat → Nat → ℝ := fun capability mission =>
  a4aPrior + a4aIncrement *
    (corpus.filter fun record => record.capability = capability ∧
      record.mission = mission).length

/-- Exposes the missing recurrence argument as a check: supplying a previous
concentration cannot affect A4a's recount (`futon2:src/futon2/aif/a4a.clj:83-113`). -/
noncomputable def machineRecountWithPreviousIgnored
    (_previous : Nat → Nat → ℝ) (corpus : List CorpusRecord) : Nat → Nat → ℝ :=
  machineDirichletAccumulation corpus

/-- Da Costa eq.21 typed over the machine observation/status carriers: add
each tick's outer product to previous `a` (`futon2:holes/labs/wm-contract/aif-equations.edn`,
`:dirichlet-accumulation`). -/
noncomputable def declaredAccumulation (a : Channel → Status → ℝ)
    (ticks : List ((Channel → ℝ) × (Status → ℝ))) : Channel → Status → ℝ :=
  fun channel status => a channel status +
    (ticks.map fun tick => tick.1 channel * tick.2 status).sum

/-- A nonzero declared outer-product update changes its previous concentration;
the runtime recount is idempotent on identical corpus input
(`futon2:src/futon2/aif/a4a.clj:83-113`). -/
theorem recurrenceMissingBothArms :
    let o : Channel → ℝ := fun c => if c = .loopHealth then 1 else 0
    let s : Status → ℝ := fun x => if x = .spawned then 1 else 0
    let zero : Channel → Status → ℝ := fun _ _ => 0
    declaredAccumulation zero [(o, s)] .loopHealth .spawned = 1 ∧
    declaredAccumulation (declaredAccumulation zero [(o, s)]) [(o, s)]
      .loopHealth .spawned = 2 ∧
    machineRecountWithPreviousIgnored (fun _ _ => 0) [⟨0, 0⟩] =
      machineRecountWithPreviousIgnored (fun _ _ => 99) [⟨0, 0⟩] := by
  norm_num [declaredAccumulation, machineRecountWithPreviousIgnored,
    machineDirichletAccumulation]

/-- One-hot o and s add one only at their joint cell
(`futon2:src/futon2/aif/a4a.clj:76-82`). -/
theorem oneHotOuterProductIsUnitCell :
    let o : Channel → ℝ := fun c => if c = .loopHealth then 1 else 0
    let s : Status → ℝ := fun x => if x = .spawned then 1 else 0
    o .loopHealth * s .spawned = a4aIncrement ∧
    o .stackPct * s .spawned = 0 ∧ o .loopHealth * s .refined = 0 := by
  norm_num [a4aIncrement]
  decide

/-- A non-one-hot observation adds positive mass to two cells, unlike one
runtime record's single unit cell (`futon2:src/futon2/aif/a4a.clj:76-82`). -/
theorem nonOneHotOuterProductIsNotUnitCell :
    let o : Channel → ℝ := fun c => if c = .loopHealth ∨ c = .stackPct then 1/2 else 0
    let s : Status → ℝ := fun x => if x = .spawned then 1 else 0
    0 < o .loopHealth * s .spawned ∧ 0 < o .stackPct * s .spawned := by norm_num

/-- Positional lookup used after sorted mission ids are rebuilt
(`futon2:src/futon2/aif/a4a.clj:71-74,100-101`). -/
def outcomePosition (mission : String) (outcomes : List String) : Option Nat :=
  outcomes.idxOf? mission

/-- Adding an earlier-sorting mission moves m1 from column zero to column one
(`futon2:src/futon2/aif/a4a.clj:71-74,100-101`). -/
theorem machineCoordinatesAreNotStable :
    outcomePosition "m1" ["m1", "m2"] = some 0 ∧
    outcomePosition "m1" ["aaa", "m1", "m2"] = some 1 := by decide

/-- Checkable obligations for an implementation of declared accumulation,
derived from the R17 equation and the falsifier of
`Holes.dirichletAccumulationImportAbsent` (`Holes.lean:7679`). -/
structure RealisationEvidence where
  fixedChannelStatusCoordinates : Bool
  outerProductIncrement : Bool
  acceptsPreviousConcentration : Bool
  deriving DecidableEq, Repr

/-- A realising implementation must meet all three obligations
(`futon2:holes/labs/wm-contract/aif-equations.edn`, `:dirichlet-accumulation`). -/
def RealisesDeclaredAccumulation (e : RealisationEvidence) : Prop :=
  e.fixedChannelStatusCoordinates = true ∧ e.outerProductIncrement = true ∧
    e.acceptsPreviousConcentration = true

/-- A4a has sorted positional mission coordinates, unit counts, and no previous
`a` argument (`futon2:src/futon2/aif/a4a.clj:71-113`). -/
def machineRealisationEvidence : RealisationEvidence := ⟨false, false, false⟩

/-- The runtime recount fails each declared-realisation obligation for its
named reason (`futon2:src/futon2/aif/a4a.clj:71-113`). -/
theorem machineSatisfiesNoneOfRepairPredicate :
    machineRealisationEvidence.fixedChannelStatusCoordinates = false ∧
    machineRealisationEvidence.outerProductIncrement = false ∧
    machineRealisationEvidence.acceptsPreviousConcentration = false ∧
    ¬ RealisesDeclaredAccumulation machineRealisationEvidence := by
  simp [machineRealisationEvidence, RealisesDeclaredAccumulation]

#print axioms a4aPrior
#print axioms a4aIncrement
#print axioms CorpusRecord
#print axioms machineDirichletAccumulation
#print axioms machineRecountWithPreviousIgnored
#print axioms declaredAccumulation
#print axioms recurrenceMissingBothArms
#print axioms oneHotOuterProductIsUnitCell
#print axioms nonOneHotOuterProductIsNotUnitCell
#print axioms outcomePosition
#print axioms machineCoordinatesAreNotStable
#print axioms RealisationEvidence
#print axioms RealisesDeclaredAccumulation
#print axioms machineRealisationEvidence
#print axioms machineSatisfiesNoneOfRepairPredicate

end DarkTower.WarMachine.MachineDirichletAccumulation
