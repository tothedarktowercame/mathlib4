import DarkTower.WarMachine.Proof2.AdjudicationCounts

/-! C6: observation_label_reader selects the current check name AND loaded source
identity. Observer identity remains independent. Store admission/unique-label
validation precede this projection; no claim that arbitrary labels are admitted. -/
namespace DarkTower.WarMachine.Proof2.ChannelIdentity
open AdjudicationCounts
structure Mechanism where
  name : String
  source : String
  deriving DecidableEq
structure Label (κ V : Type*) where
  record : Record κ V
  mechanism : Option Mechanism
variable {κ V : Type*}
def currentPopulation (loaded : κ → Mechanism) (labels : List (Label κ V)) :
    List (Label κ V) :=
  labels.filter fun l => decide (l.mechanism = some (loaded l.record.tokenClass))
def recordsFor (loaded : κ → Mechanism) (labels : List (Label κ V)) : List (Record κ V) :=
  (currentPopulation loaded labels).map Label.record

theorem current_iff (loaded : κ → Mechanism) (labels : List (Label κ V)) (l : Label κ V) :
    l ∈ currentPopulation loaded labels ↔
      l ∈ labels ∧ l.mechanism = some (loaded l.record.tokenClass) := by
  simp [currentPopulation]
theorem wrongMechanismExcluded (loaded : κ → Mechanism) (labels : List (Label κ V))
    (l : Label κ V) (h : l.mechanism ≠ some (loaded l.record.tokenClass)) :
    l ∉ currentPopulation loaded labels := by
  simp [currentPopulation, h]
theorem unstampedExcluded (loaded : κ → Mechanism) (labels : List (Label κ V))
    (l : Label κ V) (h : l.mechanism = none) : l ∉ currentPopulation loaded labels := by
  simp [currentPopulation, h]
theorem everyCountedRecordHasCurrentIdentity (loaded : κ → Mechanism)
    (labels : List (Label κ V)) (r : Record κ V) (h : r ∈ recordsFor loaded labels) :
    ∃ l ∈ labels, l.record = r ∧ l.mechanism = some (loaded r.tokenClass) := by
  obtain ⟨l, hl, rfl⟩ := List.mem_map.mp h
  have hp := (current_iff loaded labels l).mp hl
  exact ⟨l, hp.1, rfl, hp.2⟩
example : (some ({name := "C3", source := "sha"} : Mechanism)) ≠
    some ({name := "C4", source := "sha"} : Mechanism) := by decide
example : (some ({name := "C3", source := "old"} : Mechanism)) ≠
    some ({name := "C3", source := "new"} : Mechanism) := by decide
end DarkTower.WarMachine.Proof2.ChannelIdentity
