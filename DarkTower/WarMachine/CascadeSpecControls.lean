import DarkTower.WarMachine.CascadeSpec

namespace DarkTower.WarMachine.CascadeSpecControls
open DarkTower.WarMachine.CascadeSpec

/--
error: Unknown constant `DarkTower.WarMachine.CascadeSpec.PolicySet.mk`
-/
#guard_msgs in
example {L : Library} (xs : List (Cascade L)) : PolicySet L := PolicySet.mk xs

/--
error: invalid {...} notation, constructor for `PolicySet` is marked as private
-/
#guard_msgs in
example {L : Library} (xs : List (Cascade L)) : PolicySet L := { data := xs }

/--
error: `readingCascades` is not a field of structure `Reading`
-/
#guard_msgs in
example {L : Library} (fs : List (Fragment L)) (xs : List (Cascade L)) : Reading L :=
  { fragments := fs, readingCascades := xs }

-- A self-overlap cannot supply the strict identity ordering proof.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : Overlap ({0} : Library) where
  left := ⟨0, 0, by simp, none⟩
  right := ⟨0, 0, by simp, none⟩
  canonical := by simp

-- A label outside the library cannot supply its membership proof.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : Unit ({0} : Library) := ⟨0, 1, by simp, none⟩

-- A two-cycle cannot have a strictly increasing rank in both directions.
/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : Cascade ({0, 1} : Library) where
  units := {⟨0, 0, by simp, none⟩, ⟨1, 1, by simp, none⟩}
  nonempty := by simp
  precedes := {(⟨0, 0, by simp, none⟩, ⟨1, 1, by simp, none⟩),
    (⟨1, 1, by simp, none⟩, ⟨0, 0, by simp, none⟩)}
  overlap := ∅
  labelsInLibrary := by simp
  precedesEndpoints := by simp
  overlapEndpoints := by simp
  rank := (·.id)
  precedesForward := by simp

end DarkTower.WarMachine.CascadeSpecControls
