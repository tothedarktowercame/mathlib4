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

end DarkTower.WarMachine.CascadeSpecControls
