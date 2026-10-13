import DarkTower.CoolMemories

namespace DarkTower.CoolMemoriesBoundaryNegative

open DarkTower.CoolMemories

def left : CertifiedDelta ({1} : Snapshot Nat) {2} := CertifiedDelta.between {1} {2}
def wrongRight : CertifiedDelta ({3} : Snapshot Nat) {4} := CertifiedDelta.between {3} {4}

/--
error: Application type mismatch: The argument
  wrongRight
has type
  CertifiedDelta {3} {4}
but is expected to have type
  CertifiedDelta {2} ?m.22
in the application
  TypedDiagram.atom wrongRight
-/
#guard_msgs in
def malformed := TypedDiagram.seq (.atom left) (.atom wrongRight)

end DarkTower.CoolMemoriesBoundaryNegative
