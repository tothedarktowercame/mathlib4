import DarkTower.WarMachine.ThreeHalvesBlend

/-! A deliberately single-square runtime certificate.  It validates source
pins, hom-set membership, required commutation, consistency, and the finite
K1' pushout-coverage criterion.  Gluing, pasting and transition-kernel
adequacy remain out of scope. -/

namespace DarkTower.WarMachine.ThreeHalvesRuntimeCertificate
open DarkTower.WarMachine.ThreeHalvesBlend

structure ObjectReceipt where
  text : String
  sourcePath : String
  sourceSha256 : String
  theory : Theory
  deriving DecidableEq

def ObjectReceipt.valid (o : ObjectReceipt) : Bool :=
  !o.text.isEmpty && !o.sourcePath.isEmpty && o.sourceSha256.length = 64 &&
    o.theory.wellFormed

structure Receipt where
  G : ObjectReceipt
  I₁ : ObjectReceipt
  I₂ : ObjectReceipt
  B : ObjectReceipt
  a₁ : PMap
  a₂ : PMap
  b₁ : PMap
  b₂ : PMap
  aux₁ : Bool
  aux₂ : Bool
  deriving DecidableEq

def Receipt.square (r : Receipt) : Square :=
  ⟨r.G.theory, r.I₁.theory, r.I₂.theory, r.B.theory,
   r.a₁, r.a₂, r.b₁, r.b₂, r.aux₁, r.aux₂⟩

/-- A non-auxiliary pair of triangles must commute.  If either triangle is
auxiliary there is no two-route equality obligation at this one-square slice;
`Cone.consistent` still checks the active route(s). -/
def Receipt.requiredCommutes (r : Receipt) : Bool :=
  r.aux₁ || r.aux₂ || r.square.commutes

def Receipt.valid (r : Receipt) : Bool :=
  r.G.valid && r.I₁.valid && r.I₂.valid && r.B.valid &&
  r.a₁.wellFormed r.G.theory r.I₁.theory &&
  r.a₂.wellFormed r.G.theory r.I₂.theory &&
  r.b₁.wellFormed r.I₁.theory r.B.theory &&
  r.b₂.wellFormed r.I₂.theory r.B.theory &&
  r.requiredCommutes && r.square.cone.consistent && r.square.cone.isPushout

theorem valid_projects_consistent (r : Receipt) (h : r.valid = true) :
    r.square.cone.consistent = true := by
  simp only [Receipt.valid, Bool.and_eq_true] at h
  aesop

/-- Coverage is computed from the pinned blend object and the two cone-leg
graphs; it is not a receipt-supplied verdict.  By `pushout_iff_coverage`, this
is the executable K1' pushout condition for the square. -/
theorem valid_projects_pushout (r : Receipt) (h : r.valid = true) :
    r.square.cone.isPushout = true := by
  simp only [Receipt.valid, Bool.and_eq_true] at h
  exact h.2

end DarkTower.WarMachine.ThreeHalvesRuntimeCertificate
