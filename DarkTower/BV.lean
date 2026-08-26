/-!
# System BV structures

This file adds a first DarkTower syntax and one-step relation for Guglielmi's
system BV in the calculus of structures.  BV has atoms, a self-dual unit, and
three binary connectives:

* `seq S T` is non-commutative sequential composition, read here as sequential
  fill or a path through typed holes;
* `copar S T` is a commutative conjunction of hole requirements;
* `par S T` is a commutative alternative of hole patterns.

The bridge to the rest of DarkTower is intentionally prose-level in this pass:
`Comb` supplies wiring between polynomial positions and `Fill` supplies
substitution; BV supplies a small algebra of hole-pattern shapes over the atoms.

Grounding:
* Guglielmi, *A System of Interaction and Structure* (arXiv:cs/9910023), is the
  definitional source for system BV and its medial/deep-inference rules.
* Guglielmi, *Deep Inference*, is the overview reference for inference inside
  structures rather than only at the root.
* Categorical BV models, often called BV-categories, are the intended semantic
  direction for a later pass.

Atoms have an explicit formal-dual constructor rather than requiring the
parameter type `A` to carry an involution.  This preserves existing users of
`atom` while making De Morgan duality and atomic interaction intrinsic.

TODO: defer cut-elimination, decidability of derivability, and the full
splitting theorem.  This file records syntax, structural congruence, primitive
one-step rules, and finite reduction to the unit.
-/

namespace DarkTower

universe u

/-- BV structures over atoms of type `A`. -/
inductive BV (A : Type u) where
  /-- The self-dual unit. -/
  | unit : BV A
  /-- An atomic hole-pattern label. -/
  | atom : A -> BV A
  /-- The formal dual of an atomic label.  Formal dual atoms preserve the
  existing atom type and its users without requiring a global involution on
  `A`. -/
  | dualAtom : A -> BV A
  /-- Non-commutative sequential composition. -/
  | seq : BV A -> BV A -> BV A
  /-- Commutative conjunction/cotensor of structures. -/
  | copar : BV A -> BV A -> BV A
  /-- Commutative alternative/par structure. -/
  | par : BV A -> BV A -> BV A

namespace BV

variable {A : Type u}

/-- De Morgan duality.  Atoms and formal dual atoms exchange, `par` and
`copar` exchange, and the self-dual noncommutative `seq` retains its order. -/
def dual : BV A → BV A
  | unit => unit
  | atom a => dualAtom a
  | dualAtom a => atom a
  | seq S T => seq (dual S) (dual T)
  | copar S T => par (dual S) (dual T)
  | par S T => copar (dual S) (dual T)

@[simp] theorem dual_dual (S : BV A) : dual (dual S) = S := by
  induction S <;> simp [dual, *]

/--
Structural congruence for BV structures.

This is an inductive relation rather than a quotient: it includes reflexive,
symmetric, transitive, and congruence closure, plus associativity for all three
binary connectives, commutativity for `copar` and `par`, and unit laws.
-/
inductive Cong : BV A -> BV A -> Prop where
  /-- Reflexivity of structural congruence. -/
  | refl (S : BV A) : Cong S S
  /-- Symmetry of structural congruence. -/
  | symm {S T : BV A} : Cong S T -> Cong T S
  /-- Transitivity of structural congruence. -/
  | trans {S T U : BV A} : Cong S T -> Cong T U -> Cong S U
  /-- Congruence under `seq`. -/
  | seq_congr {S S' T T' : BV A} : Cong S S' -> Cong T T' ->
      Cong (seq S T) (seq S' T')
  /-- Congruence under `copar`. -/
  | copar_congr {S S' T T' : BV A} : Cong S S' -> Cong T T' ->
      Cong (copar S T) (copar S' T')
  /-- Congruence under `par`. -/
  | par_congr {S S' T T' : BV A} : Cong S S' -> Cong T T' ->
      Cong (par S T) (par S' T')
  /-- Associativity of non-commutative sequence. -/
  | seq_assoc (S T U : BV A) : Cong (seq (seq S T) U) (seq S (seq T U))
  /-- Associativity of `copar`. -/
  | copar_assoc (S T U : BV A) : Cong (copar (copar S T) U) (copar S (copar T U))
  /-- Associativity of `par`. -/
  | par_assoc (S T U : BV A) : Cong (par (par S T) U) (par S (par T U))
  /-- Commutativity of `copar`. -/
  | copar_comm (S T : BV A) : Cong (copar S T) (copar T S)
  /-- Commutativity of `par`. -/
  | par_comm (S T : BV A) : Cong (par S T) (par T S)
  /-- Left unit law for sequence. -/
  | seq_unit_left (S : BV A) : Cong (seq unit S) S
  /-- Right unit law for sequence. -/
  | seq_unit_right (S : BV A) : Cong (seq S unit) S
  /-- Left unit law for `copar`. -/
  | copar_unit_left (S : BV A) : Cong (copar unit S) S
  /-- Right unit law for `copar`. -/
  | copar_unit_right (S : BV A) : Cong (copar S unit) S
  /-- Left unit law for `par`. -/
  | par_unit_left (S : BV A) : Cong (par unit S) S
  /-- Right unit law for `par`. -/
  | par_unit_right (S : BV A) : Cong (par S unit) S

/--
One-step BV rewriting.

The rules here are deliberately minimal.  `ai_down` introduces a dual atomic
pair from the unit, `medial` interleaves sequence with `copar`/`par`, `switch`
distributes `copar` through one side of `par`, and `cong` allows structural
congruence as a step.

All rules are oriented DOWNWARD, in the calculus-of-structures convention: a
derivation runs from premise to conclusion, so a proof of `S` is a derivation
from the unit to `S`.  (Joe, 2026-08-26: keep `ai_down` in line with canonical
sources.  Guglielmi gives `ai↓ : S{◦} → S[a, ā]`; an earlier version here had it
reversed, as reduction TO the unit, which inverted `Provable` with it.)
-/
inductive Step : BV A -> BV A -> Prop where
/-- Atomic interaction, canonical `ai↓ : S{◦} → S[a, ā]` — the unit introduces
  a dual atomic pair. -/
  | ai_down (a : A) : Step unit (par (atom a) (dualAtom a))
  /--
  Medial: sequentially composed `copar` pairs step to a `copar` of `par` pairs.
  This is the schematic deep-inference move used here as the BV heart rule.
  -/
  | medial (S T U V : BV A) :
      Step (seq (copar S U) (copar T V)) (copar (par S T) (par U V))
  /-- Switch: tensor/coproduct distributes through one side of `par`. -/
  | switch (R U T : BV A) :
      Step (copar (par R U) T) (par (copar R T) U)
  /-- Structural congruence can be used as a one-step move. -/
  | cong {S T : BV A} : Cong S T -> Step S T

/-- A BV derivation is the reflexive-transitive closure of primitive steps. -/
inductive Derives : BV A → BV A → Prop where
  | refl (S : BV A) : Derives S S
  | tail {S T U : BV A} : Derives S T → Step T U → Derives S U

/-- A structure is provable when it is derivable FROM the unit — the
calculus-of-structures reading, matching `ai_down`'s canonical orientation. -/
def Provable (S : BV A) : Prop := Derives unit S

/-- The smallest interaction proof: an atom paired with its formal dual. -/
theorem dual_pair_provable (a : A) : Provable (par (atom a) (dualAtom a)) :=
  Derives.tail (Derives.refl unit) (Step.ai_down a)

/-- Sanity check: sequence associativity is structural congruence. -/
theorem seq_assoc_cong (S T U : BV A) :
    Cong (seq (seq S T) U) (seq S (seq T U)) :=
  Cong.seq_assoc S T U

/-- Sanity check: `par` commutativity is structural congruence. -/
theorem par_comm_cong (S T : BV A) : Cong (par S T) (par T S) :=
  Cong.par_comm S T

/-- Sanity check: a concrete atom-level medial step. -/
theorem atom_medial (a b c d : A) :
    Step
      (seq (copar (atom a) (atom c)) (copar (atom b) (atom d)))
      (copar (par (atom a) (atom b)) (par (atom c) (atom d))) :=
  Step.medial (atom a) (atom b) (atom c) (atom d)

/-- Sanity check: structural congruence embeds as a step. -/
theorem seq_assoc_step (S T U : BV A) :
    Step (seq (seq S T) U) (seq S (seq T U)) :=
  Step.cong (seq_assoc_cong S T U)

#check BV.Cong.seq_assoc
#check BV.Step.medial
#check BV.atom_medial

end BV

end DarkTower
