import DarkTower.WarMachine.Holes

/-!
# The cascade-grain policy set

The supplied menu ranges over the same ordered cascade keys used by the
production habit prior. Provenance and typed absences retain their existing
meaning; declaring this set does not fill missing identity information.
-/

namespace DarkTower.WarMachine.Proof2.CascadePolicySet

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

/-- The extensional set of cascade keys in the supplied policy menu. -/
def cascadePolicySet (menu : List (PolicyKey M P)) : Set (PolicyKey M P) :=
  {key | key ∈ menu}

@[simp] theorem mem_cascadePolicySet (menu : List (PolicyKey M P))
    (key : PolicyKey M P) : key ∈ cascadePolicySet menu ↔ key ∈ menu := Iff.rfl

#print axioms PolicyKey
#print axioms KeyProvenance
#print axioms KeyAbsence
#print axioms cascadePolicySet
#print axioms mem_cascadePolicySet

end DarkTower.WarMachine.Proof2.CascadePolicySet
