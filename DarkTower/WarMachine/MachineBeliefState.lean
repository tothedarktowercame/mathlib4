import DarkTower.WarMachine.Holes

/-!
# Stored machine belief μ

The machine stores entity-indexed categorical posteriors over the seven
statuses in `futon2:src/futon2/aif/belief.clj:36-66`, not the channel-indexed
moment carrier `Holes.BeliefState`. `reconcileBeliefCarry` mirrors
`reconcile-belief-carry` (`futon2:src/futon2/aif/belief.clj:510-522`): its
domain is exactly the fresh bootstrap, with values chosen without arithmetic.
-/
namespace DarkTower.WarMachine.MachineBeliefState

inductive Status
  | spawned | refined | strengthened | addressed | falsified | foreclosed | reopened
  deriving DecidableEq, Repr

def Status.all : List Status :=
  [.spawned, .refined, .strengthened, .addressed, .falsified, .foreclosed, .reopened]

abbrev Entity := Nat
abbrev Posterior := Status → ℝ
abbrev machineBeliefState := Entity → Option Posterior

noncomputable def uniformPrior : Posterior := fun _ => 1 / 7

def reconcileBeliefCarry (fresh carried : machineBeliefState) : machineBeliefState :=
  fun entity => match fresh entity with
    | none => none
    | some prior => some ((carried entity).getD prior)

theorem survivorKeepsCarried (fresh carried : machineBeliefState) (e : Entity)
    (prior posterior : Posterior) (hf : fresh e = some prior)
    (hc : carried e = some posterior) :
    reconcileBeliefCarry fresh carried e = some posterior := by
  simp [reconcileBeliefCarry, hf, hc]

theorem newEntityKeepsFresh (fresh carried : machineBeliefState) (e : Entity)
    (prior : Posterior) (hf : fresh e = some prior) (hc : carried e = none) :
    reconcileBeliefCarry fresh carried e = some prior := by
  simp [reconcileBeliefCarry, hf, hc]

theorem carriedOnlyEntityIsDropped (fresh carried : machineBeliefState) (e : Entity)
    (posterior : Posterior) (hf : fresh e = none)
    (_hc : carried e = some posterior) :
    reconcileBeliefCarry fresh carried e = none := by
  simp [reconcileBeliefCarry, hf]

theorem coldStartReturnsFresh (fresh : machineBeliefState) :
    reconcileBeliefCarry fresh (fun _ => none) = fresh := by
  funext e
  cases h : fresh e <;> simp [reconcileBeliefCarry, h]

def Normalised (posterior : Posterior) : Prop :=
  (Status.all.map posterior).sum = 1

theorem carryPreservesNormalisation (fresh carried : machineBeliefState)
    (hf : ∀ e p, fresh e = some p → Normalised p)
    (hc : ∀ e p, carried e = some p → Normalised p) :
    ∀ e p, reconcileBeliefCarry fresh carried e = some p → Normalised p := by
  intro e p h
  cases hfresh : fresh e with
  | none => simp [reconcileBeliefCarry, hfresh] at h
  | some prior =>
    cases hcarry : carried e with
    | none =>
      simp [reconcileBeliefCarry, hfresh, hcarry] at h
      subst p
      exact hf e prior hfresh
    | some posterior =>
      simp [reconcileBeliefCarry, hfresh, hcarry] at h
      subst p
      exact hc e posterior hcarry

noncomputable def entropy (posterior : Posterior) : ℝ :=
  -((Status.all.filter (fun s => 0 < posterior s)).map
      (fun s => posterior s * Real.log (posterior s))).sum

end DarkTower.WarMachine.MachineBeliefState
