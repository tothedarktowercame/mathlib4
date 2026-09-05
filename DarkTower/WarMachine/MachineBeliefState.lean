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

open DarkTower.WarMachine.Holes

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

/-- An entity the previous tick believed something about, absent from this tick's
bootstrap domain, is absent from the result.  Both conjuncts are needed: the
first alone holds for any `carried` and so would not be about a carried-only
entity at all. -/
theorem carriedOnlyEntityIsDropped (fresh carried : machineBeliefState) (e : Entity)
    (posterior : Posterior) (hf : fresh e = none)
    (hc : carried e = some posterior) :
    reconcileBeliefCarry fresh carried e = none ∧ carried e ≠ none := by
  refine ⟨by simp [reconcileBeliefCarry, hf], ?_⟩
  simp [hc]

theorem coldStartReturnsFresh (fresh : machineBeliefState) :
    reconcileBeliefCarry fresh (fun _ => none) = fresh := by
  funext e
  cases h : fresh e <;> simp [reconcileBeliefCarry, h]

def Normalised (posterior : Posterior) : Prop :=
  (Status.all.map posterior).sum = 1

/-- The uniform prior `belief.clj:44-49` builds is a distribution.  Without this
`carryPreservesNormalisation`'s hypotheses are never discharged for any concrete
state in the development. -/
theorem uniformPriorIsNormalised : Normalised uniformPrior := by
  simp [Normalised, Status.all, uniformPrior]
  norm_num

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

/-- The machine's posterior is indexed by the seven `Status` values; the
glossary's `Holes.BeliefState` carries its mean and variance over the fourteen
`Holes.Channel` values (`Holes.lean:6806-6808`).  This says the two index sets
are not the same set relabelled.  It does NOT say that no map between the two
carriers exists — that is a claim about a corpus, which Lean cannot settle. -/
theorem statusIndexDiffersFromChannelIndex :
    Status.all.length ≠ Channel.all.length := by
  simp [Status.all, Channel.all]

noncomputable def entropy (posterior : Posterior) : ℝ :=
  -((Status.all.filter (fun s => 0 < posterior s)).map
      (fun s => posterior s * Real.log (posterior s))).sum

end DarkTower.WarMachine.MachineBeliefState
