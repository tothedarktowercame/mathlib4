import DarkTower.WarMachine.Proof2.PrefixFreeEnergyPosterior

/-! # Explicit cold-start authority for prefix free energy

This additive layer does not choose a distribution family or numeric prior.  It
states the authority, identity, calibration and update obligations that any such
choice must satisfy, while preserving the empirical prefix implementation.
-/

namespace DarkTower.WarMachine.Proof2.PrefixFreeEnergyColdStart

open DarkTower.WarMachine
open DarkTower.WarMachine.Proof2.CascadePolicySet (PolicyKey)
open DarkTower.WarMachine.Proof2.PrefixFreeEnergyAtMachine
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {M P S O Θ D Authority Evidence Ledger UpdateRule : Type*}
  [DecidableEq M] [DecidableEq P] [Fintype S] [DecidableEq S]
  [DecidableEq Authority]

/-- An external, evidence-bearing prior for exactly one complete policy key. -/
structure BootstrapPrior (M P Θ D Authority Evidence Ledger UpdateRule : Type*) where
  policy : PolicyKey M P
  model : String
  version : String
  parameters : Θ
  distribution : D
  suppliedF : EReal
  rationale : String
  evidence : Evidence
  calibrationEpoch : String
  updateRule : UpdateRule
  evidenceLedger : Ledger
  authority : Authority

/-- Validity is parameterized by independent judgments.  In particular, this
file supplies neither a numeric parameter vector nor a distribution family. -/
structure ValidBootstrap
    (scorerAuthority : Authority) (policy : PolicyKey M P)
    (validParameters : Θ → Prop) (validDistribution : D → Prop)
    (ledgerAuthorizes : Ledger → Evidence → Prop)
    (updateDeclared : UpdateRule → Prop)
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule) : Prop where
  exactPolicy : b.policy = policy
  externalAuthority : b.authority ≠ scorerAuthority
  modelNonempty : b.model ≠ ""
  versionNonempty : b.version ≠ ""
  rationaleNonempty : b.rationale ≠ ""
  epochNonempty : b.calibrationEpoch ≠ ""
  parametersValid : validParameters b.parameters
  distributionValid : validDistribution b.distribution
  ledgerEvidence : ledgerAuthorizes b.evidenceLedger b.evidence
  updateRuleDeclared : updateDeclared b.updateRule

inductive EmpiricalAssessment (M P S O : Type*) where
  | unseen
  | coherent (history : List (Step M P S O)) (f : EReal)
  | malformed (reason : Refusal)
  | contradiction

/-- Empty history is unseen.  Any observed refusal is malformed/contradictory,
never an invitation to bootstrap past the bad evidence. -/
def assessEmpirical (policy : PolicyKey M P) (steps : List (Step M P S O)) :
    EmpiricalAssessment M P S O :=
  match admittedPrefix policy steps with
  | ([], none) => .unseen
  | (history, none) => .coherent history (sumF history)
  | (_, some .contradiction) => .contradiction
  | (_, some reason) => .malformed reason

inductive FRoute where | empirical | bootstrap deriving DecidableEq, Repr

structure SuppliedF where
  value : EReal
  route : FRoute

inductive ColdStartRefusal (M P : Type*) where
  | unseenWithoutPrior (policy : PolicyKey M P)
  | invalidBootstrap (policy : PolicyKey M P)
  | empiricalMalformed (policy : PolicyKey M P) (reason : Refusal)
  | empiricalContradiction (policy : PolicyKey M P)

/-- Exactly one route supplies F: coherent empirical evidence has precedence;
only truly unseen history may consult a valid external bootstrap prior. -/
def supplyF
    (scorerAuthority : Authority)
    (validParameters : Θ → Prop) (validDistribution : D → Prop)
    (ledgerAuthorizes : Ledger → Evidence → Prop)
    (updateDeclared : UpdateRule → Prop)
    (policy : PolicyKey M P) (steps : List (Step M P S O))
    (prior : Option (BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)) :
    Except (ColdStartRefusal M P) SuppliedF := by
  classical
  exact match assessEmpirical policy steps with
  | .coherent _ f => .ok ⟨f, .empirical⟩
  | .malformed reason => .error (.empiricalMalformed policy reason)
  | .contradiction => .error (.empiricalContradiction policy)
  | .unseen => match prior with
    | none => .error (.unseenWithoutPrior policy)
    | some b =>
      if ValidBootstrap scorerAuthority policy validParameters validDistribution
          ledgerAuthorizes updateDeclared b
      then .ok ⟨b.suppliedF, .bootstrap⟩
      else .error (.invalidBootstrap policy)

structure ColdStartPosterior where
  weights : List ℝ
  sources : List (PolicyKey M P × FRoute)

/-- Posterior comparison retains one route receipt per menu policy, in menu
order.  No missing value is replaced by numeric zero. -/
def collectSupplied
    (supply : PolicyKey M P → Except (ColdStartRefusal M P) SuppliedF) :
    List (PolicyKey M P) → Except (ColdStartRefusal M P) (List SuppliedF)
  | [] => .ok []
  | p :: ps => do
      let f ← supply p
      let rest ← collectSupplied supply ps
      return f :: rest

def machineWeightsAtSuppliedF
    (habit : PolicyKey M P → ℝ)
    (grade : PolicyKey M P → Holes.ExpectedFreeEnergyValue)
    (supply : PolicyKey M P → Except (ColdStartRefusal M P) SuppliedF)
    (tau : ℝ) (policies : List (PolicyKey M P)) :
    Except (ColdStartRefusal M P) (ColdStartPosterior (M := M) (P := P)) :=
  match collectSupplied supply policies with
  | .error e => .error e
  | .ok supplied =>
    .ok { weights := machineWeights habit grade
            (fun p => match supply p with | .ok f => f.value | .error _ => ⊤) tau policies
          sources := policies.zip (supplied.map (·.route)) }

theorem unseen_validExternalPrior_isAdmissible
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (hv : ValidBootstrap scorer policy validParameters validDistribution
      ledgerAuthorizes updateDeclared b) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy ([] : List (Step M P S O)) (some b) = .ok ⟨b.suppliedF, .bootstrap⟩ := by
  classical
  simp [supplyF, assessEmpirical, admittedPrefix, admitFrom, hv]

theorem unseen_withoutPrior_refuses :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy ([] : List (Step M P S O)) none = .error (.unseenWithoutPrior policy) := by
  simp [supplyF, assessEmpirical, admittedPrefix, admitFrom]

theorem unseen_withoutPrior_isNotZeroDefault (route : FRoute) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy ([] : List (Step M P S O)) none ≠ .ok ⟨(0 : EReal), route⟩ := by
  rw [unseen_withoutPrior_refuses]
  simp

theorem malformedEmpirical_neverBootstraps
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (steps : List (Step M P S O))
    (h : assessEmpirical policy steps = .malformed reason) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy steps (some b) = .error (.empiricalMalformed policy reason) := by
  simp [supplyF, h]

theorem contradictoryEmpirical_neverBootstraps
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (steps : List (Step M P S O))
    (h : assessEmpirical policy steps = .contradiction) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy steps (some b) = .error (.empiricalContradiction policy) := by
  simp [supplyF, h]

theorem selfAuthoredPrior_refuses
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (ha : b.authority = scorer) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      b.policy ([] : List (Step M P S O)) (some b) = .error (.invalidBootstrap b.policy) := by
  classical
  have hn : ¬ ValidBootstrap scorer b.policy validParameters validDistribution
      ledgerAuthorizes updateDeclared b := by
    intro hv
    exact hv.externalAuthority ha
  simp [supplyF, assessEmpirical, admittedPrefix, admitFrom, hn]

theorem priorForAnotherPolicy_refuses
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (hne : b.policy ≠ policy) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy ([] : List (Step M P S O)) (some b) = .error (.invalidBootstrap policy) := by
  classical
  have hn : ¬ ValidBootstrap scorer policy validParameters validDistribution
      ledgerAuthorizes updateDeclared b := by
    intro hv
    exact hne hv.exactPolicy
  simp [supplyF, assessEmpirical, admittedPrefix, admitFrom, hn]

theorem coherentEmpirical_takesAuthority
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (steps : List (Step M P S O))
    (h : assessEmpirical policy steps = .coherent history f) :
    supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      policy steps (some b) = .ok ⟨f, .empirical⟩ := by
  simp [supplyF, h]

/-- The declared update boundary: once a coherent enacted prefix is present,
the route is empirical regardless of the former bootstrap. -/
structure BootstrapUpdateObligation
    (ledgerAuthorizes : Ledger → Evidence → Prop)
    (updateDeclared : UpdateRule → Prop)
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (steps : List (Step M P S O)) : Prop where
  coherentAfterEnactment : ∃ history f, assessEmpirical b.policy steps = .coherent history f
  evidenceRecorded : ledgerAuthorizes b.evidenceLedger b.evidence
  updateStillDeclared : updateDeclared b.updateRule

theorem updateBoundary_retiresBootstrap
    (b : BootstrapPrior M P Θ D Authority Evidence Ledger UpdateRule)
    (steps : List (Step M P S O))
    (h : BootstrapUpdateObligation ledgerAuthorizes updateDeclared b steps) :
    ∃ (history : List (Step M P S O)) (f : EReal),
      supplyF scorer validParameters validDistribution ledgerAuthorizes updateDeclared
      b.policy steps (some b) = .ok ⟨f, .empirical⟩ := by
  obtain ⟨history, f, hcoherent⟩ := h.coherentAfterEnactment
  exact ⟨history, f, coherentEmpirical_takesAuthority b steps hcoherent⟩

end

#print axioms unseen_validExternalPrior_isAdmissible
#print axioms unseen_withoutPrior_refuses
#print axioms unseen_withoutPrior_isNotZeroDefault
#print axioms malformedEmpirical_neverBootstraps
#print axioms selfAuthoredPrior_refuses
#print axioms priorForAnotherPolicy_refuses
#print axioms coherentEmpirical_takesAuthority
#print axioms updateBoundary_retiresBootstrap

end DarkTower.WarMachine.Proof2.PrefixFreeEnergyColdStart
