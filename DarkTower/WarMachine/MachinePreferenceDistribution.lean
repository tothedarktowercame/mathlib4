import DarkTower.WarMachine.F10RuledCarrier
import DarkTower.WarMachine.MachineModelSpec

namespace DarkTower.WarMachine.MachinePreferenceDistribution

open Holes
open F10RuledCarrier
open MachineModelSpec

/-- The ordered preference composition recorded by the production layer
declaration. Only the ruled outcome seed contributes mass to this tagged sum;
the introspective channel C is outside it, the serendipity region is empty,
and the mission-grain layer remains undeclared. -/
inductive Layer where
  | ruledOutcome | introspective | serendipity | mission
  deriving DecidableEq, Repr

def orderedLayers : List Layer :=
  [.ruledOutcome, .introspective, .serendipity, .mission]

/-- Keyword-sorted support order used by the Clojure constructor after it has
derived the member set from MachineModelSpec. This is ordering, not a second
support authority. -/
def machineSupport : List FlightDisposition :=
  [.abstained, .agentUnavailable, .artifactOnly, .buildFailed, .cancelled,
   .dispatchFailed, .groundedChange, .groundedNoChange, .guardrailRefusal,
   .incomplete, .noSelection, .substrateUnavailable]

noncomputable def machineC : PreferenceDistribution SeedObs where
  support := fun _ => machineSupport.map organisationOutcome
  mass := seed.mass
  nonnegative := seed.nonnegative
  support_nodup := by intro; simp [machineSupport, organisationOutcome]
  mass_eq_zero_of_not_mem := by intro s o h; rcases o with ⟨v, x⟩; cases v <;> cases x <;> simp_all [machineSupport, organisationOutcome, seed]
  normalised := by intro _; norm_num [machineSupport, organisationOutcome, seed]

theorem machineC_normalised :
    ∀ u, ((machineC.support u).map (machineC.mass u)).sum = 1 :=
  machineC.normalised

theorem machineC_nonnegative : ∀ u o, 0 ≤ machineC.mass u o :=
  machineC.nonnegative

theorem machineC_unconditional (u₁ u₂ : Unit) (o : Outcome SeedObs) :
    machineC.mass u₁ o = machineC.mass u₂ o := by
  cases u₁; cases u₂; rfl

theorem machineC_support_partition (o : Outcome SeedObs)
    (h : o ∈ machineC.support ()) : o.1 = .organization := by
  simp only [machineC, machineSupport, List.mem_map] at h
  rcases h with ⟨d, _, rfl⟩
  rfl

theorem machineC_named_zero (d : FlightDisposition)
    (h : d ∈ namedZeroDispositions) :
    machineC.mass () (organisationOutcome d) = 0 :=
  seedMass_zero_of_mem_namedZeros d h

theorem machineC_named_empty_nouns (o : Outcome SeedObs)
    (hm : o ∈ machineC.support ()) (hv : o.1 = .nouns) : False := by
  have hp := machineC_support_partition o hm
  simp_all

theorem machineC_named_empty_verbs (o : Outcome SeedObs)
    (hm : o ∈ machineC.support ()) (hv : o.1 = .verbs) : False := by
  have hp := machineC_support_partition o hm
  simp_all

theorem machineC_first_supported :
    (machineC.support ()).head? = some (organisationOutcome .abstained) := by
  rfl

theorem machineC_first_positive :
    ((machineC.support ()).dropWhile (fun o => decide (machineC.mass () o = 0))).head? =
      some (organisationOutcome .agentUnavailable) := by
  norm_num [machineC, machineSupport, organisationOutcome, seed]

theorem evidence_consumption_refused :
    evidenceConsumable .owed = false :=
  evidence_request_refused .owed

end DarkTower.WarMachine.MachinePreferenceDistribution
