/-
Copyright (c) 2026 Joseph Corneli. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import DarkTower.BaldwinMechanismPreregistration
import DarkTower.ExperimentalDesign
import Mathlib.Data.Nat.Choose.Basic

/-!
# Preregistration: MetaCA inherited-content response and held endpoints

This is the paid diagnostic battery admitted after the target-stationarity
pilot.  It closes the gap identified by `TN-baldwin-experiment-guidance`: gene
reachability is not evidence that inherited content affects post-learning
fitness.  Response is a paired exact sign test over `(seed, site)`, corrected
across the fixed family of at most 640 allele probes.  The full 80 by 256 map
then asks separately whether useful held endpoints exist.

The two gates must remain separate. A selectable endpoint without inherited
response diagnoses a gradient problem; inherited response without an endpoint
licenses guidance, not assimilation.
-/

namespace BaldwinMechanismBatteryPreregistration

open ExperimentPreregistration ExperimentalDesign

def expectedAlleleProbes : Nat := 640
def expectedMapRows : Nat := 80 * 256

/-- Upper tail of the fair-binomial null, kept in exact natural arithmetic. -/
def binomTail (n k : Nat) : Nat :=
  ((List.range (n + 1)).filter (fun i => k ≤ i)).foldl
    (fun acc i => acc + Nat.choose n i) 0

/-- Two-sided exact paired sign test with Bonferroni familywise alpha 0.05.

Ties have already been excluded, so `positive + negative` is the sample size.
The integer inequality is
`2 * tail / 2^n ≤ 0.05 / familySize`, hence
`40 * familySize * tail ≤ 2^n`. -/
def familywiseSignificant (positive negative familySize : Nat) : Bool :=
  let n := positive + negative
  let k := max positive negative
  decide (0 < n) && decide (0 < familySize) &&
    decide (40 * familySize * binomTail n k ≤ 2 ^ n)

theorem production_22_of_24_passes :
    familywiseSignificant 22 2 expectedAlleleProbes = true := by decide

theorem production_21_of_24_fails :
    familywiseSignificant 21 3 expectedAlleleProbes = false := by decide

structure Trace where
  sourceRevisionBound : Bool
  inputChecksumBound : Bool
  pairedSchedulesAligned : Bool
  alleleProbesObserved : Nat
  /-- Rows passing the preregistered two-sided exact paired sign test after
  Bonferroni correction over all 640 possible probes. -/
  familywiseResponsiveAlleles : Nat
  mapRowsObserved : Nat
  mapCheckpointsComplete : Bool
  /-- Held rule/locus combinations which preserve function and are at least as
  fit as the unheld baseline under the registered capacity cost. -/
  usefulHeldEndpoints : Nat
  artifactsChecksummed : Bool
  deriving Repr

def provenance : Flag Trace where
  name := "revision and evolved-population input are immutable"
  observable :=
    { name := "source revision and input checksum were re-observed"
      holds := fun t => t.sourceRevisionBound = true ∧ t.inputChecksumBound = true
      check := fun t => t.sourceRevisionBound && t.inputChecksumBound
      check_sound := by simp }

def pairing : Flag Trace where
  name := "candidate and baseline use identical evaluation units"
  observable :=
    { name := "every delta is paired on seed and site"
      holds := fun t => t.pairedSchedulesAligned = true
      check := fun t => t.pairedSchedulesAligned
      check_sound := by simp }

def complete : Flag Trace where
  name := "content response and full endpoint map are complete"
  observable :=
    { name := "all probes, map rows, checkpoints and checksums are present"
      holds := fun t =>
        t.alleleProbesObserved = expectedAlleleProbes ∧
        t.mapRowsObserved = expectedMapRows ∧
        t.mapCheckpointsComplete = true ∧ t.artifactsChecksummed = true
      check := fun t =>
        t.alleleProbesObserved == expectedAlleleProbes &&
        t.mapRowsObserved == expectedMapRows &&
        t.mapCheckpointsComplete && t.artifactsChecksummed
      check_sound := by
        intro t h
        simp only [Bool.and_eq_true, beq_iff_eq] at h
        obtain ⟨⟨⟨ha, hb⟩, hc⟩, hd⟩ := h
        exact ⟨ha, hb, hc, hd⟩ }

noncomputable def unchangedFieldArm : Arm where
  name := "unchanged inherited field paired baseline"
  neutral := true
  axes := []

noncomputable def allelePerturbationArm : Arm where
  name := "one inherited allele varied while the locus remains plastic"
  neutral := false
  axes := []

noncomputable def heldEndpointMapArm : Arm where
  name := "one locus held at each of 256 rules"
  neutral := false
  axes := []

noncomputable def base : Registration Trace where
  name := "metaca-inherited-content-response-and-endpoint-map"
  claim := .descriptive
  arms := [unchangedFieldArm, allelePerturbationArm, heldEndpointMapArm]
  flags := [provenance, pairing, complete]
  estimatedCost := 480
  budgetCap := 720
  teardownDeadline := some 720

def replication : ReplicationPlan where
  pilotSeeds := [1, 2, 3]
  confirmationSeeds := [101, 102, 103]
  pilotNonempty := by simp
  confirmationNonempty := by simp
  disjoint := by simp

inductive Outcome
  | invalid
  | contentFlatNoEndpoint
  | contentFlatUsefulEndpoint
  | contentResponsiveNoEndpoint
  | contentResponsiveUsefulEndpoint
  deriving DecidableEq, Repr

def classify (t : Trace) : Outcome :=
  if !t.sourceRevisionBound || !t.inputChecksumBound ||
      !t.pairedSchedulesAligned ||
      t.alleleProbesObserved != expectedAlleleProbes ||
      t.mapRowsObserved != expectedMapRows ||
      !t.mapCheckpointsComplete || !t.artifactsChecksummed then
    .invalid
  else if t.familywiseResponsiveAlleles = 0 then
    if t.usefulHeldEndpoints = 0 then .contentFlatNoEndpoint
    else .contentFlatUsefulEndpoint
  else if t.usefulHeldEndpoints = 0 then .contentResponsiveNoEndpoint
  else .contentResponsiveUsefulEndpoint

def decision : DecisionRule Trace Outcome where
  name := "separate inherited-content response from useful held endpoints"
  classify := classify

def invalidApparatus : StopRule Trace where
  name := "provenance, pairing or artifact completeness failed"
  fires := fun t =>
    t.sourceRevisionBound = false ∨ t.inputChecksumBound = false ∨
    t.pairedSchedulesAligned = false ∨
    t.alleleProbesObserved ≠ expectedAlleleProbes ∨
    t.mapRowsObserved ≠ expectedMapRows ∨
    t.mapCheckpointsComplete = false ∨ t.artifactsChecksummed = false
  check := fun t =>
    !t.sourceRevisionBound || !t.inputChecksumBound ||
    !t.pairedSchedulesAligned ||
    t.alleleProbesObserved != expectedAlleleProbes ||
    t.mapRowsObserved != expectedMapRows ||
    !t.mapCheckpointsComplete || !t.artifactsChecksummed
  check_iff := by
    intro t
    cases t.sourceRevisionBound <;> cases t.inputChecksumBound <;>
      cases t.pairedSchedulesAligned <;> cases t.mapCheckpointsComplete <;>
      cases t.artifactsChecksummed <;> simp

noncomputable def experiment : ProspectiveRegistration Trace Outcome where
  base := base
  replication := replication
  stopRules := [invalidApparatus]
  stopRulesNonempty := by simp
  decision := decision

theorem useful_endpoint_without_response_selects_gradient_repair (t : Trace)
    (hvalid : invalidApparatus.check t = false)
    (hflat : t.familywiseResponsiveAlleles = 0)
    (hendpoint : 0 < t.usefulHeldEndpoints) :
    classify t = .contentFlatUsefulEndpoint := by
  simp only [invalidApparatus] at hvalid
  simp [classify, hvalid, hflat, Nat.ne_of_gt hendpoint]

end BaldwinMechanismBatteryPreregistration
