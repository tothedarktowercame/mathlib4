import DarkTower.WarMachine.HistoricalMisclassificationCorrection

/-!
# Medic sweep provenance

This module leaves `medicProcess` and `medicSweep` unchanged.  `AdmittedSweep`
is a proof trace for a sweep beginning with an empty correction log.  Every
step must be the actual result of `medicProcess` and must append.  Thus no
arbitrary prepopulated correction is promoted to qualified evidence.

The existing `latestEntries` computation supplies one latest entry per injury;
this module adds no authenticity or serving claim.
-/

namespace DarkTower.WarMachine.MedicSweepProvenance

open HistoricalMisclassificationCorrection

structure AdmittedStep (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) (before after : MedicState) where
  request : MedicRequest
  current : InjuryEntry
  evidence : MedicEvidence
  evidence_present : request.evidence = some evidence
  latest_matches : latestFor before.history request.candidate.injury = some current
  qualified : medicQualified misclassification genuine current
    request.candidate evidence = true
  process_appends : medicProcess misclassification genuine request.evidence before
    request.candidate = ⟨.appended, after⟩

inductive AdmittedSweep (misclassification : MisclassificationAdmission)
    (genuine : GenuineRepairAdmission) : MedicState → List MedicRequest → MedicState → Prop
  | nil (initial : MedicState) :
      AdmittedSweep misclassification genuine initial [] initial
  | cons {before middle after : MedicState} {request : MedicRequest}
      {rest : List MedicRequest}
      (step : AdmittedStep misclassification genuine before middle)
      (same_request : step.request = request)
      (tail : AdmittedSweep misclassification genuine middle rest after) :
      AdmittedSweep misclassification genuine before (request :: rest) after

theorem medicProcess_appended_corrections
    (h : medicProcess misclassification genuine evidence before candidate =
      ⟨.appended, after⟩) :
    after.corrections = before.corrections ++ [candidate] := by
  unfold medicProcess at h
  grind

theorem admittedStep_appends_candidate
    (step : AdmittedStep misclassification genuine before after) :
    after.corrections = before.corrections ++ [step.request.candidate] := by
  exact medicProcess_appended_corrections step.process_appends

theorem admittedSweep_preserves_history
    (sweep : AdmittedSweep misclassification genuine initial requests final) :
    final.history = initial.history := by
  induction sweep with
  | nil => rfl
  | @cons before middle after request rest step same_request tail ih =>
      rw [ih]
      have hp := medicProcess_preserves_history
        (misclassification := misclassification) (genuine := genuine)
        (evidence := step.request.evidence) (state := before)
        (candidate := step.request.candidate)
      rw [step.process_appends] at hp
      exact hp

theorem admittedSweep_executes_medicSweep
    (sweep : AdmittedSweep misclassification genuine initial requests final) :
    medicSweep misclassification genuine initial requests = final := by
  induction sweep with
  | nil => rfl
  | cons step same_request tail ih =>
      simp only [medicSweep]
      subst same_request
      rw [step.process_appends]
      exact ih

theorem admittedSweep_corrections_exact
    (sweep : AdmittedSweep misclassification genuine initial requests final) :
    final.corrections = initial.corrections ++ requests.map MedicRequest.candidate := by
  induction sweep with
  | nil => simp
  | cons step same_request tail ih =>
      rw [ih, admittedStep_appends_candidate step, same_request]
      simp [List.append_assoc]

theorem admittedSweep_from_empty_corrections_exact
    (sweep : AdmittedSweep misclassification genuine initial requests final)
    (empty : initial.corrections = []) :
    final.corrections = requests.map MedicRequest.candidate := by
  simpa [empty] using admittedSweep_corrections_exact sweep

theorem request_has_admitted_step
    (sweep : AdmittedSweep misclassification genuine initial requests final)
    (hrequest : request ∈ requests) :
    ∃ before after current evidence,
      request.evidence = some evidence ∧
      latestFor before.history request.candidate.injury = some current ∧
      medicQualified misclassification genuine current request.candidate evidence = true ∧
      medicProcess misclassification genuine request.evidence before request.candidate =
        ⟨.appended, after⟩ := by
  induction sweep with
  | nil => simp at hrequest
  | @cons before middle final head rest step same_request tail ih =>
      rcases List.mem_cons.mp hrequest with hhead | htail
      · subst request
        subst head
        refine ⟨before, middle, step.current, step.evidence,
          step.evidence_present, ?_, step.qualified, ?_⟩
        · exact step.latest_matches
        · exact step.process_appends
      · exact ih htail

theorem correction_has_admitted_step
    (sweep : AdmittedSweep misclassification genuine initial requests final)
    (empty : initial.corrections = [])
    (hcorrection : correction ∈ final.corrections) :
    ∃ before after request current evidence,
      request ∈ requests ∧ request.candidate = correction ∧
      request.evidence = some evidence ∧
      latestFor before.history correction.injury = some current ∧
      medicQualified misclassification genuine current correction evidence = true ∧
      medicProcess misclassification genuine request.evidence before correction =
        ⟨.appended, after⟩ := by
  rw [admittedSweep_from_empty_corrections_exact sweep empty] at hcorrection
  rcases List.mem_map.mp hcorrection with ⟨request, hrequest, rfl⟩
  rcases request_has_admitted_step sweep hrequest with ⟨b, a, c, e, he, hl, hq, hp⟩
  exact ⟨b, a, request, c, e, hrequest, rfl, he, hl, hq, hp⟩

theorem effectiveActiveOccurrence_iff
    (occurrence : Occurrence) :
    occurrence ∈ medicEffectiveActiveOccurrences state ↔
      (∃ entry ∈ latestEntries state.history,
        entry.active = true ∧ entry.occurrence = occurrence) ∧
      occurrence ∉ state.corrections.map MedicCorrection.occurrence := by
  simp only [medicEffectiveActiveOccurrences, List.mem_filter, List.mem_map]
  aesop

theorem effectiveActive_empty_iff_latest_covered :
    medicEffectiveActiveOccurrences state = [] ↔
      ∀ entry ∈ latestEntries state.history, entry.active = true →
        entry.occurrence ∈ state.corrections.map MedicCorrection.occurrence := by
  constructor
  · intro hempty entry hlatest hactive
    by_contra hmissing
    have : entry.occurrence ∈ medicEffectiveActiveOccurrences state := by
      rw [effectiveActiveOccurrence_iff]
      exact ⟨⟨entry, hlatest, hactive, rfl⟩, hmissing⟩
    simpa [hempty] using this
  · intro covered
    apply List.eq_nil_iff_forall_not_mem.mpr
    intro occurrence hactive
    rw [effectiveActiveOccurrence_iff] at hactive
    rcases hactive with ⟨⟨entry, hlatest, hentryactive, rfl⟩, hmissing⟩
    exact hmissing (covered entry hlatest hentryactive)

theorem admittedSweep_clear_all_iff
    (sweep : AdmittedSweep misclassification genuine initial requests final)
    (empty : initial.corrections = []) :
    medicEffectiveActiveOccurrences final = [] ↔
      ∀ entry ∈ latestEntries final.history, entry.active = true →
        ∃ correction ∈ final.corrections,
          correction.occurrence = entry.occurrence ∧
          ∃ before after request current evidence,
            request ∈ requests ∧ request.candidate = correction ∧
            request.evidence = some evidence ∧
            latestFor before.history correction.injury = some current ∧
            medicQualified misclassification genuine current correction evidence = true ∧
            medicProcess misclassification genuine request.evidence before correction =
              ⟨.appended, after⟩ := by
  rw [effectiveActive_empty_iff_latest_covered]
  constructor
  · intro covered entry hlatest hactive
    rcases List.mem_map.mp (covered entry hlatest hactive) with
      ⟨correction, hmember, heq⟩
    refine ⟨correction, hmember, heq, ?_⟩
    exact correction_has_admitted_step sweep empty hmember
  · intro covered entry hlatest hactive
    rcases covered entry hlatest hactive with
      ⟨correction, hmember, heq, _⟩
    exact List.mem_map.mpr ⟨correction, hmember, heq⟩

def forgedState : MedicState := ⟨[a9Entry], [a9Candidate]⟩

theorem forged_prepopulation_not_admitted :
    ¬ ∃ (_trace : AdmittedSweep admitA9 noGenuine forgedState [] forgedState),
      forgedState.corrections = [] := by
  simp [forgedState]

end DarkTower.WarMachine.MedicSweepProvenance
