import DarkTower.WarMachine.R15StrategicTarget

/-!
# Supplied strategic-focus candidate correspondence

This module adapts a finite list of already supplied target relations to
`R15StrategicTarget.StrategicTickRecord`.  It is deliberately only a
supplied-value correspondence: it is not a runtime decoder and it establishes
neither provenance nor authenticity.  In particular, it introduces no runtime
encoding for an unknown or off-facet relation.

Adaptation is all-or-nothing.  One absent relation refuses the whole list;
present data, including a relation paired with the wrong scored class, is
preserved for `StrategicTickConforms` to judge.  Candidate order, targets and
scored classes, and the supplied horizon and preference function are unchanged.
-/

namespace DarkTower.WarMachine.R20StrategicFocusRowCorrespondence

open CTauClassPreference R15StrategicTarget

/-- Raw supplied values at the formal boundary.  `target` is already Lean's
`Target`; no runtime identity translation is performed here. -/
structure SuppliedCandidate where
  target : Target
  relation : Option TargetRelation
  scoredClass : Option EndingClass
  deriving DecidableEq, Repr

/-- Exact positional correspondence between a supplied candidate and the
existing strategic candidate receipt. -/
def CandidateAdapts (raw : SuppliedCandidate) (out : CandidateClassReceipt) : Prop :=
  ∃ relation, raw.relation = some relation ∧
    out = ⟨raw.target, relation, raw.scoredClass⟩

/-- Total, all-or-nothing adaptation.  No absent element is filtered. -/
def adaptCandidates : List SuppliedCandidate → Option (List CandidateClassReceipt)
  | [] => some []
  | raw :: rest => do
      let relation ← raw.relation
      let adaptedRest ← adaptCandidates rest
      pure (⟨raw.target, relation, raw.scoredClass⟩ :: adaptedRest)

/-- Successful adaptation preserves every position and every supplied value. -/
theorem adaptCandidates_eq_some_iff (raw : List SuppliedCandidate)
    (out : List CandidateClassReceipt) :
    adaptCandidates raw = some out ↔ List.Forall₂ CandidateAdapts raw out := by
  induction raw generalizing out with
  | nil => cases out <;> simp [adaptCandidates]
  | cons head tail ih =>
      cases relationEq : head.relation with
      | none =>
          constructor
          · simp [adaptCandidates, relationEq]
          · intro relates
            cases relates with
            | cons headRel _ =>
                obtain ⟨relation, present, _⟩ := headRel
                rw [relationEq] at present
                contradiction
      | some relation =>
          cases out with
          | nil =>
              cases restEq : adaptCandidates tail <;>
                simp [adaptCandidates, relationEq, restEq]
          | cons outHead outTail =>
              cases restEq : adaptCandidates tail with
              | none =>
                  constructor
                  · simp [adaptCandidates, relationEq, restEq]
                  · intro relates
                    cases relates with
                    | cons _ tailRel =>
                        have present := (ih outTail).2 tailRel
                        rw [restEq] at present
                        contradiction
              | some adaptedTail =>
                  constructor
                  · intro adapted
                    have listEq :
                        (⟨head.target, relation, head.scoredClass⟩ :: adaptedTail) =
                          outHead :: outTail := by
                      simpa [adaptCandidates, relationEq, restEq] using adapted
                    cases listEq
                    exact .cons ⟨relation, relationEq, rfl⟩
                      ((ih outTail).1 restEq)
                  · intro relates
                    cases relates with
                    | cons headRel tailRel =>
                        obtain ⟨r, present, outEq⟩ := headRel
                        rw [relationEq] at present
                        cases present
                        subst outHead
                        have tailEq := (ih outTail).2 tailRel
                        rw [restEq] at tailEq
                        cases tailEq
                        simp [adaptCandidates, relationEq, restEq]

/-- Keep the supplied focus, horizon and preference function unchanged. -/
def adaptTick (focus horizon : Nat) (raw : List SuppliedCandidate)
    (preference : Nat → Distribution) : Option StrategicTickRecord := do
  let candidates ← adaptCandidates raw
  pure ⟨focus, horizon, candidates, preference⟩

theorem adaptTick_eq_some_iff (focus horizon : Nat) (raw : List SuppliedCandidate)
    (preference : Nat → Distribution) (tick : StrategicTickRecord) :
    adaptTick focus horizon raw preference = some tick ↔
      ∃ candidates, adaptCandidates raw = some candidates ∧
        tick = ⟨focus, horizon, candidates, preference⟩ := by
  cases adaptedEq : adaptCandidates raw <;> simp [adaptTick, adaptedEq, eq_comm]

/-- The supplied equation checked for every candidate, including its relation's
presence. -/
def SuppliedClassesAgree (raw : List SuppliedCandidate) : Prop :=
  ∀ candidate ∈ raw, ∃ relation,
    candidate.relation = some relation ∧ candidate.scoredClass = scorerClass relation

private theorem adapted_classes_iff (raw : List SuppliedCandidate)
    (out : List CandidateClassReceipt) (adapted : List.Forall₂ CandidateAdapts raw out) :
    (∀ candidate ∈ out,
      candidate.scoredClass = scorerClass candidate.recordedRelation) ↔
      SuppliedClassesAgree raw := by
  induction adapted with
  | nil => simp [SuppliedClassesAgree]
  | @cons rawHead outHead rawTail outTail headRel tailRel ih =>
      obtain ⟨relation, relationEq, outEq⟩ := headRel
      subst outHead
      simp only [List.forall_mem_cons, ih, SuppliedClassesAgree]
      constructor
      · rintro ⟨headGood, tailGood⟩
        refine ⟨?_, tailGood⟩
        exact ⟨relation, relationEq, headGood⟩
      · rintro ⟨headGood, tailGood⟩
        obtain ⟨r, present, classEq⟩ := headGood
        rw [relationEq] at present
        cases present
        exact ⟨classEq, tailGood⟩

/-- A successfully adapted finite tick conforms exactly when every supplied
relation/class pair agrees and the independently supplied schedule is the
existing canonical in-horizon schedule. -/
theorem adapted_tick_conforms_iff (focus horizon : Nat) (raw : List SuppliedCandidate)
    (preference : Nat → Distribution) (tick : StrategicTickRecord)
    (adapted : adaptTick focus horizon raw preference = some tick) :
    StrategicTickConforms tick ↔
      SuppliedClassesAgree raw ∧
      (∀ tau, 1 ≤ tau → tau ≤ horizon →
        preference tau = classPreference horizon tau) := by
  obtain ⟨candidates, candidatesEq, rfl⟩ :=
    (adaptTick_eq_some_iff focus horizon raw preference tick).1 adapted
  have relates := (adaptCandidates_eq_some_iff raw candidates).1 candidatesEq
  simp only [StrategicTickConforms, outcomeClass]
  rw [adapted_classes_iff raw candidates relates]

/-- The accepted singleton result is a direct instance of the finite adapter. -/
theorem singleton_conformance (focus target horizon : Nat)
    (relation : TargetRelation) (scored : Option EndingClass)
    (preference : Nat → Distribution) :
    ∃ tick, adaptTick focus horizon
        [⟨target, some relation, scored⟩] preference = some tick ∧
      (StrategicTickConforms tick ↔
        scored = scorerClass relation ∧
        (∀ tau, 1 ≤ tau → tau ≤ horizon →
          preference tau = classPreference horizon tau)) := by
  refine ⟨⟨focus, horizon, [⟨target, relation, scored⟩], preference⟩, rfl, ?_⟩
  simpa [SuppliedClassesAgree] using adapted_tick_conforms_iff focus horizon
    [⟨target, some relation, scored⟩] preference
    ⟨focus, horizon, [⟨target, relation, scored⟩], preference⟩ rfl

/-! ## Boundary and discriminating controls -/

def goodRaw : List SuppliedCandidate :=
  [⟨7, some .focus, some .focused⟩,
   ⟨8, some .associated, some .related⟩,
   ⟨9, some (.other 4), none⟩]

def goodTick : StrategicTickRecord :=
  ⟨7, 2,
   [⟨7, .focus, some .focused⟩,
    ⟨8, .associated, some .related⟩,
    ⟨9, .other 4, none⟩],
   classPreference 2⟩

theorem positive_multi_candidate :
    adaptTick 7 2 goodRaw (classPreference 2) = some goodTick ∧
      StrategicTickConforms goodTick := by
  constructor
  · rfl
  · simp [goodTick, StrategicTickConforms, outcomeClass, scorerClass]

theorem missing_middle_refuses :
    adaptCandidates
      [⟨7, some .focus, some .focused⟩,
       ⟨8, none, some .related⟩,
       ⟨9, some .usefulElsewhere, some .unrelated⟩] = none := by
  rfl

def wrongSecondTick : StrategicTickRecord :=
  ⟨7, 2,
   [⟨7, .focus, some .focused⟩,
    ⟨8, .associated, some .focused⟩],
   classPreference 2⟩

theorem wrong_nonfirst_class_remains_present :
    adaptTick 7 2
      [⟨7, some .focus, some .focused⟩,
       ⟨8, some .associated, some .focused⟩]
      (classPreference 2) = some wrongSecondTick := by
  rfl

theorem wrong_nonfirst_class_rejected : ¬ StrategicTickConforms wrongSecondTick := by
  simp [wrongSecondTick, StrategicTickConforms, outcomeClass, scorerClass]

def wrongScheduleTick : StrategicTickRecord :=
  ⟨7, 2,
   [⟨7, .focus, some .focused⟩, ⟨8, .associated, some .related⟩],
   fun _ => terminalPreference⟩

theorem wrong_schedule_rejected : ¬ StrategicTickConforms wrongScheduleTick := by
  intro conforms
  have schedule := conforms.2 1 (by norm_num) (by norm_num [wrongScheduleTick])
  have focused := congrFun schedule EndingClass.focused
  norm_num [wrongScheduleTick, classPreference, terminalPreference, waitingPreference] at focused

theorem empty_list_preserved (focus horizon : Nat) (preference : Nat → Distribution) :
    adaptTick focus horizon [] preference = some ⟨focus, horizon, [], preference⟩ := by
  rfl

theorem empty_list_conforms_iff (focus horizon : Nat) (preference : Nat → Distribution) :
    StrategicTickConforms ⟨focus, horizon, [], preference⟩ ↔
      (∀ tau, 1 ≤ tau → tau ≤ horizon →
        preference tau = classPreference horizon tau) := by
  simp [StrategicTickConforms]

theorem zero_horizon_preserved (focus : Nat) (raw : List SuppliedCandidate)
    (preference : Nat → Distribution) (tick : StrategicTickRecord)
    (adapted : adaptTick focus 0 raw preference = some tick) :
    StrategicTickConforms tick ↔ SuppliedClassesAgree raw := by
  rw [adapted_tick_conforms_iff focus 0 raw preference tick adapted]
  constructor
  · exact And.left
  · intro agrees
    refine ⟨agrees, ?_⟩
    intro tau positive atZero
    omega

#print axioms adaptCandidates_eq_some_iff
#print axioms adapted_tick_conforms_iff
#print axioms singleton_conformance
#print axioms positive_multi_candidate
#print axioms missing_middle_refuses
#print axioms wrong_nonfirst_class_remains_present
#print axioms wrong_nonfirst_class_rejected
#print axioms wrong_schedule_rejected
#print axioms empty_list_preserved
#print axioms empty_list_conforms_iff
#print axioms zero_horizon_preserved

end DarkTower.WarMachine.R20StrategicFocusRowCorrespondence
