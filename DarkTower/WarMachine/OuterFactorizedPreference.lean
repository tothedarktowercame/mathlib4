import DarkTower.WarMachine.FactorizedPreferenceSemantics

/-!
# Outer completion, then relevance, then conditional gain

This is the certificate contract for the outer producer, not a replacement kit.
The order is the law; calibrated numbers are Joe's to authorize. The numeric
functions below describe ONLY the current 55/35/5/5/0 × 1/2/3 kit and exhibit why
its flat product is not a certificate. No new preference weights are chosen.
-/
namespace DarkTower.WarMachine.OuterFactorizedPreference


inductive Ending where
  | focused | related | unrelated | stopTheLine | notYetEvaluated
  deriving DecidableEq, Repr

inductive Gain where
  | none | one | several
  deriving DecidableEq, Repr

structure OuterOutcome where
  ending : Ending
  gain : Gain
  deriving DecidableEq, Repr

/-- Relevance is meaningful only for truthfully completed work. The producer
must retain the terminal receipt warranting a completed ending; this map does
not itself verify external execution. Unmeasured is not a failed execution. -/
def project (o : OuterOutcome) : FactorizedPreferenceSemantics.Outcome :=
  match o.ending with
  | .focused => ⟨.completed, some .focused⟩
  | .related => ⟨.completed, some .related⟩
  | .unrelated => ⟨.completed, some .unrelated⟩
  | .stopTheLine => ⟨.notCompleted, none⟩
  | .notYetEvaluated => ⟨.unmeasured, none⟩

def Gain.Preferred : Gain → Gain → Prop
  | .several, .one | .several, .none | .one, .none => True
  | _, _ => False

/-- Gain breaks ties only after completion and conditional relevance agree.
It cannot purchase completion, relevance, or a comparison with unmeasured. -/
def Preferred (c : FactorizedPreferenceSemantics.RelevanceCalibration) (a b : OuterOutcome) : Prop :=
  FactorizedPreferenceSemantics.Preferred c (project a) (project b) ∨
    ((project a).completion = .completed ∧ (project b).completion = .completed ∧
     (project a).relevance = (project b).relevance ∧ Gain.Preferred a.gain b.gain)

inductive GainLaw where
  | completionThenRelevanceThenGain
  | flatProduct
  deriving DecidableEq, Repr

/-- The base retains calibration, independent selector/calibration authorities,
factorization identity/version/authority and their authorization receipts.
The outer extension declares the conditional gain law, never fresh kit numbers. -/
structure Certificate where
  base : FactorizedPreferenceSemantics.Certificate
  gainLaw : GainLaw
  deriving DecidableEq, Repr

def Certificate.Valid (calibrationRegistry : List FactorizedPreferenceSemantics.CalibrationAuthorization)
    (factorizationRegistry : List FactorizedPreferenceSemantics.FactorizationAuthorization) (c : Certificate) : Prop :=
  c.base.Valid calibrationRegistry factorizationRegistry ∧
    c.gainLaw = .completionThenRelevanceThenGain

theorem outer_certificate_retains_authorized_base
    (cs : List FactorizedPreferenceSemantics.CalibrationAuthorization) (fs : List FactorizedPreferenceSemantics.FactorizationAuthorization)
    (c : Certificate) (h : c.Valid cs fs) : c.base.Valid cs fs := h.1

theorem authorized_base_with_conditional_gain_valid
    (cs : List FactorizedPreferenceSemantics.CalibrationAuthorization) (fs : List FactorizedPreferenceSemantics.FactorizationAuthorization)
    (base : FactorizedPreferenceSemantics.Certificate) (h : base.Valid cs fs) :
    (Certificate.mk base .completionThenRelevanceThenGain).Valid cs fs := ⟨h, rfl⟩

theorem flat_gain_certificate_invalid
    (cs : List FactorizedPreferenceSemantics.CalibrationAuthorization) (fs : List FactorizedPreferenceSemantics.FactorizationAuthorization)
    (base : FactorizedPreferenceSemantics.Certificate) : ¬ (Certificate.mk base .flatProduct).Valid cs fs := by
  intro h
  cases h.2

theorem project_valid (o : OuterOutcome) : (project o).Valid := by
  cases h : o.ending <;> simp [project, h, FactorizedPreferenceSemantics.Outcome.Valid]

theorem completion_before_stopped (c : FactorizedPreferenceSemantics.RelevanceCalibration) (a b : OuterOutcome)
    (ha : (project a).completion = .completed)
    (hb : (project b).completion = .notCompleted) : Preferred c a b := by
  exact Or.inl (FactorizedPreferenceSemantics.completion_always_outranks_noncompletion c _ _
    (project_valid a) (project_valid b) ha hb)

theorem unknown_incomparable (c : FactorizedPreferenceSemantics.RelevanceCalibration) (g : Gain) (o : OuterOutcome) :
    ¬ Preferred c ⟨.notYetEvaluated, g⟩ o ∧
    ¬ Preferred c o ⟨.notYetEvaluated, g⟩ := by
  cases o.ending <;> simp [Preferred, project, FactorizedPreferenceSemantics.Preferred, FactorizedPreferenceSemantics.Outcome.Valid]

theorem several_before_one_when_completed (c : FactorizedPreferenceSemantics.RelevanceCalibration) :
    Preferred c ⟨.focused, .several⟩ ⟨.focused, .one⟩ := by
  exact Or.inr ⟨rfl, rfl, rfl, trivial⟩

theorem one_before_none_when_completed (c : FactorizedPreferenceSemantics.RelevanceCalibration) :
    Preferred c ⟨.focused, .one⟩ ⟨.focused, .none⟩ := by
  exact Or.inr ⟨rfl, rfl, rfl, trivial⟩

/-- Recorded kit weights, not proposed calibration parameters. Multiplying by
a common normalization does not alter these comparisons. -/
def currentEndingWeight : Ending → Nat
  | .focused => 55
  | .related => 35
  | .unrelated => 5
  | .stopTheLine => 5
  | .notYetEvaluated => 0

def currentGainWeight : Gain → Nat
  | .none => 1
  | .one => 2
  | .several => 3

def currentKitWeight (o : OuterOutcome) : Nat :=
  currentEndingWeight o.ending * currentGainWeight o.gain

theorem kit_orders_stopped_above_unmeasured :
    currentKitWeight ⟨.stopTheLine, .none⟩ >
      currentKitWeight ⟨.notYetEvaluated, .none⟩ := by decide

theorem law_does_not_order_stopped_above_unmeasured (c : FactorizedPreferenceSemantics.RelevanceCalibration) :
    ¬ Preferred c ⟨.stopTheLine, .none⟩ ⟨.notYetEvaluated, .none⟩ :=
  (unknown_incomparable c .none ⟨.stopTheLine, .none⟩).2

theorem kit_ties_completed_unrelated_and_stopped :
    currentKitWeight ⟨.unrelated, .none⟩ = currentKitWeight ⟨.stopTheLine, .none⟩ := by decide

theorem law_strictly_prefers_completed_unrelated (c : FactorizedPreferenceSemantics.RelevanceCalibration) :
    Preferred c ⟨.unrelated, .none⟩ ⟨.stopTheLine, .none⟩ :=
  completion_before_stopped c _ _ rfl rfl

/-- A strict reversal on completed outcomes: 105 > 55 in the flat product,
while conditional relevance ranks focused ahead of related regardless of gain. -/
theorem kit_reverses_conditional_relevance :
    currentKitWeight ⟨.related, .several⟩ > currentKitWeight ⟨.focused, .none⟩ := by decide

theorem law_prefers_focused_none_to_related_several
    (c : FactorizedPreferenceSemantics.RelevanceCalibration) (selector : FactorizedPreferenceSemantics.Id) (h : c.Valid selector) :
    Preferred c ⟨.focused, .none⟩ ⟨.related, .several⟩ :=
  Or.inl (FactorizedPreferenceSemantics.focused_before_related c selector h)

#print axioms law_prefers_focused_none_to_related_several
#print axioms authorized_base_with_conditional_gain_valid
end DarkTower.WarMachine.OuterFactorizedPreference
