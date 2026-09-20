import DarkTower.WarMachine.TokenPreference

/-! Owned preference families: per-owner C vectors, divergence reported,
never averaged.

Transcribes the operator rulings of 2026-09-20 (futon2
`holes/labs/wm-contract/DECLARATION-machine-aim-2026-09-20.md`, "RULING —
multi-owner conflict rule": per-owner C vectors scored separately with
divergence reported; a typed refusal when owners conflict on an outcome;
never a weighted average) onto the P6 preference model
(`TokenPreference.lean`), which this module extends without modifying.

An `OwnedPreferences` value is a family of `PreferenceSpec`s indexed by
owner (e.g. `joe/eat-your-tail`, `rob/dont-reinvent-the-wheel`, plus the
community-event entries). Its only joint query is `jointReport`, whose
result is either the tuple of per-owner scores or a typed refusal naming
a conflicted outcome. **This API deliberately provides no function from a
family of owners to a single scalar.** Erasing disagreement into a number
is the failure mode the ruling forbids; downstream consumers get every
owner's score or none.

Like `TokenPreference.lean`, this is a mathematical model, not a
correspondence claim about the live machine; owner identity, parameter
acquisition, and outcome interpretation are external. The companion
conformance obligations on declarations (want tokens producible and
generalizable; evidence witnesses bound to artifacts EXTERNAL to the run
— an artifact the run itself writes fails review) live in the futon2
contract layer, since they constrain acquisition, which this model
declares out of scope.
-/

namespace DarkTower.WarMachine.TokenPreferenceOwned

open DarkTower.WarMachine.TokenPreference

variable {Owner : Type*} {V : Type*} [Fintype V] [DecidableEq V]

noncomputable section

/-- A family of declared preference specifications, one per owner. -/
structure OwnedPreferences (Owner V : Type*) [Fintype V] [DecidableEq V] where
  /-- Each owner's own declared spec; owners are never pooled. -/
  spec : Owner → PreferenceSpec V

namespace OwnedPreferences

variable (P : OwnedPreferences Owner V)

/-- Owners conflict on an outcome when one gives it positive preference
mass and another rules it zero. (Zero mass is exactly membership in that
owner's ruled-zero sets, by `preference_eq_zero_iff`.) -/
def ConflictOn (P : OwnedPreferences Owner V) (o : Finset V) : Prop :=
  ∃ a b : Owner, 0 < (P.spec a).preference o ∧ (P.spec b).preference o = 0

/-- The typed result of a joint query: every owner's score, or a refusal
naming the conflicted outcome. There is no third constructor; in
particular there is no aggregate. -/
inductive Verdict (Owner V : Type*) [Fintype V] [DecidableEq V]
  | scores (perOwner : Owner → ℝ)
  | refusal (o : Finset V)

open Classical in
/-- The only joint query. Conflict yields a typed refusal carrying the
outcome; otherwise every owner's score is reported unmodified. -/
def jointReport (P : OwnedPreferences Owner V) (o : Finset V) :
    Verdict Owner V :=
  if ConflictOn P o then Verdict.refusal o
  else Verdict.scores (fun a => (P.spec a).preference o)

/-- Reported scores are each owner's own preference value, untouched: no
averaging, reweighting, or normalization across owners. -/
theorem jointReport_scores_faithful (P : OwnedPreferences Owner V)
    (o : Finset V) (f : Owner → ℝ)
    (h : jointReport P o = Verdict.scores f) :
    ∀ a : Owner, f a = (P.spec a).preference o := by
  classical
  unfold jointReport at h
  by_cases hc : ConflictOn P o
  · simp [hc] at h
  · simp only [hc, if_false] at h
    intro a
    have := congrArg (fun v => match v with
      | Verdict.scores g => g a
      | Verdict.refusal _ => (0:ℝ)) h
    simpa using this.symm

/-- A refusal is only issued on a genuine conflict: some owner scores the
outcome positive while another rules it zero. -/
theorem jointReport_refusal_iff (P : OwnedPreferences Owner V)
    (o : Finset V) :
    jointReport P o = Verdict.refusal o ↔ ConflictOn P o := by
  classical
  unfold jointReport
  by_cases hc : ConflictOn P o
  · simp [hc]
  · simp [hc]

/-- Conflict unpacked to the ruled-zero sets: owners conflict on `o`
exactly when `o` is outside one owner's ruled-zero sets and inside
another's. Divergence is a fact about declared rulings, not about
magnitudes. -/
theorem conflictOn_iff_zeroed (P : OwnedPreferences Owner V) (o : Finset V) :
    ConflictOn P o ↔
      ∃ a b : Owner, o ∉ (P.spec a).zeroed ∧ o ∈ (P.spec b).zeroed := by
  unfold ConflictOn
  constructor
  · rintro ⟨a, b, hpos, hzero⟩
    exact ⟨a, b, (PreferenceSpec.preference_pos_iff _ _).mp hpos,
      (PreferenceSpec.preference_eq_zero_iff _ _).mp hzero⟩
  · rintro ⟨a, b, hnot, hin⟩
    exact ⟨a, b, (PreferenceSpec.preference_pos_iff _ _).mpr hnot,
      (PreferenceSpec.preference_eq_zero_iff _ _).mpr hin⟩

/-- With a single owner there is never a conflict: `jointReport` always
returns that owner's scores. Multi-owner machinery is conservative over
the single-owner model. -/
theorem jointReport_subsingleton (P : OwnedPreferences Owner V)
    [Subsingleton Owner] (o : Finset V) :
    jointReport P o = Verdict.scores (fun a => (P.spec a).preference o) := by
  classical
  unfold jointReport
  have hc : ¬ ConflictOn P o := by
    rintro ⟨a, b, hpos, hzero⟩
    rw [Subsingleton.elim a b, hzero] at hpos
    exact lt_irrefl 0 hpos
  simp [hc]

end OwnedPreferences

end

end DarkTower.WarMachine.TokenPreferenceOwned

#print axioms DarkTower.WarMachine.TokenPreferenceOwned.OwnedPreferences.jointReport_scores_faithful
#print axioms DarkTower.WarMachine.TokenPreferenceOwned.OwnedPreferences.jointReport_refusal_iff
#print axioms DarkTower.WarMachine.TokenPreferenceOwned.OwnedPreferences.conflictOn_iff_zeroed
#print axioms DarkTower.WarMachine.TokenPreferenceOwned.OwnedPreferences.jointReport_subsingleton
