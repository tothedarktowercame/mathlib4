import DarkTower.WarMachine.PolicyRollout

/-!
# Matched observation evidence: the F comparison semantics

The F term consumes evidence only when an observation is MATCHED to the
prediction for its own step. Until now this had no Lean statement (a queued
transcription item of futon2 `SPEC-a-model-conformance-2026-09-20.md`), and
the runtime's `:zero-consumed-f` history shows what grows in that silence:
an absent comparison reading as the number 0.

This module fixes the semantics as a three-valued result:

- a step with NO received observation yields `missing` — never the number 0
  (the type has no coercion from `missing` to a value; an adapter that
  wants a number must confront the constructor);
- a RECEIVED observation with predictive probability 0 is a typed
  `contradiction` — the model said impossible and the world produced it —
  distinct from missing (this is `exactUpdate_eq_none_iff`'s refusal
  boundary, at the evidence layer);
- otherwise the evidence value is the surprisal `−log Q(o|π,n)` against
  `PolicyRollout.predictedOutcome`, and it is provably nonnegative from the
  model laws alone.

Both-sides discipline: the `_iff` lemmas characterise each constructor
exactly, so an implementation can be probed into every branch.
-/

namespace DarkTower.WarMachine.MatchedObservationEvidence

open DarkTower.WarMachine.PolicyRollout

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-- The three-valued outcome of matching a step's observation to its
prediction. There is deliberately no `zero` and no default. -/
inductive MatchedEvidence (O : Type*)
  | missing
  | contradiction (o : O)
  | value (f : ℝ)

noncomputable section

open Classical in
/-- Match an optional received observation at step `n` to the policy's
predicted outcome distribution for step `n`. -/
noncomputable def matchedEvidence (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) :
    Option O → MatchedEvidence O
  | none => .missing
  | some o =>
      if predictedOutcome M π n o = 0 then .contradiction o
      else .value (-Real.log (predictedOutcome M π n o))

@[simp] theorem matchedEvidence_none (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ) :
    matchedEvidence M π n none = MatchedEvidence.missing := rfl

/-- A missing observation never yields a value — in particular never `0`. -/
theorem matchedEvidence_none_ne_value (M : ForwardModel S O U) (π : ℕ → U)
    (n : ℕ) (f : ℝ) : matchedEvidence M π n none ≠ MatchedEvidence.value f :=
  fun h => by simp at h

/-- Contradiction exactly when the model gave the received observation
predictive probability zero. -/
theorem matchedEvidence_contradiction_iff (M : ForwardModel S O U) (π : ℕ → U)
    (n : ℕ) (o o' : O) :
    matchedEvidence M π n (some o) = MatchedEvidence.contradiction o'
      ↔ predictedOutcome M π n o = 0 ∧ o' = o := by
  simp only [matchedEvidence]
  split_ifs with hz
  · constructor
    · intro h
      cases h
      exact ⟨hz, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl
  · constructor
    · intro h; simp at h
    · rintro ⟨h0, _⟩; exact absurd h0 hz

/-- A value exactly when the received observation was predictively possible,
and then it is the surprisal. -/
theorem matchedEvidence_value_iff (M : ForwardModel S O U) (π : ℕ → U)
    (n : ℕ) (o : O) (f : ℝ) :
    matchedEvidence M π n (some o) = MatchedEvidence.value f
      ↔ predictedOutcome M π n o ≠ 0
        ∧ f = -Real.log (predictedOutcome M π n o) := by
  simp only [matchedEvidence]
  split_ifs with hz
  · constructor
    · intro h; simp at h
    · rintro ⟨hne, _⟩; exact absurd hz hne
  · constructor
    · intro h
      cases h
      exact ⟨hz, rfl⟩
    · rintro ⟨_, rfl⟩
      rfl

/-- Predicted outcomes never exceed 1: one term of a unit sum. -/
theorem predictedOutcome_le_one (M : ForwardModel S O U) (π : ℕ → U) (n : ℕ)
    (o : O) : predictedOutcome M π n o ≤ 1 := by
  have h := predictedOutcome_sum M π n
  calc predictedOutcome M π n o
      ≤ ∑ o', predictedOutcome M π n o' :=
        Finset.single_le_sum (fun o' _ => predictedOutcome_nonneg M π n o')
          (Finset.mem_univ o)
    _ = 1 := h

/-- **Matched evidence is nonnegative** from the model laws alone: surprisal
of a probability in `(0, 1]`. -/
theorem matchedEvidence_value_nonneg (M : ForwardModel S O U) (π : ℕ → U)
    (n : ℕ) (o : O) (f : ℝ)
    (h : matchedEvidence M π n (some o) = MatchedEvidence.value f) : 0 ≤ f := by
  obtain ⟨hne, rfl⟩ := (matchedEvidence_value_iff M π n o f).mp h
  have hpos : 0 < predictedOutcome M π n o :=
    lt_of_le_of_ne (predictedOutcome_nonneg M π n o) (Ne.symm hne)
  have hle : Real.log (predictedOutcome M π n o) ≤ 0 :=
    Real.log_nonpos (le_of_lt hpos) (predictedOutcome_le_one M π n o)
  linarith

end

end DarkTower.WarMachine.MatchedObservationEvidence

#print axioms DarkTower.WarMachine.MatchedObservationEvidence.matchedEvidence_contradiction_iff
#print axioms DarkTower.WarMachine.MatchedObservationEvidence.matchedEvidence_value_iff
#print axioms DarkTower.WarMachine.MatchedObservationEvidence.matchedEvidence_value_nonneg
