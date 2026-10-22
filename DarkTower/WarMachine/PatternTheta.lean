import DarkTower.WarMachine.Proof2.ObservedInterpretation
import DarkTower.WarMachine.R15TemporalHierarchy

/-!
# Pattern transition probability from a published reading and witnessed fires

Sources: futon2/holes/labs/wm-contract/refs/friston2017.txt:352, `Q(B) = Dir(b)`;
refs/dacosta2020.txt, Appendix A.1 "Learning B and D" (transition Dirichlet
counts), and equation (21) (additive learning of observation counts). Equation
(21) itself concerns A; Appendix A.1 supplies the analogous transition update.
A binary success/failure transition specializes the Dirichlet to Beta; here θ
is its posterior mean, not its expected log probability.

The prior pseudo-counts are supplied by the published interpretation reading,
as in Proof2.ObservedInterpretation (Joe's D3). Attestation is opaque text, not
a proof of publication or of the prior's truth. Both positive pseudo-counts are
an explicit modeling condition. The caller identifies the pattern and attests
that the guard held when each fire occurred; this module does not infer that.

`thetaOf` takes the already-witnessed Bool outcomes of one pattern. For raw R15
records, `witnessedOutcomes` explicitly filters both witness flag and pattern
key; `advanceWitnessed` uses the same filter before calling R15TemporalHierarchy.advance. R15's
arithmetic advance alone does NOT enforce witness admission. The agreement
below concerns precisely the admitted list. No outcome is invented for an
unobserved fire. `interpretWithTheta` builds a pattern; it does not replace any
existing example or certify a runtime reading.
-/

namespace DarkTower.WarMachine.PatternTheta


/-- Positive success/failure pseudo-counts received in an attested reading. -/
structure ThetaReading where
  priorS : ℕ
  priorF : ℕ
  success_positive : 1 ≤ priorS
  failure_positive : 1 ≤ priorF
  readingAttestation : String
  deriving Repr

def successes : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) + successes bs

def failures : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 0 else 1) + failures bs

theorem counts_length (xs : List Bool) : successes xs + failures xs = xs.length := by
  induction xs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp_all [successes, failures] <;> omega

theorem successes_append (xs ys : List Bool) :
    successes (xs ++ ys) = successes xs + successes ys := by
  induction xs with
  | nil => simp [successes]
  | cons b bs ih => simp [successes, ih, Nat.add_assoc]

theorem failures_append (xs ys : List Bool) :
    failures (xs ++ ys) = failures xs + failures ys := by
  induction xs with
  | nil => simp [failures]
  | cons b bs ih => simp [failures, ih, Nat.add_assoc]

/-- Posterior mean; outcomes are admitted, witnessed fires of this pattern. -/
def thetaOf (r : ThetaReading) (xs : List Bool) : ℚ :=
  (r.priorS + successes xs : ℚ) /
    ((r.priorS + successes xs : ℚ) + (r.priorF + failures xs : ℚ))

theorem theta_closed_form (r : ThetaReading) (xs : List Bool)
    (n k : ℕ) (hn : xs.length = n) (hk : successes xs = k) :
    thetaOf r xs = (r.priorS + k : ℚ) / (r.priorS + r.priorF + n : ℚ) := by
  have hc : (successes xs : ℚ) + failures xs = n := by
    exact_mod_cast (counts_length xs).trans hn
  unfold thetaOf
  rw [← hk]
  congr 1
  linarith

private theorem positive_counts (r : ThetaReading) (xs : List Bool) :
    0 < (r.priorS + successes xs : ℚ) ∧ 0 < (r.priorF + failures xs : ℚ) := by
  have hs : (1 : ℚ) ≤ r.priorS := by exact_mod_cast r.success_positive
  have hf : (1 : ℚ) ≤ r.priorF := by exact_mod_cast r.failure_positive
  constructor <;> positivity

theorem theta_pos (r : ThetaReading) (xs : List Bool) : 0 < thetaOf r xs := by
  obtain ⟨hs, hf⟩ := positive_counts r xs
  exact div_pos hs (add_pos hs hf)

theorem theta_lt_one (r : ThetaReading) (xs : List Bool) : thetaOf r xs < 1 := by
  obtain ⟨hs, hf⟩ := positive_counts r xs
  apply (div_lt_one (add_pos hs hf)).2
  linarith

theorem success_raises (r : ThetaReading) (xs : List Bool) :
    thetaOf r xs < thetaOf r (xs ++ [true]) := by
  obtain ⟨hs, hf⟩ := positive_counts r xs
  simp [thetaOf, successes_append, failures_append, successes, failures]
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

theorem failure_lowers (r : ThetaReading) (xs : List Bool) :
    thetaOf r (xs ++ [false]) < thetaOf r xs := by
  obtain ⟨hs, hf⟩ := positive_counts r xs
  simp [thetaOf, successes_append, failures_append, successes, failures]
  apply (div_lt_div_iff₀ (by linarith) (by linarith)).2
  nlinarith

theorem theta_nil (r : ThetaReading) :
    thetaOf r [] = (r.priorS : ℚ) / (r.priorS + r.priorF : ℚ) := by
  simp [thetaOf, successes, failures]

variable {Key : Type} [DecidableEq Key]

/-- Raw events are admitted only for this pattern and only when witnessed. -/
def witnessedOutcomes (key : Key) (events : List (R15TemporalHierarchy.FastOutcome Key)) : List Bool :=
  (events.filter (fun e => e.witnessed && decide (e.policy = key))).map (·.succeeded)

theorem unwitnessed_not_counted (key : Key) (e : R15TemporalHierarchy.FastOutcome Key)
    (events : List (R15TemporalHierarchy.FastOutcome Key)) (h : e.witnessed = false) :
    witnessedOutcomes key (e :: events) = witnessedOutcomes key events := by
  simp [witnessedOutcomes, h]

/-- Fold the admitted outcomes with the existing R15 update, marking each witnessed. -/
def foldFires (key : Key) (state : R15TemporalHierarchy.SlowState Key) (xs : List Bool) :
    R15TemporalHierarchy.SlowState Key :=
  xs.foldl (fun s b => R15TemporalHierarchy.advance s ⟨key, true, b⟩) state

def advanceWitnessed (key : Key) (state : R15TemporalHierarchy.SlowState Key)
    (events : List (R15TemporalHierarchy.FastOutcome Key)) : R15TemporalHierarchy.SlowState Key :=
  foldFires key state (witnessedOutcomes key events)

theorem advanceWitnessed_unwitnessed (key : Key) (state : R15TemporalHierarchy.SlowState Key)
    (e : R15TemporalHierarchy.FastOutcome Key) (events : List (R15TemporalHierarchy.FastOutcome Key))
    (h : e.witnessed = false) :
    advanceWitnessed key state (e :: events) = advanceWitnessed key state events := by
  simp [advanceWitnessed, unwitnessed_not_counted key e events h]

theorem foldFires_counts (key : Key) (state : R15TemporalHierarchy.SlowState Key) (xs : List Bool) :
    R15TemporalHierarchy.countsFor (foldFires key state xs) key =
      ⟨(R15TemporalHierarchy.countsFor state key).alpha + successes xs,
       (R15TemporalHierarchy.countsFor state key).beta + failures xs⟩ := by
  induction xs generalizing state with
  | nil => simp [foldFires, successes, failures]
  | cons b bs ih =>
    change R15TemporalHierarchy.countsFor (foldFires key (R15TemporalHierarchy.advance state ⟨key, true, b⟩) bs) key = _
    rw [ih]
    cases b <;>
      simp [R15TemporalHierarchy.advance, R15TemporalHierarchy.countsFor_setCounts_same, R15TemporalHierarchy.updatedCounts,
        successes, failures, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm]

/-- Agreement with R15's actual keyed advance, starting at the reading counts. -/
theorem r15_agreement (key : Key) (r : ThetaReading) (xs : List Bool) :
    let c := R15TemporalHierarchy.countsFor (foldFires key [(key, ⟨r.priorS, r.priorF⟩)] xs) key
    (c.alpha : ℚ) / (c.alpha + c.beta : ℚ) = thetaOf r xs := by
  simp [foldFires_counts, R15TemporalHierarchy.countsFor, thetaOf, Nat.cast_add]

/-- No arbitrary θ parameter: θ is the posterior mean of the received reading. -/
def interpretWithTheta {V : Type*} [Fintype V] [DecidableEq V]
    (consumes produces forbids : Finset V) (r : ThetaReading) (xs : List Bool) :
    CascadeTransition.InterpretedPattern V where
  consumes := consumes
  produces := produces
  forbids := forbids
  theta := (thetaOf r xs : ℝ)
  theta_nonneg := le_of_lt (by exact_mod_cast theta_pos r xs)
  theta_le_one := le_of_lt (by exact_mod_cast theta_lt_one r xs)

/-- Zero prior failures cannot inhabit the required reading type. -/
theorem no_zero_prior_failures (r : ThetaReading) : r.priorF ≠ 0 := by
  have := r.failure_positive
  omega

/-- Concrete prior, supplied here solely for negative controls. -/
def controlReading : ThetaReading := ⟨1, 1, by decide, by decide, "control reading"⟩

/-- The empirical fraction ignoring the reading prior is not this posterior. -/
def priorFreeTheta (xs : List Bool) : ℚ := (successes xs : ℚ) / (xs.length : ℚ)

theorem prior_free_empty_disagrees : priorFreeTheta [] ≠ thetaOf controlReading [] := by
  norm_num [priorFreeTheta, thetaOf, controlReading, successes, failures]

theorem prior_free_one_success_disagrees :
    priorFreeTheta [true] ≠ thetaOf controlReading [true] := by
  norm_num [priorFreeTheta, thetaOf, controlReading, successes, failures]

#print axioms theta_closed_form
#print axioms theta_pos
#print axioms theta_lt_one
#print axioms success_raises
#print axioms failure_lowers
#print axioms theta_nil
#print axioms r15_agreement
#print axioms unwitnessed_not_counted
#print axioms advanceWitnessed_unwitnessed
#print axioms no_zero_prior_failures
#print axioms prior_free_empty_disagrees
#print axioms prior_free_one_success_disagrees
#print axioms interpretWithTheta

end DarkTower.WarMachine.PatternTheta
