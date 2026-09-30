import DarkTower.WarMachine.CascadeEFEPolicies

/-! Finite arithmetic requirements for G over reading-derived arranged cascades.
This does not assert runtime conformance; `Requirements.lean` states the
countable certificate facts needed for that check. -/

namespace DarkTower.WarMachine.HeadCascadeG

noncomputable section

structure Terms where
  risk : ℝ
  ambiguity : ℝ
  expectedInformationGain : ℝ

def G (x : Terms) : ℝ := x.risk + x.ambiguity - x.expectedInformationGain

/-- The selector uses `σ(log E - F - γG)`; this is its pre-softmax logit. -/
def selectionLogit (logHabit freeEnergy precision : ℝ) (x : Terms) : ℝ :=
  logHabit - freeEnergy - precision * G x

theorem information_nonnegative_is_required (x : Terms)
    (h : 0 ≤ x.expectedInformationGain) : G x ≤ x.risk + x.ambiguity := by
  simp [G]; linarith

theorem more_information_strictly_lowers_G (a b : Terms)
    (hr : a.risk = b.risk) (ha : a.ambiguity = b.ambiguity)
    (hi : b.expectedInformationGain < a.expectedInformationGain) : G a < G b := by
  simp [G]; linarith

theorem lower_G_strictly_raises_logit (a b : Terms) (logHabit freeEnergy precision : ℝ)
    (hp : 0 < precision) (hG : G a < G b) :
    selectionLogit logHabit freeEnergy precision b <
      selectionLogit logHabit freeEnergy precision a := by
  simp [selectionLogit]; nlinarith

def droppedInformationG (x : Terms) : ℝ := x.risk + x.ambiguity

/-- S5b's C-tau log weight. Normalizing exp of these weights preserves order. -/
def progressWeight (total completed : ℕ) (wantMet : Bool) : ℝ :=
  4 * (completed : ℝ) / total + if wantMet then 2 else 0

theorem progress_strict (total a b : ℕ) (ht : 0 < total) (hab : a < b) (w : Bool) :
    progressWeight total a w < progressWeight total b w := by
  have ht' : (0 : ℝ) < total := by exact_mod_cast ht
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  simp only [progressWeight]
  split <;> field_simp <;> nlinarith

theorem want_met_strict (total completed : ℕ) :
    progressWeight total completed false < progressWeight total completed true := by
  simp [progressWeight]

def countEmission (completed : Finset ℕ) : ℕ := completed.card

theorem countEmission_preserves_strict {a b : Finset ℕ} (hsub : a ⊂ b) :
    countEmission a < countEmission b := Finset.card_lt_card hsub

/-- Per-step normalized missing-progress risk. -/
def progressRisk (total completed : ℕ) : ℝ :=
  ((total : ℝ) - completed) / total

theorem earlier_progress_lower_step_risk (total a b : ℕ) (hab : a ≤ b) :
    progressRisk total b ≤ progressRisk total a := by
  unfold progressRisk
  gcongr

theorem earlier_progress_strictly_lower_step_risk (total a b : ℕ)
    (ht : 0 < total) (hab : a < b) : progressRisk total b < progressRisk total a := by
  unfold progressRisk
  have ht' : (0 : ℝ) < total := by exact_mod_cast ht
  have hab' : (a : ℝ) < b := by exact_mod_cast hab
  apply (div_lt_div_iff_of_pos_right ht').2
  linarith

def cumulativeProgressRisk {T : ℕ} (total : ℕ) (progress : Fin T → ℕ) : ℝ :=
  ∑ t, progressRisk total (progress t)

theorem pointwise_earlier_no_greater_cumulative_risk {T total : ℕ}
    (later earlier : Fin T → ℕ) (h : ∀ t, later t ≤ earlier t) :
    cumulativeProgressRisk total earlier ≤ cumulativeProgressRisk total later := by
  apply Finset.sum_le_sum
  intro t _
  exact earlier_progress_lower_step_risk total _ _ (h t)

theorem one_step_earlier_strictly_lowers_cumulative_risk {T total : ℕ}
    (later earlier : Fin T → ℕ) (ht : 0 < total)
    (hle : ∀ t, later t ≤ earlier t) (hlt : ∃ t, later t < earlier t) :
    cumulativeProgressRisk total earlier < cumulativeProgressRisk total later := by
  apply Finset.sum_lt_sum
  · intro t _
    exact earlier_progress_lower_step_risk total _ _ (hle t)
  · obtain ⟨t, h⟩ := hlt
    exact ⟨t, Finset.mem_univ _, earlier_progress_strictly_lower_step_risk total _ _ ht h⟩

def placeholderWeight (_total _completed : ℕ) (_wantMet : Bool) : ℝ := 0

/-- F is evidence surprisal, not a constant callback. -/
def fitF (likelihood : ℝ) : ℝ := -Real.log likelihood

theorem accepted_evidence_lowers_F : fitF (9 / 10) < fitF (1 / 2) := by
  simp only [fitF, neg_lt_neg_iff]
  apply Real.log_lt_log
  norm_num
  norm_num

theorem fit_total (likelihood : ℝ) : ∃ f : ℝ, fitF likelihood = f := ⟨_, rfl⟩

def constantF (_likelihood : ℝ) : ℝ := 0

inductive Node where | a | b | c deriving DecidableEq, Repr
inductive Operator where
  /-- Destination requires the source's completion token. -/
  | edge (source destination : Node)
  /-- Both endpoints advance using one shared token. -/
  | overlap (left right : Node)
  deriving DecidableEq, Repr

structure ArrangedCascade where
  nodes : Finset Node
  operators : List Operator
  deriving DecidableEq

def chainFixture : ArrangedCascade :=
  ⟨{.a, .b, .c}, [.edge .a .b, .edge .b .c]⟩
def shortcutFixture : ArrangedCascade :=
  ⟨{.a, .b, .c}, [.edge .a .c]⟩

theorem fixture_same_firing_nodes : chainFixture.nodes = shortcutFixture.nodes := rfl

/-- What Q10 requires of the scorer. It cannot be discharged from a recorded
decimal pair: the transition and observation semantics must imply it. -/
def ShapeSensitive (score : ArrangedCascade → ℝ) : Prop :=
  score chainFixture ≠ score shortcutFixture

/-- The exact pair attested by the Clojure fixture, retained as evidence to be
checked, not converted into a theorem about an invented Lean scorer. -/
def codeFixtureScores : ℚ × ℚ := (3074890 / 1000000, 1414694 / 1000000)

theorem recorded_fixture_scores_differ : codeFixtureScores.1 ≠ codeFixtureScores.2 := by
  norm_num [codeFixtureScores]

/-- A conforming model supplies total G and F functions on every constructible
arrangement. There is no `Option` in either domain. -/
structure TotalScorer where
  g : ArrangedCascade → ℝ
  f : ArrangedCascade → ℝ

theorem arranged_total (s : TotalScorer) (c : ArrangedCascade) :
    ∃ g f : ℝ, s.g c = g ∧ s.f c = f := ⟨_, _, rfl, rfl⟩

/-- S5b units: risk per horizon/log-support, ambiguity per horizon, and
information per distinct pattern. -/
def normalizedG (risk ambiguity information nodeCount : ℚ) : ℚ :=
  risk / nodeCount + ambiguity - information / nodeCount

theorem same_normalized_terms_same_G {r₁ r₂ a₁ a₂ i₁ i₂ n₁ n₂ : ℚ}
    (hr : r₁ / n₁ = r₂ / n₂) (ha : a₁ = a₂)
    (hi : i₁ / n₁ = i₂ / n₂) :
    normalizedG r₁ a₁ i₁ n₁ = normalizedG r₂ a₂ i₂ n₂ := by
  simp [normalizedG, hr, ha, hi]

/-- The requested unconditional size invariance is false: per-horizon
interaction ambiguity can rise even when per-node risk and information match. -/
theorem more_nodes_can_raise_normalized_G :
    normalizedG 1 1 1 1 < normalizedG 2 2 2 2 := by norm_num [normalizedG]

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : droppedInformationG ⟨1, 1, 2⟩ < droppedInformationG ⟨1, 1, 1⟩ := by
  norm_num [droppedInformationG]

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : placeholderWeight 4 0 false < placeholderWeight 4 1 false := by
  norm_num [placeholderWeight]

/--
error: unsolved goals
⊢ False
-/
#guard_msgs in
example : constantF (9/10) < constantF (1/2) := by norm_num [constantF]

/-- error: unsolved goals
⊢ False -/
#guard_msgs in
example : ShapeSensitive (fun _ => 0) := by simp [ShapeSensitive]

#print axioms more_information_strictly_lowers_G
#print axioms progress_strict
#print axioms want_met_strict
#print axioms countEmission_preserves_strict
#print axioms earlier_progress_lower_step_risk
#print axioms earlier_progress_strictly_lower_step_risk
#print axioms pointwise_earlier_no_greater_cumulative_risk
#print axioms one_step_earlier_strictly_lowers_cumulative_risk
#print axioms accepted_evidence_lowers_F
#print axioms fit_total
#print axioms recorded_fixture_scores_differ
#print axioms arranged_total
#print axioms more_nodes_can_raise_normalized_G

end

end DarkTower.WarMachine.HeadCascadeG
