import DarkTower.WarMachine.CascadeEFEPolicies

/-! Finite arithmetic requirements for G over reading-derived arranged cascades.
This does not assert runtime conformance; `Requirements.lean` states the
countable certificate facts needed for that check. -/

namespace DarkTower.WarMachine.HeadCascadeG

noncomputable section

set_option maxHeartbeats 5000000

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

def placeholderWeight (_total _completed : ℕ) (_wantMet : Bool) : ℝ := 0

/-- F is evidence surprisal, not a constant callback. -/
def fitF (likelihood : ℝ) : ℝ := -Real.log likelihood

theorem accepted_evidence_lowers_F : fitF (9 / 10) < fitF (1 / 2) := by
  simp only [fitF, neg_lt_neg_iff]
  apply Real.log_lt_log
  norm_num
  norm_num

def constantF (_likelihood : ℝ) : ℝ := 0

inductive Node where | a | b | c deriving DecidableEq, Repr, Fintype
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

inductive Token where
  | done (node : Node)
  | edge (source destination : Node)
  | shared (left right : Node)
  deriving DecidableEq, Repr

def doneToken := Token.done
def edgeToken := Token.edge
def sharedToken := Token.shared
def tokenNode? : Token → Option Node | .done n => some n | _ => none

abbrev State := Finset Token
abbrev Distribution := List (State × ℚ)

structure BuiltModel where
  arrangement : ArrangedCascade
  firing : List Node
  requires : Node → Finset Token
  produces : Node → Finset Token

def canonicalFiring : List Node := [.a, .b, .c]

def buildModel (c : ArrangedCascade) (_theta : Node → ℚ) : BuiltModel where
  arrangement := c
  firing := canonicalFiring.filter (fun n => decide (n ∈ c.nodes))
  requires := fun n => c.operators.foldl (fun acc op => match op with
    | .edge source destination => if destination = n then insert (doneToken source) acc else acc
    | .overlap _ _ => acc) ∅
  produces := fun n => insert (doneToken n) <| c.operators.foldl (fun acc op => match op with
    | .edge source destination => if destination = n then insert (edgeToken source destination) acc else acc
    | .overlap left right =>
        if left = n ∨ right = n then insert (sharedToken left right) acc else acc) ∅

def enabled (m : BuiltModel) (n : Node) (s : State) : Bool :=
  decide (m.requires n ⊆ s ∧ ¬ m.produces n ⊆ s)

def findEnabled (m : BuiltModel) (s : State) : List Node → Option Node
  | [] => none
  | n :: ns => if enabled m n s then some n else findEnabled m s ns

def firstEnabled (m : BuiltModel) (s : State) : Option Node := findEnabled m s m.firing

/-- Rational first-enabled union-theta-v1 kernel mirrored from the runner. -/
def transition (m : BuiltModel) (theta : Node → ℚ) (s : State) : Distribution :=
  match firstEnabled m s with
  | none => [(s, 1)]
  | some n =>
      [(s, 1 - theta n), (s ∪ m.produces n, theta n)]

/-- `CascadeEFE.Model.interpretation` is `some` for every pattern by construction.
The rational kernel is kept here because coercing it to the real-valued
`ProbabilityKernel` is a separate normalization-preservation lemma. -/
def interpretation (m : BuiltModel) (theta : Node → ℚ) (n : Node) :
    Option (State → Distribution) := some (fun s =>
      [(s, 1 - theta n), (s ∪ m.produces n, theta n)])

theorem buildModel_interprets_every_node (c : ArrangedCascade) (theta : Node → ℚ)
    (n : Node) : ∃ k, interpretation (buildModel c theta) theta n = some k := ⟨_, rfl⟩

def brokenInterpretation (n : Node) : Option (State → Distribution) :=
  if n = .a then none else some (fun s => [(s, 1)])

/--
error: Tactic `rfl` failed: The left-hand side
  brokenInterpretation Node.a
is not definitionally equal to the right-hand side
  some fun s => [(s, 1)]

⊢ brokenInterpretation Node.a = some fun s => [(s, 1)]
-/
#guard_msgs in
example : brokenInterpretation .a = some (fun s => [(s, 1)]) := by rfl

def addMass : Distribution → State → ℚ → Distribution
  | [], s, p => [(s, p)]
  | row :: rows, s, p =>
      if row.1 = s then (row.1, row.2 + p) :: rows
      else row :: addMass rows s p

def normalizeAux : Distribution → Distribution → Distribution
  | [], acc => acc
  | row :: rows, acc => normalizeAux rows (addMass acc row.1 row.2)

def normalize (rows : Distribution) : Distribution := normalizeAux rows []

def push (m : BuiltModel) (theta : Node → ℚ) (q : Distribution) : Distribution :=
  normalize <| q.flatMap (fun row =>
    (transition m theta row.1).map (fun out => (out.1, row.2 * out.2)))

def initial : Distribution := [(∅, 1)]

def rollout (m : BuiltModel) (theta : Node → ℚ) : ℕ → Distribution
  | 0 => initial
  | t + 1 => push m theta (rollout m theta t)

def halfTheta (_ : Node) : ℚ := 1 / 2

def mass (rows : List (State × ℚ)) : Distribution := rows

def chainFixture : ArrangedCascade :=
  ⟨{.a, .b, .c}, [.edge .a .b, .edge .b .c]⟩
def shortcutFixture : ArrangedCascade :=
  ⟨{.a, .b, .c}, [.edge .a .c]⟩

def chainRows : Fin 4 → List (State × ℚ)
  | 0 => [(∅, 1)]
  | 1 => [(∅, 1/2), ({doneToken .a}, 1/2)]
  | 2 => [(∅, 1/4), ({doneToken .a}, 1/2),
      ({doneToken .a, doneToken .b, edgeToken .a .b}, 1/4)]
  | 3 => [(∅, 1/8), ({doneToken .a}, 3/8),
      ({doneToken .a, doneToken .b, edgeToken .a .b}, 3/8),
      ({doneToken .a, doneToken .b, doneToken .c, edgeToken .a .b, edgeToken .b .c}, 1/8)]

def shortcutRows : Fin 4 → List (State × ℚ)
  | 0 => [(∅, 1)]
  | 1 => [(∅, 1/2), ({doneToken .a}, 1/2)]
  | 2 => [(∅, 1/4), ({doneToken .a}, 1/2), ({doneToken .a, doneToken .b}, 1/4)]
  | 3 => [(∅, 1/8), ({doneToken .a}, 3/8), ({doneToken .a, doneToken .b}, 3/8),
      ({doneToken .a, doneToken .b, doneToken .c, edgeToken .a .c}, 1/8)]

theorem chain_three_step_distribution (t : Fin 4) :
    rollout (buildModel chainFixture halfTheta) halfTheta t = mass (chainRows t) := by
  fin_cases t <;> simp +decide [rollout, initial, push, normalize, addMass, transition,
    firstEnabled, findEnabled, enabled, buildModel, chainFixture, chainRows, halfTheta,
    normalizeAux,
    canonicalFiring, mass, doneToken, edgeToken] <;> norm_num

theorem shortcut_three_step_distribution (t : Fin 4) :
    rollout (buildModel shortcutFixture halfTheta) halfTheta t = mass (shortcutRows t) := by
  fin_cases t <;> simp +decide [rollout, initial, push, normalize, addMass, transition,
    firstEnabled, findEnabled, enabled, buildModel, shortcutFixture, shortcutRows, halfTheta,
    normalizeAux, canonicalFiring, mass, doneToken, edgeToken] <;> norm_num

theorem fixture_distributions_differ_at_two :
    rollout (buildModel chainFixture halfTheta) halfTheta 2 ≠
      rollout (buildModel shortcutFixture halfTheta) halfTheta 2 := by
  rw [chain_three_step_distribution ⟨2, by decide⟩,
    shortcut_three_step_distribution ⟨2, by decide⟩]
  simp +decide [mass, chainRows, shortcutRows, doneToken, edgeToken]

def doneProjection (s : State) : Finset Node :=
  ({.a, .b, .c} : Finset Node).filter (fun n => doneToken n ∈ s)

theorem doneProjection_insert_edge (s : State) (a b : Node) :
    doneProjection (insert (edgeToken a b) s) = doneProjection s := by
  ext n
  simp +decide [doneProjection, doneToken, edgeToken]

def projected (q : Distribution) (nodes : Finset Node) : ℚ :=
  (q.filter (fun row => doneProjection row.1 = nodes)).map (fun row => row.2) |>.sum

def projectRows (q : Distribution) : List (Finset Node × ℚ) :=
  q.map (fun row => (doneProjection row.1, row.2))

/-- Warning: on these fixtures, deleting structural progress tokens deletes
all shape signal for the entire three-step horizon. -/
theorem projection_erases_fixture_shape (t : Fin 4) :
    projectRows (rollout (buildModel chainFixture halfTheta) halfTheta t) =
      projectRows (rollout (buildModel shortcutFixture halfTheta) halfTheta t) := by
  rw [chain_three_step_distribution t, shortcut_three_step_distribution t]
  fin_cases t <;> simp +decide [projectRows, chainRows, shortcutRows, mass,
    doneProjection, doneToken, edgeToken]

/-- The eight forward-edge subsets compatible with `[a,b,c]`. -/
structure ForwardEdges where
  ab : Bool
  ac : Bool
  bc : Bool
  deriving DecidableEq, Fintype

def forwardArrangement (e : ForwardEdges) : ArrangedCascade :=
  ⟨{.a, .b, .c},
   (if e.ab then [.edge .a .b] else []) ++
   (if e.ac then [.edge .a .c] else []) ++
   (if e.bc then [.edge .b .c] else [])⟩

/-- No valid forward-edge arrangement with this firing order changes the
node-token distribution in three rounds; only structural tokens separate it. -/
theorem no_enabling_only_separation_three_nodes (e₁ e₂ : ForwardEdges)
    (t : Fin 4) :
    projectRows (rollout (buildModel (forwardArrangement e₁) halfTheta) halfTheta t) =
      projectRows (rollout (buildModel (forwardArrangement e₂) halfTheta) halfTheta t) := by
  rcases e₁ with ⟨ab₁, ac₁, bc₁⟩
  rcases e₂ with ⟨ab₂, ac₂, bc₂⟩
  cases ab₁ <;> cases ac₁ <;> cases bc₁ <;>
    cases ab₂ <;> cases ac₂ <;> cases bc₂ <;> fin_cases t <;>
    simp +decide [projectRows, rollout, initial, push, normalize, normalizeAux, addMass,
      transition, firstEnabled, findEnabled, enabled, buildModel, forwardArrangement,
      halfTheta, canonicalFiring, doneProjection, doneToken, edgeToken]

theorem fixture_same_firing_nodes : chainFixture.nodes = shortcutFixture.nodes := rfl

/-- What Q10 requires of the scorer. It cannot be discharged from a recorded
decimal pair: the transition and observation semantics must imply it. -/
def ShapeSensitive (score : ArrangedCascade → ℝ) : Prop :=
  score chainFixture ≠ score shortcutFixture


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
#print axioms accepted_evidence_lowers_F
#print axioms buildModel_interprets_every_node
#print axioms chain_three_step_distribution
#print axioms shortcut_three_step_distribution
#print axioms fixture_distributions_differ_at_two
#print axioms projection_erases_fixture_shape
#print axioms no_enabling_only_separation_three_nodes

end

end DarkTower.WarMachine.HeadCascadeG
