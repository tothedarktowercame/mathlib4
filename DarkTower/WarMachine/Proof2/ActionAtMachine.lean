import DarkTower.WarMachine.ActionMarginal
import DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

/-!
# The Bayes action at the machine's own policy posterior (W2, registry `:action`)

`ActionMarginal.IsBayesAction` states Da Costa et al. 2020 eq. (11),
`u_t = argmax_u ∑_π δ(u, π_t) Q(π)`, over an ABSTRACT posterior `Q`.
`PolicyPosteriorAtMachine.machinePosterior` (W1/W1b) is the machine's own `Q`.
Nothing applied the one to the other, so the registry edge R6→R16 (`Q-pi`, the
policy posterior into the action) had the term in the consumer's signature and no
import behind it. This module is that application.

The file name is `ActionAtMachine`, not `MachineAction`: the production selector
`DarkTower.WarMachine.MachineAction.machineAction` (`SelectionBoundary → StrategicLaw
→ … → Option Candidate`, the registry row's `:lean-at`) is a different declaration
and is unchanged. The two are not the same object and this module does not claim
they agree (the row's `:lean-note` states where the production selector differs
from eq. 11).

## The chosen maximiser and the code it follows

`IsBayesAction` allows ties ("any maximiser satisfies eq. (11)"). The machine does
not: `futon2 src/futon2/aif/cascade_selection.clj`, `bayes-choice`
(lines 131-159 at futon2 `5974218d`; the function's last change is `c4aa4f98`)
sums the posterior over the policies taking each action, orders the actions by
`(comp str key)` — ASCENDING ACTION NAME — and folds keeping the current best
unless the next mass is STRICTLY greater (`(if (> m' best-m) [a' m'] best)`). So
among equal masses the FIRST in ascending order wins, and the result carries
`:tie-break-rule :action-name-ascending` (`bayes-choice-tie-rule`, line 128-129).
`chooseAction` is that fold, over an abstract `LinearOrder Action` standing for the
ascending-name order (an order on `Action` is a parameter; this module does not
say the production order on strings is a linear order of `Action`, only that the
tie rule is "least in the given order").

Two differences from the code are real and stated:

* the code accumulates masses in floating point; here they are reals;
* the code's candidate actions are the actions some policy takes (it builds
  `masses` from the posterior); so is `chooseAction`'s list. An action no policy
  takes has mass 0, and `machineAction_isBayesAction` shows the chosen action is
  still a maximiser over ALL of `Action`, because the masses are nonnegative.

No default action is ever supplied: an absent posterior gives an absent action
(`machineAction_absent`), and an empty candidate list gives
`Absence.allFreeEnergiesInfinite`, which is literally true of the empty policy list
(no policy has a finite F). That arm is unreachable on an ok posterior
(`machineAction_ok_nonempty`).
-/

namespace DarkTower.WarMachine.Proof2.ActionAtMachine

open DarkTower.WarMachine
open DarkTower.WarMachine.Proof2.PolicyPosteriorAtMachine

noncomputable section

variable {PolicyIndex Action : Type*}

/-! ## The mass -/

/-- **Bayesian-model-average mass** `∑_π δ(u, π_t) Q(π)`, over the zip of the
machine's weights with the policies: the total weight of the policies whose current
action `head π` is `u`. -/
def machineActionMass [DecidableEq Action] (weights : List ℝ)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action) : ℝ :=
  (((weights.zip policies).filter fun p => decide (head p.2 = u)).map Prod.fst).sum

/-! ## The chosen maximiser -/

/-- The fold of `bayes-choice`: keep the current best unless the next mass is
STRICTLY greater. -/
def pickFirstMax (m : Action → ℝ) : Action → List Action → Action
  | a, [] => a
  | a, x :: xs => pickFirstMax m (if m a < m x then x else a) xs

/-- The choice: sort the candidate actions ascending, then `pickFirstMax`. `none`
only when there is no candidate. -/
def chooseAction [LinearOrder Action] (m : Action → ℝ) (heads : List Action) :
    Option Action :=
  match heads.insertionSort (· ≤ ·) with
  | [] => none
  | a :: xs => some (pickFirstMax m a xs)

/-- **The action at the machine's posterior.** The machine's `Q` through
`machinePosterior`'s `Except`, then `chooseAction` on the mass. No default: an
absent posterior is an absent action. -/
def machineAction [LinearOrder Action] (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) :
    Except (Absence PolicyIndex) Action :=
  match machinePosterior habit grade F opts policies with
  | .error a => .error a
  | .ok ws =>
    match chooseAction (machineActionMass ws policies head) (policies.map head) with
    | some u => .ok u
    | none => .error .allFreeEnergiesInfinite

/-! ## The fold picks the first maximiser -/

theorem pickFirstMax_spec [LinearOrder Action] (m : Action → ℝ) :
    ∀ (xs : List Action) (a : Action), (a :: xs).Pairwise (· ≤ ·) →
      pickFirstMax m a xs ∈ a :: xs ∧
      (∀ y ∈ a :: xs, m y ≤ m (pickFirstMax m a xs)) ∧
      (∀ y ∈ a :: xs, m y = m (pickFirstMax m a xs) → pickFirstMax m a xs ≤ y) := by
  intro xs
  induction xs with
  | nil =>
    intro a _
    refine ⟨by simp [pickFirstMax], ?_, ?_⟩
    · intro y hy
      simp at hy
      subst hy
      simp [pickFirstMax]
    · intro y hy _
      simp at hy
      subst hy
      simp [pickFirstMax]
  | cons x xs ih =>
    intro a hp
    rw [List.pairwise_cons] at hp
    obtain ⟨hax, hxs⟩ := hp
    have hax' : a ≤ x := hax x (by simp)
    by_cases hlt : m a < m x
    · have hp' : (x :: xs).Pairwise (· ≤ ·) := hxs
      obtain ⟨hmem, hmax, hleast⟩ := ih x hp'
      have hb : pickFirstMax m a (x :: xs) = pickFirstMax m x xs := by
        simp [pickFirstMax, hlt]
      rw [hb]
      have hxb : m x ≤ m (pickFirstMax m x xs) := hmax x (by simp)
      refine ⟨by simp only [List.mem_cons] at hmem ⊢; tauto, ?_, ?_⟩
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact le_trans hlt.le hxb
        · exact hmax y hy
      · intro y hy heq
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd heq (ne_of_lt (lt_of_lt_of_le hlt hxb))
        · exact hleast y hy heq
    · have hle : m x ≤ m a := not_lt.mp hlt
      have hp' : (a :: xs).Pairwise (· ≤ ·) := by
        rw [List.pairwise_cons]
        exact ⟨fun b hb => hax b (List.mem_cons_of_mem _ hb), (List.pairwise_cons.mp hxs).2⟩
      obtain ⟨hmem, hmax, hleast⟩ := ih a hp'
      have hb : pickFirstMax m a (x :: xs) = pickFirstMax m a xs := by
        simp [pickFirstMax, hlt]
      rw [hb]
      have hab : m a ≤ m (pickFirstMax m a xs) := hmax a (by simp)
      refine ⟨?_, ?_, ?_⟩
      · simp only [List.mem_cons] at hmem ⊢; tauto
      · intro y hy
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hab
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact le_trans hle hab
          · exact hmax y (List.mem_cons_of_mem _ hy)
      · intro y hy heq
        rcases List.mem_cons.mp hy with rfl | hy
        · exact hleast y (by simp) heq
        · rcases List.mem_cons.mp hy with rfl | hy
          · have hay : m a = m (pickFirstMax m a xs) :=
              le_antisymm hab (heq ▸ hle)
            exact le_trans (hleast a (by simp) hay) hax'
          · exact hleast y (List.mem_cons_of_mem _ hy) heq

/-- The chosen action is a candidate, a maximiser over the candidates, and the
LEAST maximiser in the order. -/
theorem chooseAction_spec [LinearOrder Action] (m : Action → ℝ) (heads : List Action)
    (u : Action) (h : chooseAction m heads = some u) :
    u ∈ heads ∧ (∀ y ∈ heads, m y ≤ m u) ∧
      (∀ y ∈ heads, m y = m u → u ≤ y) := by
  unfold chooseAction at h
  have hsorted := List.pairwise_insertionSort (· ≤ ·) heads
  have hmemiff : ∀ y, y ∈ heads.insertionSort (· ≤ ·) ↔ y ∈ heads := fun y => List.mem_insertionSort (· ≤ ·)
  cases hs : heads.insertionSort (· ≤ ·) with
  | nil => simp [hs] at h
  | cons a xs =>
    rw [hs] at h hsorted hmemiff
    simp only [Option.some.injEq] at h
    subst h
    obtain ⟨h1, h2, h3⟩ := pickFirstMax_spec m xs a hsorted
    exact ⟨(hmemiff _).mp h1, fun y hy => h2 y ((hmemiff y).mpr hy),
      fun y hy => h3 y ((hmemiff y).mpr hy)⟩

theorem chooseAction_isSome [LinearOrder Action] (m : Action → ℝ) (heads : List Action)
    (hne : heads ≠ []) : ∃ u, chooseAction m heads = some u := by
  unfold chooseAction
  cases hs : heads.insertionSort (· ≤ ·) with
  | nil =>
    exfalso
    apply hne
    have : ∀ y, y ∉ heads := fun y hy => by
      have := (List.mem_insertionSort (· ≤ ·) (l := heads) (x := y)).mpr hy
      simp [hs] at this
    exact List.eq_nil_iff_forall_not_mem.mpr this
  | cons a xs => exact ⟨_, rfl⟩

/-! ## Bridging the list mass to `ActionMarginal.actionMarginal` -/

section Bridge

variable [LinearOrder Action]

/-- The policies as `Fin n`, with the machine's weights as `Q`. -/
def stepAt (policies : List PolicyIndex) (head : PolicyIndex → Action) :
    Fin policies.length → Action := fun i => head (policies.get i)

def qAt (weights : List ℝ) (policies : List PolicyIndex) : Fin policies.length → ℝ :=
  fun i => weights.getD i 0

theorem mass_eq_sum (weights : List ℝ) (policies : List PolicyIndex)
    (head : PolicyIndex → Action) (u : Action) :
    machineActionMass weights policies head u =
      ∑ i : Fin policies.length, if stepAt policies head i = u then qAt weights policies i else 0 := by
  unfold machineActionMass stepAt qAt
  induction policies generalizing weights with
  | nil => simp
  | cons p ps ih =>
    cases weights with
    | nil => simp
    | cons w ws =>
      erw [Fin.sum_univ_succ]
      by_cases hp : head p = u
      · simp [List.zip_cons_cons, hp, ih ws]
      · simp [List.zip_cons_cons, hp, ih ws]

theorem mass_eq_actionMarginal [Fintype Action] (weights : List ℝ)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action) :
    machineActionMass weights policies head u =
      ActionMarginal.actionMarginal (stepAt policies head) (qAt weights policies) u := by
  rw [mass_eq_sum, ActionMarginal.actionMarginal, Finset.sum_filter]

theorem mass_nonneg (weights : List ℝ) (hw : ∀ x ∈ weights, 0 ≤ x)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action) :
    0 ≤ machineActionMass weights policies head u := by
  unfold machineActionMass
  apply List.sum_nonneg
  intro x hx
  obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
  exact hw _ (List.mem_of_mem_filter hp |> fun h => (List.of_mem_zip h).1)

theorem mass_of_not_taken (weights : List ℝ) (policies : List PolicyIndex)
    (head : PolicyIndex → Action) (u : Action) (hu : u ∉ policies.map head) :
    machineActionMass weights policies head u = 0 := by
  unfold machineActionMass
  have : (weights.zip policies).filter (fun p => decide (head p.2 = u)) = [] := by
    apply List.filter_eq_nil_iff.mpr
    intro p hp
    have hp2 : p.2 ∈ policies := (List.of_mem_zip hp).2
    have : head p.2 ≠ u := fun h => hu (h ▸ List.mem_map_of_mem hp2)
    simpa using this
  simp [this]

end Bridge

/-! ## The theorems -/

variable [LinearOrder Action]

/-- On the posterior's ok arm the action is `chooseAction` on its weights, and the
ok arm has a candidate. -/
theorem machineAction_ok_iff (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action)
    (hrun : machineAction habit grade F opts policies head = .ok u) :
    ∃ ws, machinePosterior habit grade F opts policies = .ok ws ∧
      chooseAction (machineActionMass ws policies head) (policies.map head) = some u := by
  unfold machineAction at hrun
  cases hp : machinePosterior habit grade F opts policies with
  | error a => simp [hp] at hrun
  | ok ws =>
    refine ⟨ws, rfl, ?_⟩
    simp only [hp] at hrun
    cases hc : chooseAction (machineActionMass ws policies head) (policies.map head) with
    | none => simp [hc] at hrun
    | some v => simp [hc] at hrun; rw [hrun]

/-- **An ok posterior has policies**, so `machineAction`'s empty-candidate arm is
unreachable there. -/
theorem machineAction_ok_nonempty (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (ws : List ℝ)
    (hrun : machinePosterior habit grade F opts policies = .ok ws) :
    policies ≠ [] := by
  intro hnil
  subst hnil
  unfold machinePosterior at hrun
  cases htau : machineTau opts with
  | error a => simp [htau] at hrun
  | ok t => simp [htau, firstBot, finitePolicies] at hrun

/-- **`machineAction_isBayesAction` (W2).** On the ok arm the chosen action
satisfies `ActionMarginal.IsBayesAction` at the machine's weights: policies indexed
by `Fin n`, `Q` the machine's posterior, `step` each policy's current action.
`IsBayesAction` itself is not weakened and takes no hypothesis beyond `Fintype
Action` (its own binder). What the PROOF needs, and discharges from the posterior
rather than assuming: nonneg weights (`machinePosterior_isDistribution`), so an
action no policy takes (mass 0) cannot beat the chosen one; and a nonempty policy
list (`machineAction_ok_nonempty`). -/
theorem machineAction_isBayesAction [Fintype Action] (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action)
    (hrun : machineAction habit grade F opts policies head = .ok u) :
    ∃ ws, machinePosterior habit grade F opts policies = .ok ws ∧
      ActionMarginal.IsBayesAction (stepAt policies head) (qAt ws policies) u := by
  obtain ⟨ws, hp, hc⟩ := machineAction_ok_iff habit grade F opts policies head u hrun
  refine ⟨ws, hp, ?_⟩
  obtain ⟨hw, _⟩ := machinePosterior_isDistribution habit grade F opts policies ws hp
  obtain ⟨hmem, hmax, _⟩ := chooseAction_spec _ _ u hc
  intro u'
  rw [← mass_eq_actionMarginal, ← mass_eq_actionMarginal]
  by_cases h' : u' ∈ policies.map head
  · exact hmax u' h'
  · rw [mass_of_not_taken ws policies head u' h']
    exact mass_nonneg ws hw policies head u

/-- **`machineAction_tie` — the tie rule is doing something.** The chosen action is
the least maximiser in the order among the actions some policy takes: if two such
actions have the same mass and both are maximal, the chosen one is not the greater
of them (it is at or below the lesser). The tie is broken by the action order, not
by the order the policies are listed in (`tieFixture_ascending`). -/
theorem machineAction_tie (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (head : PolicyIndex → Action) (u : Action)
    (hrun : machineAction habit grade F opts policies head = .ok u) :
    ∃ ws, machinePosterior habit grade F opts policies = .ok ws ∧
      ∀ a b, a ∈ policies.map head → b ∈ policies.map head → a < b →
        machineActionMass ws policies head a = machineActionMass ws policies head b →
        (∀ v ∈ policies.map head, machineActionMass ws policies head v ≤
            machineActionMass ws policies head a) →
        u ≤ a ∧ u ≠ b := by
  obtain ⟨ws, hp, hc⟩ := machineAction_ok_iff habit grade F opts policies head u hrun
  refine ⟨ws, hp, ?_⟩
  obtain ⟨_, hmax, hleast⟩ := chooseAction_spec _ _ u hc
  intro a b ha hb hab heq hamax
  have hua : machineActionMass ws policies head a = machineActionMass ws policies head u :=
    le_antisymm (hmax a ha) (hamax u (by
      obtain ⟨hm, _, _⟩ := chooseAction_spec _ _ u hc; exact hm))
  have h1 : u ≤ a := hleast a ha hua
  exact ⟨h1, ne_of_lt (lt_of_le_of_lt h1 hab)⟩

/-! ## Reachability: an absent posterior is an absent action -/

/-- Whatever absence stopped the posterior stops the action, unchanged. -/
theorem machineAction_absent (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (F : PolicyIndex → EReal) (opts : MachineTemperature.TemperatureOpts)
    (policies : List PolicyIndex) (head : PolicyIndex → Action)
    (a : Absence PolicyIndex)
    (h : machinePosterior habit grade F opts policies = .error a) :
    machineAction habit grade F opts policies head = .error a := by
  simp [machineAction, h]

/-- **`allFreeEnergiesInfinite` gives no action** — the same input as
`allInfiniteIsRefused`. No default action is stood in. -/
theorem allInfiniteHasNoAction (habit : PolicyIndex → ℝ)
    (grade : PolicyIndex → Holes.ExpectedFreeEnergyValue)
    (π₀ : PolicyIndex) (head : PolicyIndex → Action)
    (tauMin spread gain beta : ℝ) (hbeta : 0 < beta) :
    machineAction habit grade (fun _ => ⊤)
        ⟨.variationalBetaGamma, tauMin, spread, gain, some (.finite beta)⟩ [π₀] head
      = .error .allFreeEnergiesInfinite :=
  machineAction_absent _ _ _ _ _ _ _ (allInfiniteIsRefused habit grade π₀ tauMin spread gain beta hbeta)

/-- **The tie rule, exhibited.** Two actions of equal mass: the ascending one is
chosen whichever way round the candidates arrive. -/
theorem tieFixture_ascending :
    chooseAction (fun _ : Bool => (0 : ℝ)) [true, false] = some false ∧
    chooseAction (fun _ : Bool => (0 : ℝ)) [false, true] = some false := by
  constructor <;> simp [chooseAction, pickFirstMax, List.insertionSort, Bool.le_iff_imp]

/-- **And a strict maximum is not a tie**: the greater mass wins even when it is
the greater action. -/
theorem strictMaxWinsOverOrder :
    chooseAction (fun b : Bool => if b then (1 : ℝ) else 0) [false, true] = some true := by
  simp [chooseAction, pickFirstMax, List.insertionSort, Bool.le_iff_imp]

end

#print axioms machineActionMass
#print axioms pickFirstMax
#print axioms chooseAction
#print axioms machineAction
#print axioms pickFirstMax_spec
#print axioms chooseAction_spec
#print axioms chooseAction_isSome
#print axioms stepAt
#print axioms qAt
#print axioms mass_eq_sum
#print axioms mass_eq_actionMarginal
#print axioms mass_nonneg
#print axioms mass_of_not_taken
#print axioms machineAction_ok_iff
#print axioms machineAction_ok_nonempty
#print axioms machineAction_isBayesAction
#print axioms machineAction_tie
#print axioms machineAction_absent
#print axioms allInfiniteHasNoAction
#print axioms tieFixture_ascending
#print axioms strictMaxWinsOverOrder

end DarkTower.WarMachine.Proof2.ActionAtMachine
