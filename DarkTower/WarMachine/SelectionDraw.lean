import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# The tie-break draw is a sealed input of the selection step (defect line R13)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R13 (claude-9,
2026-10-26, from U3; cause found by codex-14).

Observed, production-reachable: `select-live` calls `canonical-selection/evaluate`
with no draw (futon2 `meta_live_outer_selector.clj:846-849`); on an exact
canonical-G tie `evaluate` takes `(rand)` (`outer_canonical_selection.clj:39`),
seals the chosen action into the carrier and the receipt, and records the draw
as `:draw {:law :uniform-over-equal-minima :u u :candidates [...]}` (lines
51-52).  machinery-150 attempt-002 had an exact tie (M-war-machine-wiring and
M-recommendation-bindings, both `G = -3.9560226735640867`), so this ran on a real
click.  The receipt says what happened; the choice cannot be recomputed from the
click's inputs, because the draw is not among them.

Clause: the selection step is a function of its sealed inputs.  A tie-break is
admitted only through a sealed entropy input, a draw carried in the step's input
record; a step whose output depends on a value not in its input record is not a
valid step.  Companion to R3's recomputability (`IncrementalTaskFrontier`): a Q8
recomputation must reproduce the tie-break from the record.

Encoding.  `expectedOutput` is the selection law as a function of
`SelectionInputs`; `SelectionStep.Valid` says the step's output *is*
`expectedOutput` of its inputs.  Where the law has no output (a tie with no
sealed draw, or a draw outside `[0, 1)`), no selected output is valid; the only
conforming behaviour there is a typed refusal (the Clojure's
`:invalid-canonical-tie-draw` shape, extended to the absent draw).  Scores and
the drawn value are rationals here; the Clojure's doubles are read as the
decimals the receipt prints.  Selection within a tie is `⌊u · n⌋`-th of the
tied entries in sealed-menu order, as `evaluate` computes it.

Direction of conformance: forward requirement on the selection step; the
observed receipt is a failing control.  Nothing here is derived from the runner.
-/

namespace DarkTower.WarMachine.SelectionDraw

/-- A scored frontier row as `evaluate` sees it: policy, cascade digest, score.
Rows are kept in sealed-menu order. -/
structure Entry where
  policy : String
  digest : String
  G : ℚ
  deriving DecidableEq, Repr

/-- The entropy input.  `u` is the receipt's `:u`. -/
structure Draw where
  u : ℚ
  deriving DecidableEq, Repr

def Draw.Valid (d : Draw) : Prop := 0 ≤ d.u ∧ d.u < 1

instance (d : Draw) : Decidable d.Valid := by unfold Draw.Valid; infer_instance

/-- The selection step's sealed input record: the scored rows and, if the click
supplied one, its draw.  Today's `select-live` never supplies one. -/
structure SelectionInputs where
  entries : List Entry
  draw : Option Draw
  deriving DecidableEq, Repr

/-- The selection step's output: the selected row and the draw it records
(`:draw` is `nil` when there was no tie). -/
structure SelectionOutput where
  selected : Entry
  draw : Option Draw
  deriving DecidableEq, Repr

def minG : List Entry → Option ℚ
  | [] => none
  | e :: es => some ((es.map (·.G)).foldl min e.G)

/-- The rows at the minimum score, in sealed-menu order (the receipt's
`:candidates`). -/
def minima (entries : List Entry) : List Entry :=
  entries.filter (fun e => decide (some e.G = minG entries))

/-- Uniform over equal minima, deterministic in the draw: the `⌊u · n⌋`-th tied
row. -/
def selectTied (tied : List Entry) (d : Draw) : Option Entry :=
  tied[⌊d.u * tied.length⌋₊]?

/-- The selection law.  A unique minimum needs no draw and records none; a tie
needs a valid sealed draw and records it; otherwise there is no output. -/
def expectedOutput (i : SelectionInputs) : Option SelectionOutput :=
  match minima i.entries with
  | [] => none
  | [e] => some ⟨e, none⟩
  | tied =>
    match i.draw with
    | none => none
    | some d =>
      if d.Valid then
        (selectTied tied d).map (fun e => ⟨e, some d⟩)
      else none

structure SelectionStep where
  inputs : SelectionInputs
  output : SelectionOutput
  deriving DecidableEq, Repr

/-- R13.  The step's output is the law applied to its sealed inputs. -/
def SelectionStep.Valid (s : SelectionStep) : Prop :=
  expectedOutput s.inputs = some s.output

instance (s : SelectionStep) : Decidable s.Valid := by
  unfold SelectionStep.Valid; infer_instance

/-- Recomputable from the record: two valid steps over the same sealed inputs
select the same row and record the same draw. -/
theorem recomputable_from_record (s t : SelectionStep)
    (hs : s.Valid) (ht : t.Valid) (h : s.inputs = t.inputs) : s.output = t.output := by
  unfold SelectionStep.Valid at hs ht
  rw [h] at hs
  exact Option.some.inj (hs.symm.trans ht)

/-- A tie with no sealed draw admits no selected output, whatever the output
claims and whatever draw it records. -/
theorem tie_without_sealed_draw_invalid (s : SelectionStep)
    (htie : 2 ≤ (minima s.inputs.entries).length)
    (hnone : s.inputs.draw = none) : ¬ s.Valid := by
  unfold SelectionStep.Valid expectedOutput
  intro h
  revert h htie
  cases minima s.inputs.entries with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b rest' => simp [hnone]

/-- A sealed draw outside `[0, 1)` admits no selected output on a tie. -/
theorem tie_with_invalid_draw_invalid (s : SelectionStep) (d : Draw)
    (htie : 2 ≤ (minima s.inputs.entries).length)
    (hd : s.inputs.draw = some d) (hbad : ¬ d.Valid) : ¬ s.Valid := by
  unfold SelectionStep.Valid expectedOutput
  intro h
  revert h htie
  cases minima s.inputs.entries with
  | nil => simp
  | cons a rest =>
    cases rest with
    | nil => simp
    | cons b rest' => simp [hd, hbad]

/-- A unique minimum is selected without a draw, whatever the inputs carry. -/
theorem unique_minimum_selected (i : SelectionInputs) (e : Entry)
    (hmin : minima i.entries = [e]) :
    SelectionStep.Valid ⟨i, ⟨e, none⟩⟩ := by
  unfold SelectionStep.Valid expectedOutput
  rw [hmin]

/-! ## Control: machinery-150 attempt-002

The receipt's `:canonical-frontier :entries` (`002-selection.edn`, attempt-002,
`data/wm-full-loop-machinery-150/wm-contract-machinery-150-v1/`), four scored
rows; listed here in the order the receipt's `:draw :candidates` certifies for
the tied pair (M-war-machine-wiring before M-recommendation-bindings).  Policy
ids are the receipt's; digests are the receipt's cascade digests. -/

def selfImprovementLoop : Entry :=
  ⟨"M-self-improvement-loop/policy-1bbcf6a06eb2766b5e77",
   "f79e6e5b560469f5f1a5edb69cda2e990a8f33fd6aa6228c13913e06fb031b4f",
   -39443039235640867 / 10 ^ 16⟩

def stackGeometry : Entry :=
  ⟨"M-stack-geometry/policy-c7d7518e1e185c2e2318",
   "c601dc5697a2d5d65c5c8440f08b3905cee1030b9a62dfa03e2ad5e7ab202c27",
   -2004267726446009 / 10 ^ 15⟩

def warMachineWiring : Entry :=
  ⟨"M-war-machine-wiring/policy-2629917c87a61978be8f",
   "3a5228e7942579f3e0095ee4a902b1b08a0a9d0bf7a11c966c52bddbbb4e4475",
   -39560226735640867 / 10 ^ 16⟩

def recommendationBindings : Entry :=
  ⟨"M-recommendation-bindings/policy-7e8a0806fea29fa47914",
   "13c0068ddbc12266370e59d82812d9b10472a38831e7e61f0e9aef6a9e690e11",
   -39560226735640867 / 10 ^ 16⟩

def m150Entries : List Entry :=
  [selfImprovementLoop, stackGeometry, warMachineWiring, recommendationBindings]

theorem m150_tied : minima m150Entries = [warMachineWiring, recommendationBindings] := by
  native_decide

/-- The receipt's `:u`. -/
def m150Draw : Draw := ⟨22534045104810763 / 10 ^ 17⟩

/-- The observed step: no draw among the inputs, a selected action and a
recorded draw in the output. -/
def m150Step : SelectionStep where
  inputs := ⟨m150Entries, none⟩
  output := ⟨warMachineWiring, some m150Draw⟩

/-- The observed step is a certified violation of R13. -/
theorem m150_step_invalid : ¬ m150Step.Valid :=
  tie_without_sealed_draw_invalid m150Step (by rw [show m150Step.inputs.entries = m150Entries from rfl, m150_tied]; decide) rfl

/-- The same conclusion by evaluation, independent of the general theorem. -/
theorem m150_step_invalid_decide : ¬ m150Step.Valid := by native_decide

/-- The repaired record (codex-14's proposal, adopted by claude-9): the receipt's
own `:u` sealed as the step's input.  It selects what the receipt selected. -/
def m150Repaired : SelectionStep where
  inputs := ⟨m150Entries, some m150Draw⟩
  output := ⟨warMachineWiring, some m150Draw⟩

theorem m150_repaired_valid : m150Repaired.Valid := by native_decide

/-- A different sealed draw selects the other tied row. -/
def m150OtherDraw : Draw := ⟨3 / 4⟩

def m150Other : SelectionStep where
  inputs := ⟨m150Entries, some m150OtherDraw⟩
  output := ⟨recommendationBindings, some m150OtherDraw⟩

theorem m150_other_valid : m150Other.Valid := by native_decide

/-- Two draws, two valid selections: the draw is what decides the tie, and it
decides it from the record. -/
theorem m150_two_draws_two_selections :
    m150Repaired.output.selected ≠ m150Other.output.selected := by native_decide

/-- The repaired record with the draw sealed but the other row claimed is
invalid: the draw, not the author, picks. -/
def m150WrongRow : SelectionStep where
  inputs := ⟨m150Entries, some m150Draw⟩
  output := ⟨recommendationBindings, some m150Draw⟩

theorem m150_wrong_row_invalid : ¬ m150WrongRow.Valid := by native_decide

/-- A draw of `1` is refused on a tie (`:invalid-canonical-tie-draw`). -/
def m150UnitDraw : SelectionStep where
  inputs := ⟨m150Entries, some ⟨1⟩⟩
  output := ⟨warMachineWiring, some ⟨1⟩⟩

theorem m150_unit_draw_invalid : ¬ m150UnitDraw.Valid :=
  tie_with_invalid_draw_invalid m150UnitDraw ⟨1⟩
    (by rw [show m150UnitDraw.inputs.entries = m150Entries from rfl, m150_tied]; decide)
    rfl (by unfold Draw.Valid; norm_num)

/-- Without the recommendation-bindings row there is a unique minimum; the step
selects it with no draw, whether or not one was supplied. -/
theorem m150_untied_needs_no_draw :
    SelectionStep.Valid ⟨⟨[selfImprovementLoop, stackGeometry, warMachineWiring], some m150Draw⟩,
      ⟨warMachineWiring, none⟩⟩ := by native_decide

end DarkTower.WarMachine.SelectionDraw
