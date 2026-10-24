import DarkTower.WarMachine.R20RunPrefixExtension
import DarkTower.WarMachine.CheckedReturnObservation

/-!
# Checked problem-map carry across an R20 certified prefix

`R20Run.RunCertified` certifies the existing click sequence and all of its
row, wiring, prior, valence, theta, and carry obligations. This module wraps
that *same* sequence with supplied proof-bearing problem-map inputs and return
reports. It neither modifies nor duplicates `RunCertified`.

For click `i`, `input i` is the checked map before the return, `report i` is
optional, and `output i` is definitionally constrained to
`CheckedProblemMap.update (input i) (report i)`. The scored observation is not
an independent field: `observation` is
`CheckedReturnObservation.returnObs` for that exact update. At every certified
boundary `i < n`, `input (i+1) = output i` as exact proof maps, a deliberately
stronger condition than equality of closure sets.

This is a supplied synthetic enrichment. It is not a runtime decoder, does
not infer association with existing R20 ports, does not make an old closure a
fresh learning success, and introduces no probability, preference, prior,
credit, scorer, or liveness semantics.
-/

namespace DarkTower.WarMachine.R20CheckedMapCarry

open R20Run R20RunPrefixExtension
open CheckedProblemMap CheckedReturnObservation

noncomputable section

universe u

variable {Policy : Type} [Fintype Policy] [Nonempty Policy]
variable {S : Type u} [Fintype S] [DecidableEq S] {I : S → Prop}
variable {Label : Type}

/-- An exact checked-map enrichment of the same R20 click sequence through
index `n` (inclusive). -/
structure CheckedMapRun
    (L : AffectiveLevel) (relation : R15StrategicTarget.Target →
      R15StrategicTarget.Target → CTauClassPreference.TargetRelation)
    (clicks : ℕ → Click Policy) (initialMap : ProblemMap I)
    (scored : Finset S) (n : ℕ) : Type (max u 1) where
  input : ℕ → ProblemMap I
  report : ℕ → Option (ReturnReport I Label)
  output : ℕ → ProblemMap I
  certified : RunCertified L relation clicks n
  initial : input 0 = initialMap
  output_eq : ∀ i ≤ n, output i = update (input i) (report i)
  boundary : ∀ i < n, input (i + 1) = output i

/-- Input index `i`, output index `i`: the closure observation of the same
step's checked update. It is computed, not freely supplied. -/
def observation {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n) (i : ℕ) : Finset S :=
  returnObs (run.input i) scored id (run.report i)

theorem observation_eq_output {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n) {i : ℕ} (hi : i ≤ n) :
    observation run i = closureObs scored (run.output i) := by
  simp [observation, returnObs, run.output_eq i hi]

/-- Wrapper certification preserves every original R20 obligation on the
same underlying click function. -/
theorem runCertified {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n) :
    RunCertified L relation clicks n :=
  run.certified

theorem exact_boundary {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n) {i : ℕ} (hi : i < n) :
    run.input (i + 1) = update (run.input i) (run.report i) := by
  rw [run.boundary i hi, run.output_eq i (Nat.le_of_lt hi)]

/-- Every reported observed closure is justified by a proof in the exact
same-step output map. -/
theorem observation_sound {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n) {i : ℕ} {s : S}
    (h : s ∈ observation run i) : I s :=
  returnObs_sound h

/-- Apply precisely reports `0 .. n-1` to obtain input map `n`. -/
def foldReports (initialMap : ProblemMap I)
    (report : ℕ → Option (ReturnReport I Label)) (n : ℕ) : ProblemMap I :=
  (List.range n).foldl (fun m i => update m (report i)) initialMap

theorem input_eq_foldReports {L relation clicks initialMap scored N}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored N) {n : ℕ} (hn : n ≤ N) :
    run.input n = foldReports initialMap run.report n := by
  induction n with
  | zero => simpa [foldReports] using run.initial
  | succ n ih =>
      have hnN : n < N := by omega
      rw [run.boundary n hnN, run.output_eq n (by omega), ih (by omega)]
      simp [foldReports, List.range_succ, List.foldl_append]

/-- Checked updates are monotone across every earlier report: a statement
closed in the initial map remains closed in every input map of the prefix. -/
theorem initial_closed_stays_closed_input {L relation clicks initialMap scored N}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored N) {n : ℕ} (hn : n ≤ N) {s : S}
    (h : Closed initialMap s) : Closed (run.input n) s := by
  induction n with
  | zero => simpa [run.initial] using h
  | succ n ih =>
      rw [run.boundary n (by omega), run.output_eq n (by omega)]
      exact closed_update _ (ih (by omega))

theorem initial_closed_stays_closed_output {L relation clicks initialMap scored N}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored N) {n : ℕ} (hn : n ≤ N) {s : S}
    (h : Closed initialMap s) : Closed (run.output n) s := by
  rw [run.output_eq n hn]
  exact closed_update _ (initial_closed_stays_closed_input run hn h)

/-- A one-step extension is conditional on an existing R20 successor and the
exact new checked-map boundary. No successor existence is asserted. -/
def extend
    {L relation clicks initialMap scored n}
    (run : CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored n)
    (successor : ClickCertified L relation (clicks (n + 1)))
    (carries : Carries L (clicks n) (clicks (n + 1)))
    (nextReport : Option (ReturnReport I Label)) :
    CheckedMapRun (Policy := Policy) (I := I) (Label := Label)
      L relation clicks initialMap scored (n + 1) where
  input i := if i ≤ n then run.input i else run.output n
  report i := if i ≤ n then run.report i else nextReport
  output i := if i ≤ n then run.output i else update (run.output n) nextReport
  certified := (runCertified_succ_iff L relation clicks n).2
    ⟨run.certified, successor, carries⟩
  initial := by simpa using run.initial
  output_eq := by
    intro i hi
    by_cases h : i ≤ n
    · simp only [if_pos h]
      exact run.output_eq i h
    · have heq : i = n + 1 := by omega
      subst i
      simp
  boundary := by
    intro i hi
    by_cases h : i < n
    · simp only [if_pos (Nat.le_of_lt h), if_pos (Nat.succ_le_iff.mpr h)]
      exact run.boundary i h
    · have heq : i = n := by omega
      subst i
      simp

/-! ## Existing R20 two-click witness, enriched with checked map carry -/

open R20RunExample
open CheckedProblemMap (Stmt interp Verdict m0 censoredHelper foundationOnly
  adapterArt foundationArt viaFoundation)

def exampleInput : ℕ → ProblemMap interp
  | 0 => m0
  | _ => update m0 (some censoredHelper)

def exampleReport : ℕ → Option (ReturnReport interp Verdict)
  | 0 => some censoredHelper
  | _ => some foundationOnly

def exampleOutput (i : ℕ) : ProblemMap interp :=
  update (exampleInput i) (exampleReport i)

def exampleCheckedRun : CheckedMapRun (Label := Verdict)
    R20Run.flatLevel R15InjuryTier.relationExample
    (R20RunExample.clicks R20RunExample.click1) m0
    CheckedReturnObservation.scoredFix 1 where
  input := exampleInput
  report := exampleReport
  output := exampleOutput
  certified := R20RunExample.example_runCertified
  initial := rfl
  output_eq := by intros; rfl
  boundary := by
    intro i hi
    have : i = 0 := by omega
    subst i
    rfl

theorem example_preserves_original_R20 :
    RunCertified R20Run.flatLevel R15InjuryTier.relationExample
      (R20RunExample.clicks R20RunExample.click1) 1 :=
  runCertified exampleCheckedRun

/-- The first checked censored helper supplies the adapter; the second report
supplies the foundation, so the actual second observation closes consumer. -/
theorem example_second_observes_consumer :
    Stmt.consumer ∈ observation exampleCheckedRun 1 := by
  unfold observation
  rw [mem_returnObs]
  refine ⟨by simp [CheckedReturnObservation.scoredFix], ?_⟩
  apply Closed.reduction viaFoundation
  · simp [exampleCheckedRun, exampleInput, exampleReport, update, admit,
      censoredHelper, foundationOnly, m0]
  · intro s hs
    simp [viaFoundation] at hs
    rcases hs with rfl | rfl
    · exact Closed.artifact foundationArt (by
        simp [exampleCheckedRun, exampleInput, exampleReport, update, admit,
          censoredHelper, foundationOnly])
    · exact Closed.artifact adapterArt (by
        simp [exampleCheckedRun, exampleInput, exampleReport, update, admit,
          censoredHelper, foundationOnly])

/-- Fabricating the consumer observation in the first step, where foundation
is present but adapter is not, is rejected by the actual closure relation. -/
theorem foundation_without_adapter_cannot_observe_consumer :
    Stmt.consumer ∉ returnObs m0 CheckedReturnObservation.scoredFix id
      (some foundationOnly) :=
  CheckedReturnObservation.foundationOnly_not_observed

/-- Optional report absence remains an exact unchanged-map carry. -/
def absentCheckedRun : CheckedMapRun (Label := Verdict)
    R20Run.flatLevel R15InjuryTier.relationExample
    (R20RunExample.clicks R20RunExample.click1) m0
    CheckedReturnObservation.scoredFix 1 where
  input := fun _ => m0
  report := fun _ => (none : Option (ReturnReport interp Verdict))
  output := fun _ => m0
  certified := R20RunExample.example_runCertified
  initial := rfl
  output_eq := by intros; rfl
  boundary := by intros; rfl

theorem absent_reports_leave_second_input_unchanged :
    CheckedMapRun.input absentCheckedRun 1 = m0 := rfl

/-- Resetting the second input to `m0` after the checked adapter was admitted
cannot satisfy exact boundary carry. -/
theorem reset_boundary_refused :
    exampleCheckedRun.output 0 ≠ m0 := by
  intro h
  have hadapter : adapterArt ∈ (exampleCheckedRun.output 0).artifacts := by
    simp [exampleCheckedRun, exampleOutput, exampleInput, exampleReport,
      update, admit, censoredHelper]
  rw [h] at hadapter
  simpa [m0] using hadapter

#print axioms runCertified
#print axioms input_eq_foldReports
#print axioms initial_closed_stays_closed_input
#print axioms observation_sound
#print axioms example_second_observes_consumer
#print axioms reset_boundary_refused

end
end DarkTower.WarMachine.R20CheckedMapCarry
