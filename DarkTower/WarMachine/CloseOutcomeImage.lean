import DarkTower.WarMachine.Requirements

/-!
# The `RunOutcome` image of the runner's close vocabulary, and the law that a
# successful close is not an injury (R22, R23)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R22 and R23
(claude-9, 2026-10-26) and the packet
`packets/R22-R23-grounded-progress-outcome-packet.md`.  Lean first; the
Clojure conforms in a separate packet.

**What happened.**  The first reading-era click (run `2026-10-26-8be8ff03…`)
closed `:grounded-progress` with `:failure {:absent :no-failure}` and a
grounding commit (futon5a `09a7cb8d…`).  Two consumers do not know that
keyword.

1. `futon2/src/futon2/aif/previous_run.clj` `lean-outcomes` maps five
   keywords to `Requirements.RunOutcome`; `typed-outcome` sends any other
   present outcome to `:invalid` with the raw kept.  The Q6 terminal of that
   run reads `{:status :present :outcome :invalid :raw :grounded-progress}`
   (R22).
2. `futon2/src/futon2/aif/meta_terminal_injury.clj` `classify`: a record with
   no failure kind is a non-injury only when its terminal outcome is in
   `successful-outcomes` (`#{:success :closed :grounded-change
   :cohort-complete}`) or absent.  `:grounded-progress` is in neither, so
   click 1's record was classified `:injury` with `:failure-kind :none`, and
   the durable ledger opened `injury/9c6220388033cbd1fbc888cdf6bb3a5b9a3082c0`
   (entry 45).  The second click found it open and
   `meta_self_heal_production.clj` `route!` refused before ordinary selection
   (R23).  Every click after a successful click does this until the
   vocabulary is fixed.

**The runner's vocabulary.**  `CloseOutcome` is `full_loop_cohort.clj`
`outcome-kinds`, the sixteen keywords a cohort attempt's `:closed` checkpoint
may carry.  `lean-outcomes` also accepts `:question`, `:timed-out`,
`:timeout`, `:changed` and `:refused`, none of which is in `outcome-kinds`;
they are outside this module.

**The image question (settled here).**  Which `RunOutcome` is a grounded
progress: `changed`.  `full_loop_runner.clj` `classify-grounded-outcome`
derives `:grounded-progress` from a requested `:grounded-change`: the caller
supplied a reviewed, grounded increment, and what differs is only that the
declared products were not mechanically verified closed.
`grounded-progress-must-be-grounded` (`full_loop_cohort.clj`) ties the
keyword to a grounding commit, as `grounded-change-must-be-grounded` does for
`:grounded-change`.  The world changed by a commit in both cases; `changed` is
the image of both.  No constructor is added to `Requirements.RunOutcome`, so
this is not a specification change.

**The other images.**  `image` is total.  Four keywords are transcribed from
`lean-outcomes` as the code already has them (`grounded-change`,
`already-satisfied`, `grounded-no-change`, `guardrail-refusal`); the eleven
the code sends to `:invalid` are kept at `invalid` here.  That is a
transcription, not a decision: whether `:build-failed` or
`:dispatch-failed` should read as `refused`, or `:abstained` needs a value
outside `RunOutcome` (the Q6 terminal already records an abstaining
decision as `:abstained`, outside the `RunOutcome` vocabulary), is not
decided by this module.  `code_image_differs_exactly_at_groundedProgress`
says the only keyword on which this module and `typed-outcome` disagree is
`:grounded-progress`.

**The terminal-classification law.**  `closeVerdict` says what the close
outcome alone decides about the terminal classification, as a function of
(image, failure present?).  A close whose image is `changed` or
`alreadySatisfied` and whose record carries no failure is a non-injury.  A
close whose image is `invalid` with no failure is not thereby an injury
either: the injury classifier's cause is a failure, not a keyword the
specification does not know.  `none` means the close does not decide: when a
failure is present its kind decides (the typed non-injury kinds and the
producer-qualified `:already-satisfied` are beside the record and outside
this module); and for `question`, `refused` and `timedOut` with no failure
the cell is left undecided (hole, not decided here: the code opens an
injury there, the "cause is a failure" reading would not).

**The witness (Lean specifies, code conforms; witness mode certifies the
violation).**  `successfulOutcomes` transcribes the code's set;
`codeVerdictNoFailure` transcribes the branch of `classify` for a record
with no failure kind.  `click1_code_injury_law_nonInjury` is the one
theorem the packet asks for: the code classifies click 1's close as an
injury and the law says non-injury.  `disagreement_set` is what I read
differently from the packet: the disagreement is not on exactly this
keyword.  Over the cohort vocabulary with no failure, the code and the law
agree only on `:grounded-change` (non-injury) and `:guardrail-refusal`
(undecided by the close); `:already-satisfied` and `:grounded-no-change`
are successful images the code also classifies as injury when no failure
kind is present (the producer-qualified branch rescues `:already-satisfied`
only as a *failure* of kind `:already-satisfied` at `:author-wait`), and the
eleven `invalid`-image keywords are injuries in the code by the same
default.  `successful_images_disagreement` names the three with a
successful image.  Keywords such as `:build-failed` with no failure in the
record are contradictory records; the image function cannot see that, and
that case is not decided here.
-/

namespace DarkTower.WarMachine.CloseOutcomeImage

open DarkTower.WarMachine.Requirements (RunOutcome)

/-- `full_loop_cohort.clj` `outcome-kinds`: the keywords a cohort attempt's
`:closed` checkpoint may carry.  `:cohort-complete` is not among them (a
scheduler-level signal, per that set's docstring). -/
inductive CloseOutcome where
  | groundedChange
  | groundedProgress
  | alreadySatisfied
  | groundedNoChange
  | artifactOnly
  | abstained
  | noSelection
  | agentUnavailable
  | guardrailRefusal
  | dispatchFailed
  | buildFailed
  | substrateUnavailable
  | incomplete
  | cancelled
  | historicalVerificationAwaitingValidation
  | historicalVerificationRefused
  deriving DecidableEq, Repr

/-- The image of a close outcome in `Requirements.RunOutcome`.  Total.
`groundedProgress ↦ changed` is the value this module settles; the four
mapped keywords are `lean-outcomes` as the code has them; the rest are the
code's `:invalid` default, transcribed and not decided. -/
def image : CloseOutcome → RunOutcome
  | .groundedChange => .changed
  | .groundedProgress => .changed
  | .alreadySatisfied => .alreadySatisfied
  | .groundedNoChange => .alreadySatisfied
  | .guardrailRefusal => .refused
  | _ => .invalid

/-- The answer to the packet's question, as a theorem. -/
theorem groundedProgress_image : image .groundedProgress = .changed := rfl

/-- A grounded progress and a grounded change have the same image: both are
grounded by a commit. -/
theorem groundedProgress_image_eq_groundedChange :
    image .groundedProgress = image .groundedChange := rfl

/-- `previous_run.clj` `lean-outcomes`, restricted to the cohort vocabulary:
`some` is the mapped `RunOutcome`; `none` is a keyword the map does not
know, which `typed-outcome` sends to `:invalid` with the raw kept. -/
def codeImage : CloseOutcome → Option RunOutcome
  | .groundedChange => some .changed
  | .alreadySatisfied => some .alreadySatisfied
  | .groundedNoChange => some .alreadySatisfied
  | .guardrailRefusal => some .refused
  | _ => none

/-- `typed-outcome`'s `:outcome` for a present close outcome with no
downstream refusal, no Q6 refusal and a choosing decision. -/
def codeTypedOutcome (c : CloseOutcome) : RunOutcome := (codeImage c).getD .invalid

/-- The Q6 consumer (R22): the code's typed outcome and the image disagree on
exactly `:grounded-progress`. -/
theorem code_image_differs_exactly_at_groundedProgress :
    ∀ c, codeTypedOutcome c ≠ image c ↔ c = .groundedProgress := by
  intro c; cases c <;> decide

/-- The witnessed R22 value: the Q6 terminal of click 1 reads `:invalid`. -/
theorem click1_q6_reads_invalid : codeTypedOutcome .groundedProgress = .invalid := rfl

/-! ## The terminal-classification law -/

inductive Verdict where
  | injury
  | nonInjury
  deriving DecidableEq, Repr

/-- What the close outcome alone decides about the terminal classification,
from its image and whether the record carries a failure.  `none`: the close
does not decide (a failure's kind decides; or the cell is not decided by
this module, see the header). -/
def closeVerdict : RunOutcome → Bool → Option Verdict
  | .changed, false => some .nonInjury
  | .alreadySatisfied, false => some .nonInjury
  | .invalid, false => some .nonInjury
  | _, _ => none

/-- The close outcome is never the cause of an injury. -/
theorem close_never_opens_injury : ∀ (img : RunOutcome) (b : Bool),
    closeVerdict img b ≠ some .injury := by
  intro img b; cases img <;> cases b <;> decide

/-- Packet clause 2, first half: a successful image with no failure is a
non-injury. -/
theorem successful_image_no_failure_nonInjury :
    ∀ img, (img = .changed ∨ img = .alreadySatisfied) →
      closeVerdict img false = some .nonInjury := by
  intro img h; rcases h with rfl | rfl <;> rfl

/-- Packet clause 2, second half: an image the specification does not know
is not thereby an injury. -/
theorem invalid_not_thereby_injury : closeVerdict .invalid false ≠ some .injury := by
  decide

/-- Click 1's close under the law: grounded progress, no failure, non-injury. -/
theorem click1_law_nonInjury :
    closeVerdict (image .groundedProgress) false = some .nonInjury := rfl

/-! ## The witness: the code's classifier on click 1's close -/

/-- The keyword space of `meta_terminal_injury.clj` `successful-outcomes`:
the cohort closes plus three keywords that are not in `outcome-kinds`. -/
inductive Keyword where
  | close : CloseOutcome → Keyword
  | success
  | closed
  | cohortComplete
  deriving DecidableEq, Repr

/-- `meta_terminal_injury.clj` line 15 (codex-68, futon2 `cb1744798`):
`#{:success :closed :grounded-change :cohort-complete}`. -/
def successfulOutcomes : Finset Keyword :=
  {.close .groundedChange, .success, .closed, .cohortComplete}

/-- `classify` (line 137) for a record with no failure kind and no explicit
non-injury kind: `:absent-terminal-failure` when the terminal outcome is
absent, `:successful-task-outcome` when it is in `successful-outcomes`,
else the default injury branch (`:failure-kind :none`). -/
def codeVerdictNoFailure : Option Keyword → Verdict
  | none => .nonInjury
  | some k => if k ∈ successfulOutcomes then .nonInjury else .injury

/-- Click 1's terminal record as `classify` reads it: `[:terminal-receipt
:outcome] :grounded-progress`, `:failure {:absent :no-failure}` (no kind). -/
def click1Outcome : Option Keyword := some (.close .groundedProgress)

/-- The one witness theorem: the code classifies click 1's close as an injury
(ledger entry 45, `injury/9c622038…`) and the law says it is a non-injury. -/
theorem click1_code_injury_law_nonInjury :
    codeVerdictNoFailure click1Outcome = .injury ∧
      closeVerdict (image .groundedProgress) false = some .nonInjury := by
  decide

/-- The code and the law disagree on a cohort close with no failure. -/
def disagrees (c : CloseOutcome) : Prop :=
  codeVerdictNoFailure (some (.close c)) = .injury ∧
    closeVerdict (image c) false = some .nonInjury

instance : DecidablePred disagrees := fun _ => inferInstanceAs (Decidable (_ ∧ _))

/-- Read differently from the packet: over the cohort vocabulary with no
failure, the code and the law agree only on `:grounded-change` and
`:guardrail-refusal`. -/
theorem disagreement_set :
    ∀ c, disagrees c ↔ (c ≠ .groundedChange ∧ c ≠ .guardrailRefusal) := by
  intro c; cases c <;> decide

/-- The successful-image keywords the code classifies as injury with no
failure kind present: `:grounded-progress`, `:already-satisfied`,
`:grounded-no-change`. -/
theorem successful_images_disagreement :
    ∀ c, (image c = .changed ∨ image c = .alreadySatisfied) ∧ disagrees c ↔
      (c = .groundedProgress ∨ c = .alreadySatisfied ∨ c = .groundedNoChange) := by
  intro c; cases c <;> decide

/-- The code's set names only one cohort close. -/
theorem successfulOutcomes_cohort :
    ∀ c, Keyword.close c ∈ successfulOutcomes ↔ c = .groundedChange := by
  intro c; cases c <;> decide

#print axioms code_image_differs_exactly_at_groundedProgress
#print axioms click1_code_injury_law_nonInjury
#print axioms disagreement_set

end DarkTower.WarMachine.CloseOutcomeImage
