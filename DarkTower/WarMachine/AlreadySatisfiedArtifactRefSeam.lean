import DarkTower.WarMachine.HistoricalMisclassificationCorrection

/-!
# The already-satisfied close the grammar names, and the artifact-ref seam
# that renamed it a build failure (R24)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R24 and
`packets/R24-already-satisfied-artifact-ref-seam-packet.md` (claude-9,
2026-10-26).  Lean first; the Clojure classifier and the Agency extraction
conform in their own packets.  Additions only, beside `CloseOutcomeImage`.

**What happened.**  The third reading-era click (`wm-click-9468efd5…`, run
`2026-10-26-f444287e…`) passed the ledger gate and ordinary selection chose
the policy click 1 had already grounded (futon5a `09a7cb8d…`).  The author
(zai-2, job `invoke-1793031107183-4318-2d1ee292`) answered in the author
prompt's rule-7 grammar (`full_loop_runner.clj` 3822–3830, futon2
`a54f360cf`): a feature card whose `:built` says "already satisfied at base
head 09a7cb8d", `:proof-ref` the full existing sha, and the last line
`FULL_LOOP_AUTHOR: REFUSE :already-satisfied-at-base-head`.  Three consumers
disagree about where the commit goes:

1. The Agency (`futon3c/src/futon3c/transport/http.clj` `first-artifact-ref`
   1478, `artifact-ref-re` 1466, futon3c `78087dd81`): the job's
   `:artifact-ref` is the leftmost match in the reply text of one regex whose
   alternatives are a GitHub PR link, `PR #n`, a 7–40 hex sha, or a
   `/`-rooted path with a source extension.  The reply names
   `holes/missions/M-recommendation-bindings.md` at offset 242 and
   `09a7cb8d` at 291 (re-run on the job's text, 2026-10-26), so the
   artifact-ref is `/missions/M-recommendation-bindings.md`.  `:proof-ref` is
   never read by the Agency.  (A FrontierMath-local path pre-filter runs
   first; it does not match this reply and is outside this module.)
2. The runner's classifier (`author-refusal-classification` 3250–3296, futon2
   `4ea9fe47e`): with the card saying already satisfied and an artifact-ref
   present, it runs `commit-exists-in?` on that string, whatever it is; a path
   is not a commit, so `{:outcome :invalid-author-refusal}`.  The card's
   `:proof-ref` is read elsewhere (`feature-artifact-refs` 3376–3394) as a
   file reference (`existing-file-ref`), never as a commit.
3. `throw-if-author-refused!` (3300–3338) closes each classification:
   `:invalid-author-refusal` as `{:outcome :build-failed :failure-kind
   :invalid-author-refusal}`; `:already-satisfied` as `{:outcome
   :already-satisfied :failure-kind :already-satisfied :failure-stage
   :author-wait :grounded-commit …}`, which `meta_terminal_injury.clj`
   `classify` (157–173, futon2 `4ea9fe47e`) rescues through
   `producer-qualified-already-satisfied?` (59–73) as a non-injury.

Result: RR `[:failure] {:kind :invalid-author-refusal :stage :author-wait}`,
outcome `:build-failed`; the terminal opened ledger entry 47
(`injury/2aef7e0c…`, `:open`, `:injury-predecessor nil`, cause pin the RR
`d36c4a64…`); click 4 meets an active injury (`SelfHealRoute.noFallback`).

**Part 1, the close the grammar names.**  `authoredClose` is
`alreadySatisfied`; its image is `alreadySatisfied`, a successful image, and
with no failure present the law says non-injury (`click3_law_nonInjury`, the
form of `CloseOutcomeImage.click1_law_nonInjury`).

**Part 2, the seam as a function.**  A reply is the list of its ref-like
tokens in text order (`Ref`: sha, path, PR link); `firstArtifactRef` is the
head.  `Card` carries the two things the classifier could read: whether it
says already satisfied, and `:proof-ref` as a sha.  `currentClassifier`
consumes only the extracted ref: a sha the store knows gives
`alreadySatisfied`; anything else gives `invalidAuthorRefusal`.
`repairedClassifier` is the definition the Clojure packet will conform to:
when the extracted ref is not a sha, it takes the card's `:proof-ref`, and
still refuses a commit the store does not know.  `recordOf` transcribes item
3: what each consumed value closes, outcome and failure kind.  `verdictOf`
is the terminal reading of a close: `closeVerdict` when the close decides,
else the kind's verdict (`kindVerdict`, transcribed from `classify` 171–173:
`:already-satisfied` is producer-qualified, `:invalid-author-refusal` takes
the default injury branch).

Theorems: (a) `witness_path_before_sha`: for `[path, sha]` with the card
naming the sha, the consumed close is `buildFailed` with kind
`invalidAuthorRefusal`, verdict injury, while the authored close is
`alreadySatisfied`, verdict non-injury.  (b) `control_sha_before_path`: for
`[sha, path]` the consumed close is `alreadySatisfied` and the verdicts
agree.  (c) `repaired_agrees_on_both_replies`: the repaired consumer agrees
with the authored close on both replies.  `order_alone_decides` says the two
replies differ only in order and the current consumer answers differently;
`current_ignores_card` says the current consumer never reads `:proof-ref`.
Bad cases for the repaired consumer: a `:proof-ref` the store does not know
still refuses (`repaired_refuses_unknown_proofRef`), and a card that does not
say already satisfied is not this branch (`repaired_requires_already_card`).

**What I read differently from the packet.**  Under control (b) the verdicts
agree but not for the same reason.  The authored close is a non-injury by the
close (`closeVerdict … false`); the code's `:already-satisfied` record carries
a failure kind, so the close does not decide (`closeVerdict … true = none`)
and the kind's producer-qualified rescue decides
(`control_agrees_by_kind_not_by_close`).  That is why the medic vocabulary
has two non-injury replays and why Part 3 names both.

**Part 3, entry 47 in the medic form.**  `entry47` transcribes ledger entry
47 as `entry45` transcribed entry 45.  `ReplayResult` covers it: the close
alone supplies `successfulCloseNonInjury` (`click3_replay_is_successfulClose`
through `replayFromClose`), and the code's recording of a repaired
already-satisfied close would replay as `producerQualifiedNonInjury` (the a9
form).  `entry47Payload` carries the close's value, as entry 45's does;
`entry47_correction_qualifies` runs it against the ledger as it stands
(entry 45 corrected by the medic operation, entry 47 open: effective
`[2001]`) and the effective active set empties;
`entry47_producer_qualified_also_qualifies` shows the other non-injury value
qualifies under its own binding, so the Clojure packet may name whichever the
replayed classifier produces.  `doneAtBaseRevision` exists by name but is a
refusing value (`meta_medic_authority.clj` `required-findings`: a done-at-base
claim without evidence is an injury); entry 47 had the evidence, and
`entry47_doneAtBase_refuses` is the control.  No constructor is added.

**Numeral key** (transcription, not identities): sha `09a7cb8d…` ↦ 978; the
path `/missions/M-recommendation-bindings.md` ↦ 1; injury `injury/2aef7e0c…`
↦ 2001 (as in claude-9's `observed3.lean`); entry ordinal 47 ↦ 47;
`:injury-predecessor nil` ↦ 0; cause record
`tick-run-record-2026-10-26-f444287e…` ↦ 4442; cause pin `d36c4a64…` ↦ 3644;
entry 45's numerals as in `HistoricalMisclassificationCorrection`; classifier
revision, patch, reviewer, evaluator and evidence pin are placeholders for a
correction envelope that does not exist yet.
-/

namespace DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam

open DarkTower.WarMachine.CloseOutcomeImage (CloseOutcome image closeVerdict Verdict)
open DarkTower.WarMachine.HistoricalMisclassificationCorrection

/-! ## Part 1: the close the grammar names -/

/-- Rule 7's close: a card saying already satisfied, `:proof-ref` the existing
commit, `FULL_LOOP_AUTHOR: REFUSE :already-satisfied-at-base-head`.  The
author reports no failure. -/
def authoredClose : CloseOutcome := .alreadySatisfied

theorem authoredClose_image : image authoredClose = .alreadySatisfied := rfl

/-- The third click's authored close under the law: already satisfied, no
failure, non-injury. -/
theorem click3_law_nonInjury :
    closeVerdict (image authoredClose) false = some .nonInjury := rfl

/-! ## Part 2: the seam as a function -/

abbrev Sha := Nat
abbrev PathId := Nat
abbrev PrNumber := Nat

/-- A ref-like token of the reply text, one per alternative of
`artifact-ref-re` (the two PR alternatives collapsed). -/
inductive Ref where
  | sha (s : Sha)
  | path (p : PathId)
  | prLink (n : PrNumber)
  deriving DecidableEq, Repr

/-- The reply as the Agency reads it: its ref-like tokens in text order. -/
abbrev Reply := List Ref

/-- `first-artifact-ref`: the leftmost match. -/
def firstArtifactRef (reply : Reply) : Option Ref := reply.head?

/-- What the classifier could read from the feature card: whether `:built` or
`:want-coverage` says already satisfied (`already-satisfied-card?`), and
`:proof-ref` read as a commit. -/
structure Card where
  alreadySatisfied : Bool
  proofRef : Option Sha
  deriving DecidableEq, Repr

/-- `commit-exists-in?` over the primary repos: which shas name a commit. -/
abbrev CommitStore := Sha → Bool

/-- The classifier's answers on the already-satisfied branches. -/
inductive Consumed where
  | alreadySatisfied (sha : Sha)
  | invalidAuthorRefusal
  deriving DecidableEq, Repr

def Consumed.close : Consumed → CloseOutcome
  | .alreadySatisfied _ => .alreadySatisfied
  | .invalidAuthorRefusal => .buildFailed

/-- `author-refusal-classification` on a card that says already satisfied,
consuming only the extracted artifact-ref: a sha the store knows is the
grounded commit; a path, a PR link or no ref at all cannot name a commit and
falls to `:invalid-author-refusal`.  `none`: the card does not say already
satisfied, another branch of the `cond`, outside this module. -/
def currentClassifier (store : CommitStore) (card : Card) (ref : Option Ref) :
    Option Consumed :=
  if card.alreadySatisfied then
    some (match ref with
      | some (.sha s) => if store s then .alreadySatisfied s else .invalidAuthorRefusal
      | _ => .invalidAuthorRefusal)
  else none

/-- The repaired consumer: when the extracted ref is not a sha, take the
card's `:proof-ref`; a commit the store does not know is still not evidence. -/
def repairedClassifier (store : CommitStore) (card : Card) (ref : Option Ref) :
    Option Consumed :=
  if card.alreadySatisfied then
    some (match ref, card.proofRef with
      | some (.sha s), _ => if store s then .alreadySatisfied s else .invalidAuthorRefusal
      | _, some s => if store s then .alreadySatisfied s else .invalidAuthorRefusal
      | _, none => .invalidAuthorRefusal)
  else none

/-- The failure kinds the two closes carry. -/
inductive FailureKind where
  | none
  | invalidAuthorRefusal
  | alreadySatisfied
  deriving DecidableEq, Repr

/-- A close as the terminal reads it: outcome and failure kind. -/
structure Close where
  outcome : CloseOutcome
  failure : FailureKind
  deriving DecidableEq, Repr

def failurePresent : FailureKind → Bool
  | .none => false
  | _ => true

/-- `throw-if-author-refused!` 3329–3338: what each classification closes. -/
def recordOf : Consumed → Close
  | .alreadySatisfied _ => ⟨.alreadySatisfied, .alreadySatisfied⟩
  | .invalidAuthorRefusal => ⟨.buildFailed, .invalidAuthorRefusal⟩

/-- The authored close: already satisfied, no failure. -/
def authored : Close := ⟨authoredClose, .none⟩

/-- The kind's verdict when the close does not decide (`classify` 171–173):
`:already-satisfied` is producer-qualified (and in
`explicit-non-injury-kinds`); `:invalid-author-refusal` takes the default
injury branch.  `none` when no kind is present: the cell the close left
undecided is not decided here. -/
def kindVerdict : FailureKind → Option Verdict
  | .alreadySatisfied => some .nonInjury
  | .invalidAuthorRefusal => some .injury
  | .none => none

/-- The terminal reading of a close: the close decides when it does,
otherwise the kind. -/
def verdictOf (c : Close) : Option Verdict :=
  match closeVerdict (image c.outcome) (failurePresent c.failure) with
  | some v => some v
  | none => kindVerdict c.failure

theorem authored_nonInjury : verdictOf authored = some .nonInjury := rfl

/-- The sha the card names exists; nothing else does. -/
def store3 : CommitStore := fun s => s == 978

/-- The third click's card: already satisfied, `:proof-ref` the sha. -/
def card3 : Card := ⟨true, some 978⟩

/-- The reply as sent: the mission path at offset 242, the sha at 291. -/
def witnessReply : Reply := [.path 1, .sha 978]

/-- The same two refs, sha first. -/
def controlReply : Reply := [.sha 978, .path 1]

/-- (a) The witness.  The Agency extracts the path; the classifier consumes it
and answers `invalidAuthorRefusal`; the close is `buildFailed` with that
kind, verdict injury.  The authored close is `alreadySatisfied`, verdict
non-injury. -/
theorem witness_path_before_sha :
    firstArtifactRef witnessReply = some (.path 1) ∧
    currentClassifier store3 card3 (firstArtifactRef witnessReply) =
      some .invalidAuthorRefusal ∧
    recordOf .invalidAuthorRefusal = ⟨.buildFailed, .invalidAuthorRefusal⟩ ∧
    verdictOf (recordOf .invalidAuthorRefusal) = some .injury ∧
    authored.outcome = .alreadySatisfied ∧
    verdictOf authored = some .nonInjury := by decide

/-- The verdicts differ: the consumer renamed a non-injury an injury. -/
theorem witness_verdicts_differ :
    verdictOf (recordOf .invalidAuthorRefusal) ≠ verdictOf authored := by decide

/-- (b) The control.  Sha first: the classifier consumes the sha, the store
knows it, the consumed close is `alreadySatisfied`, and the verdicts agree. -/
theorem control_sha_before_path :
    firstArtifactRef controlReply = some (.sha 978) ∧
    currentClassifier store3 card3 (firstArtifactRef controlReply) =
      some (.alreadySatisfied 978) ∧
    (recordOf (.alreadySatisfied 978)).outcome = authored.outcome ∧
    verdictOf (recordOf (.alreadySatisfied 978)) = verdictOf authored := by decide

/-- Read differently from the packet: under the control the verdicts agree,
but the authored close is a non-injury by the close and the code's record is
a non-injury by its failure kind.  The code's `:already-satisfied` close
carries kind `:already-satisfied`, so the close does not decide. -/
theorem control_agrees_by_kind_not_by_close :
    closeVerdict (image authored.outcome) (failurePresent authored.failure) =
      some .nonInjury ∧
    closeVerdict (image (recordOf (.alreadySatisfied 978)).outcome)
      (failurePresent (recordOf (.alreadySatisfied 978)).failure) = none ∧
    kindVerdict (recordOf (.alreadySatisfied 978)).failure = some .nonInjury := by decide

/-- The two replies are the same refs in the other order, and the current
consumer answers differently. -/
theorem order_alone_decides :
    witnessReply.reverse = controlReply ∧
    currentClassifier store3 card3 (firstArtifactRef witnessReply) ≠
      currentClassifier store3 card3 (firstArtifactRef controlReply) := by decide

/-- The current consumer never reads `:proof-ref`: two cards that agree on
the already-satisfied reading get the same answer whatever their proof-ref. -/
theorem current_ignores_card (store : CommitStore) (c c' : Card) (ref : Option Ref)
    (h : c.alreadySatisfied = c'.alreadySatisfied) :
    currentClassifier store c ref = currentClassifier store c' ref := by
  unfold currentClassifier; rw [h]

/-- (c) The repaired consumer agrees with the authored close on both replies. -/
theorem repaired_agrees_on_both_replies :
    repairedClassifier store3 card3 (firstArtifactRef witnessReply) =
      some (.alreadySatisfied 978) ∧
    repairedClassifier store3 card3 (firstArtifactRef controlReply) =
      some (.alreadySatisfied 978) ∧
    (recordOf (.alreadySatisfied 978)).outcome = authored.outcome ∧
    verdictOf (recordOf (.alreadySatisfied 978)) = verdictOf authored := by decide

/-- In general: when the extracted ref is not a sha and the card names a
commit the store knows, the repaired consumer takes it.  Covers the path, the
PR link and the empty extraction. -/
theorem repaired_takes_card_commit (store : CommitStore) (s : Sha) (ref : Option Ref)
    (hs : store s = true) (hnot : ∀ t, ref ≠ some (.sha t)) :
    repairedClassifier store ⟨true, some s⟩ ref = some (.alreadySatisfied s) := by
  unfold repairedClassifier
  simp only [if_true]
  cases ref with
  | none => simp [hs]
  | some r =>
    cases r with
    | sha t => exact absurd rfl (hnot t)
    | path p => simp [hs]
    | prLink n => simp [hs]

/-- The repaired consumer extends the current one: whatever the current one
grounds, the repaired one grounds the same. -/
theorem repaired_extends_current (store : CommitStore) (card : Card) (ref : Option Ref)
    (s : Sha) (h : currentClassifier store card ref = some (.alreadySatisfied s)) :
    repairedClassifier store card ref = some (.alreadySatisfied s) := by
  unfold currentClassifier at h
  unfold repairedClassifier
  cases ha : card.alreadySatisfied with
  | false => simp [ha] at h
  | true =>
    simp only [ha, if_true, Option.some.injEq] at h ⊢
    cases ref with
    | none => cases h
    | some r =>
      cases r with
      | sha t =>
        cases hs : store t with
        | false => simp [hs] at h
        | true => simp [hs] at h; subst h; simp [hs]
      | path p => cases h
      | prLink n => cases h

/-- Bad case for the repaired consumer: a `:proof-ref` the store does not know
is still not evidence, on the witness reply. -/
theorem repaired_refuses_unknown_proofRef :
    repairedClassifier store3 ⟨true, some 979⟩ (firstArtifactRef witnessReply) =
      some .invalidAuthorRefusal := by decide

/-- Bad case: a card that does not say already satisfied is not this branch,
under either consumer. -/
theorem repaired_requires_already_card :
    repairedClassifier store3 ⟨false, some 978⟩ (firstArtifactRef controlReply) = none ∧
    currentClassifier store3 ⟨false, some 978⟩ (firstArtifactRef controlReply) = none := by
  decide

/-! ## Part 3: entry 47 in the medic form -/

/-- Ledger entry 47, transcribed (key in the header): injury `2aef7e0c…` ↦
2001, ordinal 47, `:injury-predecessor nil` ↦ 0, cause record the RR of run
`f444287e…` ↦ 4442, cause pin `d36c4a64…` ↦ 3644, `:state :open`. -/
def entry47 : InjuryEntry := ⟨2001, 47, 0, 4442, 3644, true⟩

/-- The third click's authored close replays as a successful close. -/
theorem click3_replay_is_successfulClose :
    replayFromClose authoredClose false = some .successfulCloseNonInjury :=
  (successfulClose_replay_iff_law_nonInjury _ _).mpr click3_law_nonInjury

/-- Entry 47's correction, replay taken from the authored close
(`entry47_replay_from_click3_close`).  The other numerals are placeholders. -/
def entry47Payload : MisclassificationPayload :=
  ⟨entry47.occurrence, 0, 4442, 3644, 2410, .successfulCloseNonInjury, 2401, 9, 10, 4701⟩
def entry47Evidence : MisclassificationEvidence :=
  ⟨entry47.occurrence, 0, 4442, 3644, 2410, .successfulCloseNonInjury, 2401, 9, 10, 4701⟩
def admitEntry47 : MisclassificationAdmission := fun current payload evidence =>
  decide (current = entry47 ∧ payload = entry47Payload ∧ evidence = entry47Evidence)

theorem entry47_replay_from_click3_close :
    some entry47Payload.replay = replayFromClose authoredClose false := rfl

/-- The ledger as it stands in the medic form: entry 45 open and corrected by
the medic operation (entry 46), entry 47 open. -/
def ledgerBefore47 : MedicState :=
  ⟨[entry45, entry47], [.historicalMisclassification entry45Payload]⟩

/-- Admission for both corrections. -/
def admitBoth : MisclassificationAdmission := fun current payload evidence =>
  admitEntry45 current payload evidence || admitEntry47 current payload evidence

/-- Before the correction the effective active set is entry 47's injury alone
(the serving readback: raw 2, effective 1).  The correction qualifies under
the exact binding and empties the effective active set; the history is
untouched. -/
def entry47Result : MedicResult :=
  medicProcess admitBoth noGenuine
    (some (.historicalMisclassification entry47Evidence)) ledgerBefore47
    (.historicalMisclassification entry47Payload)

theorem entry47_correction_qualifies :
    medicEffectiveActive ledgerBefore47 = [2001] ∧
    entry47Result.outcome = .appended ∧
    entry47Result.state.history = [entry45, entry47] ∧
    medicEffectiveActive entry47Result.state = [] := by decide

/-- The other non-injury value also qualifies, under its own binding: what the
code's recording of a repaired already-satisfied close (kind
`:already-satisfied`, producer-qualified) would replay to. -/
def entry47ProducerPayload : MisclassificationPayload :=
  { entry47Payload with replay := .producerQualifiedNonInjury }
def entry47ProducerEvidence : MisclassificationEvidence :=
  { entry47Evidence with replay := .producerQualifiedNonInjury }
def admitEntry47Producer : MisclassificationAdmission := fun current payload evidence =>
  decide (current = entry47 ∧ payload = entry47ProducerPayload ∧
    evidence = entry47ProducerEvidence)

theorem entry47_producer_qualified_also_qualifies :
    (medicProcess admitEntry47Producer noGenuine
      (some (.historicalMisclassification entry47ProducerEvidence)) ledgerBefore47
      (.historicalMisclassification entry47ProducerPayload)).outcome = .appended ∧
    medicEffectiveActive (medicProcess admitEntry47Producer noGenuine
      (some (.historicalMisclassification entry47ProducerEvidence)) ledgerBefore47
      (.historicalMisclassification entry47ProducerPayload)).state = [] := by decide

/-- Control: `doneAtBaseRevision` is the value by name, and it refuses, with a
matching binding and a permissive admission.  Entry 47 had the evidence; a
done-at-base claim without it is an injury. -/
theorem entry47_doneAtBase_refuses :
    let payload := { entry47Payload with replay := .doneAtBaseRevision }
    let evidence := { entry47Evidence with replay := .doneAtBaseRevision }
    let permissive : MisclassificationAdmission := fun _ _ _ => true
    (medicProcess permissive noGenuine (some (.historicalMisclassification evidence))
      ledgerBefore47 (.historicalMisclassification payload)).outcome = .refused ∧
    medicEffectiveActive ledgerBefore47 = [2001] := by decide

/-- Control: the correction names one occurrence; a reopening of entry 47's
injury after it is active again. -/
theorem entry47_later_reopening_remains_active :
    let corrected := entry47Result.state
    let reopened := { entry47 with entry := 48, predecessor := 47 }
    medicEffectiveActive { corrected with history := corrected.history ++ [reopened] } =
      [2001] := by decide

#print axioms click3_law_nonInjury
#print axioms authored_nonInjury
#print axioms witness_path_before_sha
#print axioms witness_verdicts_differ
#print axioms control_sha_before_path
#print axioms control_agrees_by_kind_not_by_close
#print axioms order_alone_decides
#print axioms current_ignores_card
#print axioms repaired_agrees_on_both_replies
#print axioms repaired_takes_card_commit
#print axioms repaired_extends_current
#print axioms repaired_refuses_unknown_proofRef
#print axioms repaired_requires_already_card
#print axioms click3_replay_is_successfulClose
#print axioms entry47_replay_from_click3_close
#print axioms entry47_correction_qualifies
#print axioms entry47_producer_qualified_also_qualifies
#print axioms entry47_doneAtBase_refuses
#print axioms entry47_later_reopening_remains_active

end DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam
