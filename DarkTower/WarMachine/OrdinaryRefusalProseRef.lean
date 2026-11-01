import DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam

/-!
# A typed refusal that mentions a commit is still a refusal (L5-25)

Source: click `wm-click-8ed79a0b…`, run `2026-11-01-0e6ff636…` (claude-2,
2026-11-01).  Lean first; the Clojure classifier and the terminal classifier
conform in the same packet.  Additions only, beside
`AlreadySatisfiedArtifactRefSeam` (whose `Ref`, `Reply`, `Card` and
`preferredArtifactRef` this module reuses).

**What happened.**  Ordinary selection chose M-interim-director.  The author
(wm-author on Zai, job `invoke-1793571759556-9840-92c617ea`) inspected the
mission, found every remaining C4 want to be an operator decision or an
operator-only input, and answered in the author prompt's own grammar: a
feature card `{:built "no parcel — all four C4 wants are operator-gated …"
:want-coverage "0/4" …}` with no `:proof-ref`, and the last line
`FULL_LOOP_AUTHOR: REFUSE :wants-operator-gated-no-honest-parcel (…)`.  Its
inspection findings named the mission file it read and the base HEAD it read
it at, futon7 `51af00b44628945adca1fb15f97c92ca878c279d`.

Two consumers then turned the author's answer into an apparatus injury:

1. `author-refusal-classification` (futon2 `full_loop_runner.clj`, 3648–3738
   at `9f19351f8`): its guardrail branch is `(and (not (str/blank? reason))
   (nil? artifact-ref))`.  The Agency's `first-artifact-ref` (futon3c
   `transport/http.clj`, the preferred form of `6b1bb1358`) extracts the
   full sha from the reply text, so `artifact-ref` is `51af00b…` and the
   typed refusal falls to `:invalid-author-refusal`, closed `:build-failed`.
   The classifier's own comment on the already-satisfied branch says the
   extracted ref "is prose-first text, not the author's typed claim"; the
   guardrail branch read it as a claim anyway.
2. `meta_terminal_injury.clj` `classify` (255–300): the kind table
   `explicit-non-injury-kinds` has no `:guardrail-refusal`, so even the
   correct close, kind `:guardrail-refusal`, takes the default injury branch.
   Replayed on 2026-11-01 over the reconstructed click-2 close and over the
   retained record `tick-run-record-2026-09-30-1790748841` (a plain typed
   refusal): both `:injury`.  The table's own comment (lines 23–26) says "the
   attempt closes :guardrail-refusal and there is nothing to repair".

Result: ledger entry 152 (`injury/d984347f…`, `:invalid-author-refusal` at
`:author-wait`), one self-heal author attempt refused by the provider (HTTP
429, monthly limit), the one-attempt cap, and clicks 3 and 4 refused before
ordinary selection.

**Part 1, the guardrail branch as a function.**  `Refusal` is what the
branch can read: whether the REFUSE line carries a reason, the card, and the
Agency-extracted ref.  `currentGuardrail` is the deployed branch;
`repairedGuardrail` reads the author's typed claim, the card's `:proof-ref`,
instead of the extracted ref.  The already-satisfied card stays the seam's
branch (`.alreadyBranch`) and is out of scope here.

**Part 2, the terminal's kind verdict.**  `currentKindVerdict` transcribes
the kind table; `repairedKindVerdict` adds `guardrailRefusal ↦ nonInjury`.
`verdictOf` is the seam's reading: the close decides when
`CloseOutcomeImage.closeVerdict` does (`image .guardrailRefusal = .refused`,
on which it never does), else the kind.

Theorems: the witness under both deployed consumers is an injury; mention of any ref-like token
alone decides under the deployed branch (`mention_alone_decides`); the
classifier repair alone leaves it an injury (`classifier_alone_not_enough`);
both repairs make it a non-injury; the repaired branch extends the current
one wherever the card lies in the reply; a card that names a `:proof-ref`
while refusing is still contradictory; a REFUSE without a reason is still
invalid; a build failure is still an injury under the repaired table.

**Numeral key** (transcription, not identities): futon7 `51af00b…` ↦ 5100;
`/M-interim-director-forward-model.edn` (reply offset 264) ↦ 1;
`/home/joe/code/futon7/holes/M-interim-director.md` (offset 742) ↦ 2; the
sha is at offset 807.
-/

namespace DarkTower.WarMachine.OrdinaryRefusalProseRef

open DarkTower.WarMachine.CloseOutcomeImage (CloseOutcome image closeVerdict Verdict)
open DarkTower.WarMachine.AlreadySatisfiedArtifactRefSeam
  (Ref Reply Card Sha preferredArtifactRef firstArtifactRef)

/-! ## Part 1: the guardrail branch -/

/-- What `author-refusal-classification`'s guardrail branch can read. -/
structure Refusal where
  /-- `FULL_LOOP_AUTHOR: REFUSE <reason>` with a non-blank reason. -/
  typedReason : Bool
  card : Card
  /-- The Agency-extracted artifact-ref. -/
  extracted : Option Ref
  deriving DecidableEq, Repr

inductive Consumed where
  /-- The card says already satisfied: the seam's branch, not this module's. -/
  | alreadyBranch
  | guardrailRefusal
  | invalidAuthorRefusal
  deriving DecidableEq, Repr

/-- The deployed branch: a reason and NO extracted ref. -/
def currentGuardrail (r : Refusal) : Consumed :=
  if r.card.alreadySatisfied then .alreadyBranch
  else if r.typedReason && r.extracted.isNone then .guardrailRefusal
  else .invalidAuthorRefusal

/-- The repaired branch: a reason and no `:proof-ref` on the card.  The
extracted ref is prose. -/
def repairedGuardrail (r : Refusal) : Consumed :=
  if r.card.alreadySatisfied then .alreadyBranch
  else if r.typedReason && r.card.proofRef.isNone then .guardrailRefusal
  else .invalidAuthorRefusal

/-- The sha the author mentioned exists in futon7; the full form. -/
def full2 : Sha → Bool := fun s => s == 5100

/-- Click 2's reply as sent: two paths, then the base-HEAD sha. -/
def click2Reply : Reply := [.path 1, .path 2, .sha 5100]

/-- Click 2's card: not already satisfied, no `:proof-ref`. -/
def click2Card : Card := ⟨false, none⟩

/-- The Agency extracts the full sha, whatever precedes it. -/
theorem click2_extracts_sha :
    preferredArtifactRef full2 click2Reply = some (.sha 5100) := by decide

def click2 : Refusal := ⟨true, click2Card, preferredArtifactRef full2 click2Reply⟩

theorem click2_current_invalid : currentGuardrail click2 = .invalidAuthorRefusal := by decide
theorem click2_repaired_guardrail : repairedGuardrail click2 = .guardrailRefusal := by decide
theorem click2_consumers_differ : currentGuardrail click2 ≠ repairedGuardrail click2 := by decide

/-- The same answer with no ref-like token in the prose is a guardrail
refusal under the deployed branch; the same answer naming only the mission
file it read (a path, no sha) is already invalid.  Mention alone decides:
an author who says which file it inspected condemns its own refusal. -/
theorem mention_alone_decides :
    currentGuardrail ⟨true, click2Card, preferredArtifactRef full2 []⟩ = .guardrailRefusal ∧
    currentGuardrail ⟨true, click2Card, preferredArtifactRef full2 [.path 1, .path 2]⟩ =
      .invalidAuthorRefusal ∧
    repairedGuardrail ⟨true, click2Card, preferredArtifactRef full2 []⟩ = .guardrailRefusal ∧
    repairedGuardrail ⟨true, click2Card, preferredArtifactRef full2 [.path 1, .path 2]⟩ =
      .guardrailRefusal := by decide

/-- Control: a REFUSE whose card names a `:proof-ref` is contradictory under
both consumers.  The card lies in the reply, so the Agency extracts its sha. -/
theorem proof_ref_while_refusing_invalid (s : Sha) :
    currentGuardrail ⟨true, ⟨false, some s⟩, some (.sha s)⟩ = .invalidAuthorRefusal ∧
    repairedGuardrail ⟨true, ⟨false, some s⟩, some (.sha s)⟩ = .invalidAuthorRefusal := by
  constructor <;> simp [currentGuardrail, repairedGuardrail]

/-- Control: a REFUSE without a reason is invalid under both, with or
without an extracted ref. -/
theorem no_reason_invalid (card : Card) (ref : Option Ref) (h : card.alreadySatisfied = false) :
    currentGuardrail ⟨false, card, ref⟩ = .invalidAuthorRefusal ∧
    repairedGuardrail ⟨false, card, ref⟩ = .invalidAuthorRefusal := by
  constructor <;> simp [currentGuardrail, repairedGuardrail, h]

/-- The already-satisfied card is untouched: both consumers hand it to the
seam's branch. -/
theorem already_card_untouched (reason : Bool) (p : Option Sha) (ref : Option Ref) :
    currentGuardrail ⟨reason, ⟨true, p⟩, ref⟩ = .alreadyBranch ∧
    repairedGuardrail ⟨reason, ⟨true, p⟩, ref⟩ = .alreadyBranch := by
  constructor <;> simp [currentGuardrail, repairedGuardrail]

/-- The repaired branch extends the current one wherever the card lies in the
reply (a `:proof-ref` on the card is a sha in the text, so the extraction is
not empty): whatever the current branch calls a guardrail refusal, the
repaired branch does too. -/
theorem repaired_extends_current (r : Refusal)
    (hcard : ∀ s, r.card.proofRef = some s → r.extracted ≠ none)
    (h : currentGuardrail r = .guardrailRefusal) :
    repairedGuardrail r = .guardrailRefusal := by
  unfold currentGuardrail at h
  unfold repairedGuardrail
  cases ha : r.card.alreadySatisfied with
  | true => simp [ha] at h
  | false =>
    simp only [ha] at h ⊢
    cases hr : r.typedReason with
    | false => simp [hr] at h
    | true =>
      simp only [hr, Bool.true_and] at h ⊢
      cases he : r.extracted with
      | some x => simp [he] at h
      | none =>
        cases hp : r.card.proofRef with
        | none => simp
        | some s => exact absurd he (hcard s hp)

/-! ## Part 2: the terminal's kind verdict -/

/-- The failure kinds the two closes carry, plus the guardrail refusal. -/
inductive Kind where
  | none
  | invalidAuthorRefusal
  | alreadySatisfied
  | guardrailRefusal
  deriving DecidableEq, Repr

def failurePresent : Kind → Bool
  | .none => false
  | _ => true

/-- `meta_terminal_injury.clj` `classify` at futon2 `9f19351f8`:
`:already-satisfied` is producer-qualified, `:guardrail-refusal` is not in
`explicit-non-injury-kinds` and takes the default injury branch with
`:invalid-author-refusal`. -/
def currentKindVerdict : Kind → Option Verdict
  | .alreadySatisfied => some .nonInjury
  | .invalidAuthorRefusal => some .injury
  | .guardrailRefusal => some .injury
  | .none => none

/-- The repaired table: a typed refusal is the author's answer, not the
apparatus (the kinds table's own comment, lines 23–26). -/
def repairedKindVerdict : Kind → Option Verdict
  | .alreadySatisfied => some .nonInjury
  | .invalidAuthorRefusal => some .injury
  | .guardrailRefusal => some .nonInjury
  | .none => none

/-- A close as the terminal reads it: outcome and failure kind. -/
structure Close where
  outcome : CloseOutcome
  kind : Kind
  deriving DecidableEq, Repr

/-- `throw-if-author-refused!`: what each classification closes. -/
def recordOf : Consumed → Close
  | .guardrailRefusal => ⟨.guardrailRefusal, .guardrailRefusal⟩
  | .invalidAuthorRefusal => ⟨.buildFailed, .invalidAuthorRefusal⟩
  | .alreadyBranch => ⟨.alreadySatisfied, .alreadySatisfied⟩

/-- The terminal reading under a kind table: the close decides when it does,
otherwise the kind. -/
def verdictOf (kv : Kind → Option Verdict) (c : Close) : Option Verdict :=
  match closeVerdict (image c.outcome) (failurePresent c.kind) with
  | some v => some v
  | none => kv c.kind

/-- The refused image never decides: the kind table does. -/
theorem guardrail_close_decided_by_kind (kv : Kind → Option Verdict) :
    verdictOf kv ⟨.guardrailRefusal, .guardrailRefusal⟩ = kv .guardrailRefusal := rfl

/-- (a) The witness as consumed and recorded: an injury. -/
theorem click2_consumed_injury :
    verdictOf currentKindVerdict (recordOf (currentGuardrail click2)) = some .injury := by decide

/-- (b) The classifier repair alone is not enough: the correct close is still
an injury under the deployed kind table.  This is also the September record
`tick-run-record-2026-09-30-1790748841` (kind `:guardrail-refusal`, replayed
`:injury` on 2026-11-01). -/
theorem classifier_alone_not_enough :
    verdictOf currentKindVerdict (recordOf (repairedGuardrail click2)) = some .injury := by decide

/-- (c) Both repairs: the author's answer is a non-injury. -/
theorem both_repairs_nonInjury :
    verdictOf repairedKindVerdict (recordOf (repairedGuardrail click2)) = some .nonInjury := by
  decide

/-- The repaired table extends the current one: whatever was a non-injury
stays one. -/
theorem repaired_kind_extends_current (k : Kind)
    (h : currentKindVerdict k = some .nonInjury) : repairedKindVerdict k = some .nonInjury := by
  cases k <;> simp_all [currentKindVerdict, repairedKindVerdict]

/-- A build failure is still an injury under both tables. -/
theorem buildFailed_still_injury :
    verdictOf currentKindVerdict (recordOf .invalidAuthorRefusal) = some .injury ∧
    verdictOf repairedKindVerdict (recordOf .invalidAuthorRefusal) = some .injury := by decide

/-- The already-satisfied close is a non-injury under both tables. -/
theorem already_still_nonInjury :
    verdictOf currentKindVerdict (recordOf .alreadyBranch) = some .nonInjury ∧
    verdictOf repairedKindVerdict (recordOf .alreadyBranch) = some .nonInjury := by decide

#print axioms click2_extracts_sha
#print axioms click2_current_invalid
#print axioms click2_repaired_guardrail
#print axioms click2_consumers_differ
#print axioms mention_alone_decides
#print axioms proof_ref_while_refusing_invalid
#print axioms no_reason_invalid
#print axioms already_card_untouched
#print axioms repaired_extends_current
#print axioms guardrail_close_decided_by_kind
#print axioms click2_consumed_injury
#print axioms classifier_alone_not_enough
#print axioms both_repairs_nonInjury
#print axioms repaired_kind_extends_current
#print axioms buildFailed_still_injury
#print axioms already_still_nonInjury

end DarkTower.WarMachine.OrdinaryRefusalProseRef
