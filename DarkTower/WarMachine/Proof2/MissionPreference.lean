import DarkTower.WarMachine.Holes

/-!
# C, the click-time reading rule (C8, registry `:mission-preference`)

PROOF-2a hole H-C. `Holes.PreferenceDistribution` is
`abbrev … := ProbabilityKernel Unit (Outcome Obs)` — the TYPE — and
`MachinePreferenceDistribution.Layer.mission` is the declared-but-empty slot
this row fills; its own docstring says "the mission-grain layer remains
undeclared". The row's `:formal` is a READING RULE, and
`futon2:scripts/futon2/wm/extract_outcomes.clj` runs it. No module stated the
cue table, the exactly-once span check or the typed absences. This one does.

## The three disciplines, from the code's own header (`extract_outcomes.clj:11-26`)

1. **Predeclared cues.** The rule table is fixed before any mission is read and
   every outcome names the rule that found it, because "a cue table tuned per
   mission would make the extractor a transcription of its author's reading".
   `CueTable` is therefore DATA, a parameter, never derived from the text.
2. **Verified spans.** Every quote must occur EXACTLY ONCE in the file and at
   the line range reported, and "one failure refuses the whole output: a C whose
   cues are half-checked is worse than none, because the half that resolve make
   the rest look checked". `duplicateQuoteRefusesAll` is that sentence as a
   theorem — one bad cue takes every outcome with it, including the ones that
   verified.
3. **Typed absence, never a substituted value.** No outcome found is
   `{:absent :no-stated-outcome}` naming every section read; an instance with no
   cascade is `{:absent :no-cascade}`; and an unstated weighting is
   `{:absent :unstated}`, **not a uniform prior**.

## What C is with no stated weighting: an ABSENCE, not a uniform prior

`extract_outcomes.clj:921-922` emits
`:weighting {:absent :unstated :note "no line assigns a magnitude or compares
two outcomes"}`, and the row's `:formal` says "never a uniform prior".
`missionPreference` therefore REFUSES: `unstatedWeightingIsNotUniform` shows the
ok arm is unreachable without a stated weighting, so `Layer.mission` stays
unfilled rather than being filled with a guess.

This is the OPPOSITE ruling from `:enactment-habit`'s (C4), where E with no data
IS uniform, through the Dirichlet `α = 1` that `cascade_prior` applies. Both are
on the record and they disagree on purpose: a habit prior smooths counts it has
a model for, and a preference read from text has no model for outcomes the text
does not rank.

## Pinned to the text

Spans are code-point offsets into one text, so a proposal carrying a different
`sha256` is refused FIRST (`verify-proposed-link`'s `:text-mismatch`, "spans are
meaningless elsewhere"). `spansAreMeaninglessElsewhere` is that refusal;
`readOutcomes_pinnedToText` is the determinism it protects.

## What this module does not claim

Nothing about which regexes the cue rules are (the table is a parameter here,
as it is data there), about the served-by direction-verb vocabulary or the
`:coreference :reader-claimed` two-string form, about `:no-shared-artefact`, or
about the reference comparison. And nothing about where a weighting would come
from — the point of the row is that today none is stated.
-/

namespace DarkTower.WarMachine.Proof2.MissionPreference

open DarkTower.WarMachine.Holes

/-! ## The text and its spans -/

/-- A code-point span, the unit every `:via` span uses. -/
structure Span where
  start : ℕ
  stop : ℕ
  deriving DecidableEq

/-- The mission text as a value, with the sha256 its spans are pinned to. -/
structure Text where
  content : List Char
  sha256 : String

/-- The characters a span names. -/
def Text.spanText (t : Text) (s : Span) : List Char :=
  (t.content.drop s.start).take (s.stop - s.start)

/-- The line a code-point index falls on: newlines before it. -/
def Text.lineOf (t : Text) (i : ℕ) : ℕ := ((t.content.take i).filter (· = '\n')).length

/-- How many times a quote occurs in a character list. -/
def countOcc (q : List Char) : List Char → ℕ
  | [] => 0
  | (c :: rest) => (if q.isPrefixOf (c :: rest) then 1 else 0) + countOcc q rest

/-- The index of the first occurrence, if any. -/
def firstIndexOf (q : List Char) : List Char → Option ℕ
  | [] => none
  | (c :: rest) => if q.isPrefixOf (c :: rest) then some 0 else (firstIndexOf q rest).map (· + 1)

/-! ## The predeclared cue table, and what a reading is -/

/-- **Discipline 1.** The cue table is DATA, fixed before any mission is read.
It is a parameter of `readOutcomes` and is never derived from the text. -/
structure CueTable where
  /-- The rule id beside the quote it looks for, so every outcome names the rule
  that found it. -/
  rules : List (String × List Char)

/-- One outcome, cued to the span it came from and naming its rule. -/
structure CuedOutcome where
  rule : String
  quote : List Char
  span : Span
  claimedLine : ℕ
  deriving DecidableEq

/-- Why a reading produced no C. Each arm NAMES what is missing. -/
inductive ReadAbsence where
  /-- **Discipline 2.** One or more cues do not resolve exactly once at the line
  and span they claim. Carries every failing rule, and refuses the WHOLE output. -/
  | cueDoesNotResolve (rules : List String)
  /-- No cue matched: the typed absence, naming every section read. -/
  | noStatedOutcome (sectionsRead : List String)
  /-- An instance with no cascade — not an empty want list. -/
  | noCascade (instanceName : String)
  /-- The proposal's spans belong to a different text. -/
  | textMismatch (proposed actual : String)
  /-- **The one this row is about.** No line assigns a magnitude or compares two
  outcomes, so there is no weighting — and no uniform prior standing in for one. -/
  | unstatedWeighting
  deriving DecidableEq

/-! ## Reading -/

/-- A cue resolves when its quote occurs EXACTLY ONCE, at the line it claims,
and at the code-point span it claims — `extract_outcomes.clj`'s `verify`, whose
three conjuncts these are. -/
def cueResolves (t : Text) (o : CuedOutcome) : Bool :=
  (countOcc o.quote t.content == 1) &&
  (match firstIndexOf o.quote t.content with
   | some i => t.lineOf i == o.claimedLine
   | none => false) &&
  (t.spanText o.span == o.quote)

/-- The outcome a rule yields at its single occurrence, if it has one. -/
def outcomeOf (t : Text) (rule : String) (q : List Char) : Option CuedOutcome :=
  match firstIndexOf q t.content with
  | none => none
  | some i => some ⟨rule, q, ⟨i, i + q.length⟩, t.lineOf i, ⟩

/-- **The reading.** Every rule whose quote occurs at all yields an outcome cued
to its span; if ANY of those fails to resolve exactly once the whole output
refuses; and if none matched, the typed absence naming every section read. -/
def readOutcomes (cues : CueTable) (t : Text) (sectionsRead : List String) :
    Except ReadAbsence (List CuedOutcome) :=
  let found := cues.rules.filterMap fun r => outcomeOf t r.1 r.2
  let bad := found.filter fun o => !cueResolves t o
  if bad ≠ [] then .error (.cueDoesNotResolve (bad.map CuedOutcome.rule))
  else if found = [] then .error (.noStatedOutcome sectionsRead)
  else .ok found

/-- **`readOutcomes_pinnedToText`.** The reading is a function of the text: the
same text gives the same reading, which is what the sha256 pin protects. -/
theorem readOutcomes_pinnedToText (cues : CueTable) (t u : Text) (sections : List String)
    (h : t.content = u.content) :
    readOutcomes cues t sections = readOutcomes cues u sections := by
  have : t = u ∨ t.content = u.content := Or.inr h
  unfold readOutcomes outcomeOf cueResolves Text.spanText Text.lineOf
  rw [h]

/-- And the pin itself: a proposal whose sha is not this text's is refused
first, because its spans name positions in some other document. -/
def checkTextPin (t : Text) (proposedSha : String) : Except ReadAbsence Unit :=
  if proposedSha = t.sha256 then .ok () else .error (.textMismatch proposedSha t.sha256)

theorem spansAreMeaninglessElsewhere (t : Text) (s : String) (h : s ≠ t.sha256) :
    checkTextPin t s = .error (.textMismatch s t.sha256) := by
  simp [checkTextPin, h]

/-! ## The distribution, and the absence where one would be -/

/-- A weighting the TEXT states: a normalised mass over the outcomes read. The
row's point is that no mission states one. -/
structure StatedWeighting (Obs : Vertex → Type*) where
  support : List (Outcome Obs)
  mass : Outcome Obs → ℝ
  nonneg : ∀ o, 0 ≤ mass o
  normalised : (support.map mass).sum = 1
  nodup : support.Nodup
  zero_off : ∀ o, o ∉ support → mass o = 0

/-- A completed reading: the outcomes, and whatever weighting the text stated. -/
structure Reading (Obs : Vertex → Type*) where
  outcomes : List CuedOutcome
  weighting : Option (StatedWeighting Obs)

/-- **C as a preference distribution**, or the typed absence. With a stated
weighting this IS `Holes.PreferenceDistribution`; with none it refuses. -/
def missionPreference {Obs : Vertex → Type*} (r : Reading Obs) :
    Except ReadAbsence (PreferenceDistribution Obs) :=
  match r.weighting with
  | none => .error .unstatedWeighting
  | some w =>
      .ok { support := fun _ => w.support
            mass := fun _ => w.mass
            nonnegative := fun _ => w.nonneg
            normalised := fun _ => w.normalised
            support_nodup := fun _ => w.nodup
            mass_eq_zero_of_not_mem := fun _ o h => w.zero_off o h }

/-- **`unstatedWeightingIsNotUniform`.** With no stated weighting there is no
distribution at all — not a uniform one over the outcomes read. The ok arm is
unreachable, so nothing downstream can mistake a guess for a reading. -/
theorem unstatedWeightingIsNotUniform {Obs : Vertex → Type*} (r : Reading Obs)
    (h : r.weighting = none) :
    missionPreference r = .error .unstatedWeighting ∧
    ∀ C, missionPreference r ≠ .ok C := by
  refine ⟨by simp [missionPreference, h], fun C hc => ?_⟩
  rw [missionPreference, h] at hc
  exact absurd hc (by simp)

/-- The ok arm is not vacuous: with a stated weighting the result IS that
weighting's kernel. The absence above is a fact about missions, not about the
definition. -/
theorem missionPreference_ok {Obs : Vertex → Type*} (r : Reading Obs)
    (w : StatedWeighting Obs) (h : r.weighting = some w) :
    ∃ C : PreferenceDistribution Obs, missionPreference r = .ok C ∧
      (∀ u, C.support u = w.support) ∧ (∀ u, C.mass u = w.mass) := by
  refine ⟨{ support := fun _ => w.support
            mass := fun _ => w.mass
            nonnegative := fun _ => w.nonneg
            normalised := fun _ => w.normalised
            support_nodup := fun _ => w.nodup
            mass_eq_zero_of_not_mem := fun _ o hh => w.zero_off o hh },
          by simp [missionPreference, h], fun _ => rfl, fun _ => rfl⟩

/-- **The `Layer.mission` slot**: filled by `missionPreference` on the ok arm,
and absent otherwise. This is the declared-but-empty slot
`MachinePreferenceDistribution.Layer.mission` names. -/
def missionLayer {Obs : Vertex → Type*} (r : Reading Obs) :
    Except ReadAbsence (PreferenceDistribution Obs) := missionPreference r

theorem missionLayer_absent_of_unstatedWeighting {Obs : Vertex → Type*} (r : Reading Obs)
    (h : r.weighting = none) : missionLayer r = .error .unstatedWeighting :=
  (unstatedWeightingIsNotUniform r h).1

/-! ## The bad cases -/

section BadCases

/-- A text in which "alpha" occurs ONCE and "beta" occurs TWICE. -/
def twoCueText : Text :=
  ⟨"alpha\nbeta\nbeta\n".toList, "sha-of-this-text"⟩

def goodRule : String × List Char := ("R1", "alpha".toList)
def dupRule : String × List Char := ("R2", "beta".toList)

/-- **`duplicateQuoteRefusesAll`.** The cue that occurs twice refuses the WHOLE
output — the outcome cued by "alpha", which resolves perfectly, is not returned
either. This is `extract_outcomes.clj`'s "a C whose cues are half-checked is
worse than none, because the half that resolve make the rest look checked". -/
theorem duplicateQuoteRefusesAll :
    readOutcomes ⟨[goodRule, dupRule]⟩ twoCueText ["§1"] = .error (.cueDoesNotResolve ["R2"]) := by
  decide

/-- And the good cue alone DOES read, so the refusal above is caused by the
duplicate and not by the reader failing on everything. -/
theorem goodCueAloneReads :
    (readOutcomes ⟨[goodRule]⟩ twoCueText ["§1"]).isOk = true := by
  decide

/-- **`noCueNoOutcome`.** A text no cue matches gives the typed absence naming
every section read — not an empty preference, which would read as "the mission
states that nothing matters". -/
theorem noCueNoOutcome :
    readOutcomes ⟨[("R3", "gamma".toList)]⟩ twoCueText ["§1", "§2"]
      = .error (.noStatedOutcome ["§1", "§2"]) := by
  decide

end BadCases

#print axioms Span
#print axioms Text
#print axioms countOcc
#print axioms firstIndexOf
#print axioms CueTable
#print axioms CuedOutcome
#print axioms ReadAbsence
#print axioms cueResolves
#print axioms outcomeOf
#print axioms readOutcomes
#print axioms readOutcomes_pinnedToText
#print axioms checkTextPin
#print axioms spansAreMeaninglessElsewhere
#print axioms StatedWeighting
#print axioms Reading
#print axioms missionPreference
#print axioms unstatedWeightingIsNotUniform
#print axioms missionPreference_ok
#print axioms missionLayer
#print axioms missionLayer_absent_of_unstatedWeighting
#print axioms duplicateQuoteRefusesAll
#print axioms goodCueAloneReads
#print axioms noCueNoOutcome

end DarkTower.WarMachine.Proof2.MissionPreference
