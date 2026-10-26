import DarkTower.WarMachine.PatternTheta

/-!
# Supplied pattern-observation admission

This module makes explicit the conditional boundary already required by
`PatternTheta`: a caller supplies an authority decision for a guard-held fire,
and only a matching, observed Boolean may become an existing
`R15TemporalHierarchy.FastOutcome`. It does not derive authority from selection,
prediction mass, a mission-hole observation, or the existence of an effect.

The arithmetic remains the model in `PatternTheta`. Its source discussion cites
`refs/friston2017.txt:352` (`Q(B) = Dir(b)`) and da Costa 2020 Appendix A.1 for
transition Dirichlet counts. Those sources motivate the count update; they do
not establish this domain-specific authority premise. The predicate and its
checker are therefore supplied parameters here.

Occurrence/effect/revision identify the admitted event. The `pattern` is the
separate parameter key: different admitted occurrences with the same pattern
continue to pool exactly as `PatternTheta.witnessedOutcomes` already specifies.
An observed `false` is distinct from absence and is admitted as failure only
when authority accepts it. Zero prediction mass is deliberately not an input
or a gate.
-/

namespace DarkTower.WarMachine.PatternObservationAdmission

open R15TemporalHierarchy

/-- The requested event binding. `pattern` is the shared theta parameter key;
the remaining fields identify this event. -/
structure Request (PatternKey Occurrence Effect Revision : Type) where
  pattern : PatternKey
  occurrence : Occurrence
  effect : Effect
  revision : Revision
  deriving DecidableEq, Repr

/-- A supplied observation keeps absence distinct from an observed `false`.
Authority evidence is also optional and independent of the Boolean payload. -/
structure SuppliedObservation (PatternKey Occurrence Effect Revision Evidence : Type) where
  pattern : PatternKey
  occurrence : Occurrence
  effect : Effect
  revision : Revision
  observed : Option Bool
  authorityEvidence : Option Evidence
  deriving DecidableEq, Repr

/-- A domain-supplied authority predicate plus an executable checker proved to
decide exactly that predicate. This wrapper chooses no authority semantics. -/
structure AuthorityCheck (Evidence PatternKey Occurrence Effect Revision : Type) where
  Admits : Evidence → Request PatternKey Occurrence Effect Revision → Bool → Prop
  check : Evidence → Request PatternKey Occurrence Effect Revision → Bool → Bool
  check_iff : ∀ e r outcome, check e r outcome = true ↔ Admits e r outcome

variable {PatternKey Occurrence Effect Revision Evidence : Type}
  [DecidableEq PatternKey] [DecidableEq Occurrence] [DecidableEq Effect]
  [DecidableEq Revision]

/-- Project one supplied observation only when every event binding matches, a
Boolean is present, evidence is present, and the supplied authority accepts. -/
def project (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence) :
    Option (FastOutcome PatternKey) :=
  if observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision then
    match observation.observed, observation.authorityEvidence with
    | some succeeded, some evidence =>
        if gate.check evidence requested succeeded then
          some ⟨requested.pattern, true, succeeded⟩
        else none
    | _, _ => none
  else none

theorem project_of_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (succeeded : Bool) (evidence : Evidence)
    (hadmitted : gate.Admits evidence requested succeeded) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ =
      some ⟨requested.pattern, true, succeeded⟩ := by
  simp [project, (gate.check_iff evidence requested succeeded).2 hadmitted]

/-- Every emitted event recovers the matching identity, the actual supplied
Boolean, and authority for that same Boolean. -/
theorem project_eq_some_only_if
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (event : FastOutcome PatternKey)
    (hproject : project gate requested observation = some event) :
    observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision ∧
      ∃ evidence,
        observation.observed = some event.succeeded ∧
        observation.authorityEvidence = some evidence ∧
        gate.Admits evidence requested event.succeeded ∧
        event.policy = requested.pattern ∧ event.witnessed = true := by
  unfold project at hproject
  by_cases hbinding : observation.pattern = requested.pattern ∧
      observation.occurrence = requested.occurrence ∧
      observation.effect = requested.effect ∧
      observation.revision = requested.revision
  · have hb := hbinding
    obtain ⟨hp, ho, he, hr⟩ := hbinding
    cases hobserved : observation.observed with
    | none => simp [hb, hobserved] at hproject
    | some succeeded =>
      cases hevidence : observation.authorityEvidence with
      | none => simp [hb, hobserved, hevidence] at hproject
      | some evidence =>
        by_cases hcheck : gate.check evidence requested succeeded = true
        · simp [hb, hobserved, hevidence, hcheck] at hproject
          have hevent : (⟨requested.pattern, true, succeeded⟩ : FastOutcome PatternKey) = event :=
            hproject
          rw [← hevent]
          exact ⟨hp, ho, he, hr, evidence, rfl, rfl,
            (gate.check_iff evidence requested succeeded).1 hcheck, rfl, rfl⟩
        · simp [hb, hobserved, hevidence, hcheck] at hproject
  · simp [hbinding] at hproject

theorem missing_observation_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.observed = none) :
    project gate requested observation = none := by
  simp [project, h]

theorem missing_authority_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.authorityEvidence = none) :
    project gate requested observation = none := by
  simp [project, h]

theorem unqualified_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (succeeded : Bool) (evidence : Evidence)
    (hrejected : ¬ gate.Admits evidence requested succeeded) :
    project gate requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some succeeded, some evidence⟩ = none := by
  have hcheck : gate.check evidence requested succeeded = false := by
    cases h : gate.check evidence requested succeeded
    · rfl
    · exact False.elim (hrejected ((gate.check_iff evidence requested succeeded).1 h))
  simp [project, hcheck]

theorem occurrence_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.occurrence ≠ requested.occurrence) :
    project gate requested observation = none := by
  simp [project, h]

theorem effect_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.effect ≠ requested.effect) :
    project gate requested observation = none := by
  simp [project, h]

theorem revision_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.revision ≠ requested.revision) :
    project gate requested observation = none := by
  simp [project, h]

theorem pattern_mismatch_not_admitted
    (gate : AuthorityCheck Evidence PatternKey Occurrence Effect Revision)
    (requested : Request PatternKey Occurrence Effect Revision)
    (observation : SuppliedObservation PatternKey Occurrence Effect Revision Evidence)
    (h : observation.pattern ≠ requested.pattern) :
    project gate requested observation = none := by
  simp [project, h]

/-! ## Synthetic controls: these instantiate a caller premise, not runtime authority. -/

inductive Pattern where | shared | other deriving DecidableEq, Repr
inductive EffectKind where | emitted | other deriving DecidableEq, Repr

structure ControlEvidence where
  occurrence : Nat
  effect : EffectKind
  revision : Nat
  outcome : Bool
  deriving DecidableEq, Repr

def controlGate : AuthorityCheck ControlEvidence Pattern Nat EffectKind Nat where
  Admits evidence request outcome :=
    evidence.occurrence = request.occurrence ∧
    evidence.effect = request.effect ∧
    evidence.revision = request.revision ∧
    evidence.outcome = outcome
  check evidence request outcome := decide
    (evidence.occurrence = request.occurrence ∧
     evidence.effect = request.effect ∧
     evidence.revision = request.revision ∧
     evidence.outcome = outcome)
  check_iff _ _ _ := by simp

def requested : Request Pattern Nat EffectKind Nat := ⟨.shared, 19, .emitted, 7⟩

def requestedAt (occurrence : Nat) : Request Pattern Nat EffectKind Nat :=
  ⟨.shared, occurrence, .emitted, 7⟩

def evidence (occurrence : Nat) (outcome : Bool) : ControlEvidence :=
  ⟨occurrence, .emitted, 7, outcome⟩

def supplied (occurrence : Nat) (observed : Option Bool)
    (authority : Option ControlEvidence) :
    SuppliedObservation Pattern Nat EffectKind Nat ControlEvidence :=
  ⟨.shared, occurrence, .emitted, 7, observed, authority⟩

theorem admitted_success_exact :
    project controlGate requested (supplied 19 (some true) (some (evidence 19 true))) =
      some ⟨.shared, true, true⟩ := by decide

theorem admitted_failure_exact :
    project controlGate requested (supplied 19 (some false) (some (evidence 19 false))) =
      some ⟨.shared, true, false⟩ := by decide

theorem flipped_payload_is_rejected :
    project controlGate requested (supplied 19 (some false) (some (evidence 19 true))) = none := by
  decide

theorem selected_without_authority_is_absent :
    project controlGate requested (supplied 19 (some true) none) = none := by decide

theorem occurrence_zero_cannot_relabel_as_nineteen :
    project controlGate requested (supplied 0 (some true) (some (evidence 0 true))) = none := by
  decide

/-- An authority-admitted false reaches the existing failure arithmetic. -/
theorem witnessed_false_reaches_failure_update :
    let before : SlowState Pattern := [(.shared, ⟨2, 3⟩)]
    Option.map (fun event => countsFor (advance before event) .shared)
      (project controlGate requested
        (supplied 19 (some false) (some (evidence 19 false)))) = some ⟨2, 4⟩ := by
  decide

/-- Distinct admitted occurrences retain their shared pattern key and therefore
pool under the existing `witnessedOutcomes`; no occurrence-local theta is added. -/
theorem admitted_occurrences_pool_by_pattern :
    PatternTheta.witnessedOutcomes .shared
      ([project controlGate (requestedAt 0)
          (supplied 0 (some true) (some (evidence 0 true))),
        project controlGate (requestedAt 19)
          (supplied 19 (some false) (some (evidence 19 false)))].filterMap id) =
      [true, false] := by
  decide


/-! ## The executable completion-check form (defect R8a)

`AuthorityCheck` above is a supplied parameter; `controlGate` instantiates it
with a synthetic premise. This section instantiates it with the one authored
completion-check form that has a runtime decision procedure, the artifact
locator, as `futon2.aif.completion-check/evaluate` (futon2 `173e4b091`)
computes it. Witness mode: the Lean states the law; the Clojure conforms.

The producer (`futon2.aif.pattern-observation/supplied-row`) asks the
evaluator for the one matching condition's authored check at the request's
revision. For a well-formed `C3` or `C4` locator the evaluator's Boolean
becomes the row's `observed` and the evaluator's reading becomes the row's
authority evidence. Every other form (prose, a square description, a
malformed or unsupported locator) is a typed absence: `observed = none`, and
the row falls under `missing_observation_not_admitted`. That is the status of
all 27 authored checks at attempt-002, which are prose.

What the gate decides and what it is told. The gate cannot run git. The
reading of a locator at a commit, `read`, is the supplied parameter, a
function from the validated locator and the revision to `Option Bool`:
`some b` when the repository answered (the path or declaration is present,
`b = true`, or absent, `b = false`), `none` when it could not (unknown sha).
An absent file at a resolvable commit is therefore an observation of `false`
and is admitted as failure, not treated as a missing observation. This keeps
the module's own distinction: absence of an observation is `none`; an
observation of absence is `some false`. The evaluator adds two refusals of
its own before the reader runs: a locator whose repository is not the
request's (`:different-artifact-repository`) and a revision that is not a
40-character lowercase hex sha (`:after-revision-missing`). Both are `none`
here, for every `read`.

An authored `:sha` on the locator is provenance only. The evaluator always
reads at the request's revision; the authored value is carried into the
evidence (`:authored-sha`) and binds nothing. `authored_sha_not_binding`
states that for every reading. -/

/-- The two artifact classes with a decision procedure: `C3` path present at a
commit, `C4` declaration present in a file at a commit. C5, C6 and C8 are not
executable completion checks (`supported-classes`). -/
inductive LocatorClass where | C3 | C4 deriving DecidableEq, Repr

/-- The runtime's revision: a repository name and a commit sha. -/
structure Rev where
  repo : String
  sha : String
  deriving DecidableEq, Repr

/-- The authored completion-check form, as the fold condition carries it.
Only `locator` can be executable, and only when well formed. -/
inductive CompletionCheckForm where
  | prose (text : String)
  | square (tag : String)
  | locator (cls : LocatorClass) (repo path : String) (decl : Option String)
      (authoredSha : Option String)
  deriving DecidableEq, Repr

/-- A validated locator: the fields the reader needs. The authored sha is not
among them; `evaluate` reads at the request's revision. -/
structure Locator where
  cls : LocatorClass
  repo : String
  path : String
  decl : Option String
  deriving DecidableEq, Repr

/-- `non-blank-field?`: a string with some non-whitespace character. -/
def nonBlank (s : String) : Bool := s.toList.any (fun c => !c.isWhitespace)

/-- `required-fields`: `repo` and `path` for both classes, `decl` for `C4`,
each non-blank. -/
def wellFormed (cls : LocatorClass) (repo path : String) (decl : Option String) : Bool :=
  nonBlank repo && nonBlank path &&
    (match cls, decl with
      | .C3, _ => true
      | .C4, some d => nonBlank d
      | .C4, none => false)

/-- `executable?` as a projection: `some` exactly for a complete `C3` or `C4`
locator, dropping the inert authored sha. -/
def toLocator : CompletionCheckForm → Option Locator
  | .locator cls repo path decl _ =>
      if wellFormed cls repo path decl then some ⟨cls, repo, path, decl⟩ else none
  | _ => none

def executable (form : CompletionCheckForm) : Bool := (toLocator form).isSome

/-- The runtime's revision guard: 40 lowercase hex characters. -/
def isCommitSha (s : String) : Bool :=
  s.toList.length = 40 && s.toList.all (fun c => c.isDigit || ('a' ≤ c && c ≤ 'f'))

/-- What git reads for a validated locator at a revision, or `none` when the
commit is unknown. Supplied: the module does not run git. -/
abbrev Reader := Locator → Rev → Option Bool

/-- `completion-check/evaluate` on a validated locator: the repository must be
the request's, the sha must be a commit sha, then the reader answers. -/
def evaluate (read : Reader) (loc : Locator) (rev : Rev) : Option Bool :=
  if loc.repo = rev.repo ∧ isCommitSha rev.sha then read loc rev else none

/-- The producer's `observed` for one condition's authored form: the
evaluator's Boolean where the form is executable, `none` otherwise. -/
def supplyObserved (read : Reader) (form : CompletionCheckForm) (rev : Rev) :
    Option Bool :=
  (toLocator form).bind (fun loc => evaluate read loc rev)

/-- The evaluator's reading as authority evidence: the revision it read at,
the locator it read, the authored sha it carried, and the Boolean it read. -/
structure LocatorEvidence where
  revision : Rev
  locator : Locator
  authoredSha : Option String
  reading : Bool
  deriving DecidableEq, Repr

/-- The `AuthorityCheck` for the locator form. Evidence is admitted for
outcome `b` at request `r` exactly when it is a reading at `r.revision`, its
reading is `b`, and the evaluator at `r.revision` does read `b` for its
locator. The authored sha is not consulted. -/
def locatorGate (read : Reader) :
    AuthorityCheck LocatorEvidence PatternKey Occurrence Effect Rev where
  Admits e r b :=
    e.revision = r.revision ∧ e.reading = b ∧
    evaluate read e.locator r.revision = some b
  check e r b := decide
    (e.revision = r.revision ∧ e.reading = b ∧
     evaluate read e.locator r.revision = some b)
  check_iff _ _ _ := by simp

omit [DecidableEq PatternKey] [DecidableEq Occurrence] [DecidableEq Effect] in
/-- The authored sha binds nothing: admission is the same for every value of
it, including `HEAD` and none at all. -/
theorem authored_sha_not_binding (read : Reader)
    (rev : Rev) (loc : Locator) (s s' : Option String) (b : Bool)
    (r : Request PatternKey Occurrence Effect Rev) :
    (locatorGate (PatternKey := PatternKey) (Occurrence := Occurrence)
        (Effect := Effect) read).Admits ⟨rev, loc, s, b⟩ r b ↔
      (locatorGate (PatternKey := PatternKey) (Occurrence := Occurrence)
        (Effect := Effect) read).Admits ⟨rev, loc, s', b⟩ r b := by
  simp [locatorGate]

/-- A locator on another repository is refused before any reader runs. -/
theorem wrong_repository_short_circuits_the_reader (read : Reader)
    (loc : Locator) (rev : Rev) (h : loc.repo ≠ rev.repo) :
    evaluate read loc rev = none := by
  simp [evaluate, h]

/-- A revision that is not a commit sha is refused before any reader runs. -/
theorem non_commit_revision_short_circuits_the_reader (read : Reader)
    (loc : Locator) (rev : Rev) (h : isCommitSha rev.sha = false) :
    evaluate read loc rev = none := by
  simp [evaluate, h]

/-- Only the locator form reaches `locatorGate`: a prose or square form
supplies no Boolean at any revision under any reader, so its row is the
`missing_observation_not_admitted` case. The 27 authored checks at
attempt-002 are prose. -/
theorem prose_and_square_checks_are_not_executable (read : Reader) (rev : Rev)
    (form : CompletionCheckForm)
    (h : ∀ cls repo path decl sha, form ≠ .locator cls repo path decl sha) :
    supplyObserved read form rev = none := by
  cases form with
  | prose t => rfl
  | square t => rfl
  | locator cls repo path decl sha => exact absurd rfl (h cls repo path decl sha)

/-- The producer's row for a prose check falls under the existing theorem. -/
theorem prose_row_not_admitted (read : Reader)
    (requested : Request PatternKey Occurrence Effect Rev)
    (text : String) (evidence : Option LocatorEvidence) :
    project (locatorGate read) requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, supplyObserved read (.prose text) requested.revision,
        evidence⟩ = none :=
  missing_observation_not_admitted _ _ _ rfl

/-- The R8a binding: when the producer's Boolean is the evaluator's reading at
the request's revision, the row it emits (that Boolean, that reading as
evidence) is admitted with that Boolean, `true` or `false` alike. -/
theorem supplied_locator_row_admitted (read : Reader)
    (requested : Request PatternKey Occurrence Effect Rev)
    (form : CompletionCheckForm) (loc : Locator) (b : Bool)
    (sha : Option String)
    (hloc : toLocator form = some loc)
    (hobs : supplyObserved read form requested.revision = some b) :
    project (locatorGate read) requested
      ⟨requested.pattern, requested.occurrence, requested.effect,
        requested.revision, some b, some ⟨requested.revision, loc, sha, b⟩⟩ =
      some ⟨requested.pattern, true, b⟩ := by
  apply project_of_admitted
  refine ⟨rfl, rfl, ?_⟩
  simpa [supplyObserved, hloc] using hobs

/-! ### Controls from `completion_check_test.clj` and `pattern_observation_test.clj`

The reader below is the table of what those tests observed in `futon5a` at
the pinned after revision `547b191f…`: the mission file is present, the
heading `## 1. IDENTIFY` is in it, `holes/missions/no-such-file.md` and
`## NO-SUCH-HEADING` are not, and no other commit resolves. The theorems pin
the gate's handling of those readings, not the readings themselves. -/

def after : Rev := ⟨"futon5a", "547b191f8fa1e818b0edca02560abf0017b96abd"⟩
def before : Rev := ⟨"futon5a", "68120423443eab3243c400563cc9c66f45fea6e7"⟩
def missionPath : String := "holes/missions/M-war-machine-wiring.md"

def fixtureRead : Reader := fun loc rev =>
  if rev = after then
    match loc.cls with
    | .C3 => some (loc.path = missionPath)
    | .C4 => some (loc.path = missionPath ∧ loc.decl = some "## 1. IDENTIFY")
  else none

def missionLocator : CompletionCheckForm :=
  .locator .C3 "futon5a" missionPath none none

def absentFileLocator : CompletionCheckForm :=
  .locator .C3 "futon5a" "holes/missions/no-such-file.md" none none

def fixtureGate : AuthorityCheck LocatorEvidence Pattern Nat EffectKind Rev :=
  locatorGate fixtureRead

def requestedAfter : Request Pattern Nat EffectKind Rev := ⟨.shared, 19, .emitted, after⟩

def rowAt (rev : Rev) (observed : Option Bool) (authority : Option LocatorEvidence) :
    SuppliedObservation Pattern Nat EffectKind Rev LocatorEvidence :=
  ⟨.shared, 19, .emitted, rev, observed, authority⟩

def readingOf (form : CompletionCheckForm) (rev : Rev) (sha : Option String) (b : Bool) :
    Option LocatorEvidence :=
  (toLocator form).map (fun loc => ⟨rev, loc, sha, b⟩)

theorem c3_observes_presence_at_the_after_revision :
    supplyObserved fixtureRead missionLocator after = some true := by decide

/-- Control 1. An absent file at the after revision is an observed `false`,
and the gate admits it as failure; it is not a missing observation. -/
theorem c3_false_is_an_observation_not_an_absence :
    supplyObserved fixtureRead absentFileLocator after = some false ∧
    project fixtureGate requestedAfter
      (rowAt after (some false) (readingOf absentFileLocator after none false)) =
      some ⟨.shared, true, false⟩ := by
  decide

theorem c4_observes_declarations_at_the_after_revision :
    supplyObserved fixtureRead
      (.locator .C4 "futon5a" missionPath (some "## 1. IDENTIFY") none) after =
      some true ∧
    supplyObserved fixtureRead
      (.locator .C4 "futon5a" missionPath (some "## NO-SUCH-HEADING") none) after =
      some false := by
  decide

/-- Control 2. The authored sha `HEAD` loses to the request's revision: the
same reading is admitted at `after`, and the evidence that carries `HEAD` is
admitted exactly as the evidence that carries none. -/
theorem supplied_revision_overrides_an_authored_sha :
    supplyObserved fixtureRead
      (.locator .C3 "futon5a" missionPath none (some "HEAD")) after = some true ∧
    project fixtureGate requestedAfter
      (rowAt after (some true)
        (readingOf (.locator .C3 "futon5a" missionPath none (some "HEAD")) after
          (some "HEAD") true)) =
      some ⟨.shared, true, true⟩ := by
  decide

/-- Control 3. A reading supplied at `before` is not admitted against a request
at `after`: `revision_mismatch_not_admitted`, instantiated. -/
theorem before_reading_not_admitted_at_after :
    project fixtureGate requestedAfter
      (rowAt before (some true) (readingOf missionLocator before none true)) = none :=
  revision_mismatch_not_admitted fixtureGate requestedAfter _ (by decide)

/-- The evidence's own revision must also be the request's: a reading taken
at `before` but attached to a row stamped `after` is rejected by the gate. -/
theorem stale_reading_on_a_current_row_not_admitted :
    project fixtureGate requestedAfter
      (rowAt after (some true) (readingOf missionLocator before none true)) = none := by
  decide

/-- The fold status cannot override the evaluator: a row claiming `true` for a
locator whose reading is `false` is rejected, and the reading itself is
admitted only as `false`. -/
theorem executable_check_false_overrides_an_established_fold_status :
    project fixtureGate requestedAfter
      (rowAt after (some true) (readingOf absentFileLocator after none false)) = none ∧
    project fixtureGate requestedAfter
      (rowAt after (some true) (readingOf absentFileLocator after none true)) = none := by
  decide

theorem wrong_repository_is_a_typed_absence :
    supplyObserved fixtureRead (.locator .C3 "futon2" "deps.edn" none none) after =
      none := by
  decide

theorem revision_refusals_stay_typed :
    supplyObserved fixtureRead missionLocator ⟨"futon5a", "HEAD"⟩ = none ∧
    supplyObserved fixtureRead missionLocator
      ⟨"futon5a", "0000000000000000000000000000000000000000"⟩ = none := by
  decide

/-- Control 4, the forms. A prose check, a square, a `C4` without `decl`, and a
blank repository are not executable; the mission locator is. -/
theorem malformed_locators_are_not_executable :
    executable (.prose "emission per mission") = false ∧
    executable (.square "B-observed") = false ∧
    executable (.locator .C4 "futon5a" "x" none none) = false ∧
    executable (.locator .C3 "" "x" none none) = false ∧
    executable missionLocator = true := by
  decide

#print axioms locatorGate
#print axioms authored_sha_not_binding
#print axioms supplied_locator_row_admitted
#print axioms prose_row_not_admitted
#print axioms c3_false_is_an_observation_not_an_absence
#print axioms supplied_revision_overrides_an_authored_sha
#print axioms before_reading_not_admitted_at_after
#print axioms executable_check_false_overrides_an_established_fold_status

#print axioms project_of_admitted
#print axioms project_eq_some_only_if
#print axioms missing_observation_not_admitted
#print axioms missing_authority_not_admitted
#print axioms unqualified_not_admitted
#print axioms occurrence_mismatch_not_admitted
#print axioms witnessed_false_reaches_failure_update
#print axioms admitted_occurrences_pool_by_pattern

end DarkTower.WarMachine.PatternObservationAdmission
