/-!
# Mission observation admission

This is a narrow model of the selected-mission-want reviewer seam.  It does
not infer observations from an initial belief, pattern prediction, schema tag,
or selection.  Authenticity of evidence remains an external supplied premise.
Before and after revisions are deliberately distinct.
-/

namespace DarkTower.WarMachine.MissionObservationAdmission

inductive Side where | before | after
  deriving DecidableEq, Repr

structure Request
    (Occurrence Action Target Token Locator Repository Revision : Type) where
  occurrence : Occurrence
  action : Action
  target : Target
  wants : List Token
  locators : Token → Locator
  repository : Repository
  beforeRevision : Revision
  afterRevision : Revision

structure Row
    (Occurrence Action Target Token Locator Repository Revision Evidence : Type) where
  occurrence : Occurrence
  action : Action
  target : Target
  token : Token
  locator : Locator
  repository : Repository
  beforeRevision : Revision
  afterRevision : Revision
  beforeObserved : Option Bool
  afterObserved : Option Bool
  beforeEvidence : Option Evidence
  afterEvidence : Option Evidence
  deriving Repr

structure AuthorityCheck
    (Evidence Occurrence Action Target Token Locator Repository Revision : Type) where
  Admits : Evidence → Side → Occurrence → Action → Target → Token → Locator →
    Repository → Revision → Bool → Prop
  check : Evidence → Side → Occurrence → Action → Target → Token → Locator →
    Repository → Revision → Bool → Bool
  check_iff : ∀ e side occurrence action target token locator repository revision value,
    check e side occurrence action target token locator repository revision value = true ↔
      Admits e side occurrence action target token locator repository revision value

structure Outcome (Token : Type) where
  token : Token
  beforeObserved : Bool
  afterObserved : Bool
  deriving DecidableEq, Repr

variable {Occurrence Action Target Token Locator Repository Revision Evidence : Type}
  [DecidableEq Occurrence] [DecidableEq Action] [DecidableEq Target]
  [DecidableEq Token] [DecidableEq Locator] [DecidableEq Repository]
  [DecidableEq Revision]

def qualifiedRow
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence) : Prop :=
  row.occurrence = request.occurrence ∧ row.action = request.action ∧
  row.target = request.target ∧ row.locator = request.locators row.token ∧
  row.repository = request.repository ∧ row.beforeRevision = request.beforeRevision ∧
  row.afterRevision = request.afterRevision ∧
  ∃ beforeEvidence afterEvidence afterValue,
    row.beforeObserved = some false ∧ row.afterObserved = some afterValue ∧
    row.beforeEvidence = some beforeEvidence ∧ row.afterEvidence = some afterEvidence ∧
    authority.Admits beforeEvidence .before request.occurrence request.action request.target
      row.token (request.locators row.token) request.repository request.beforeRevision false ∧
    authority.Admits afterEvidence .after request.occurrence request.action request.target
      row.token (request.locators row.token) request.repository request.afterRevision afterValue

def checkRow
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence) : Bool :=
  if row.occurrence = request.occurrence ∧ row.action = request.action ∧
      row.target = request.target ∧ row.locator = request.locators row.token ∧
      row.repository = request.repository ∧ row.beforeRevision = request.beforeRevision ∧
      row.afterRevision = request.afterRevision then
    match row.beforeObserved, row.afterObserved, row.beforeEvidence, row.afterEvidence with
    | some false, some afterValue, some beforeEvidence, some afterEvidence =>
      authority.check beforeEvidence .before request.occurrence request.action request.target
          row.token (request.locators row.token) request.repository request.beforeRevision false &&
        authority.check afterEvidence .after request.occurrence request.action request.target
          row.token (request.locators row.token) request.repository request.afterRevision afterValue
    | _, _, _, _ => false
  else false

theorem checkRow_eq_true_only_if
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence)
    (h : checkRow authority request row = true) : qualifiedRow authority request row := by
  unfold checkRow at h
  by_cases bindings : row.occurrence = request.occurrence ∧ row.action = request.action ∧
      row.target = request.target ∧ row.locator = request.locators row.token ∧
      row.repository = request.repository ∧ row.beforeRevision = request.beforeRevision ∧
      row.afterRevision = request.afterRevision
  · rw [if_pos bindings] at h
    rcases bindings with ⟨hocc, haction, htarget, hlocator, hrepo, hbefore, hafter⟩
    cases hb : row.beforeObserved with
    | none => simp [hb] at h
    | some beforeValue =>
      cases beforeValue with
      | true => simp [hb] at h
      | false =>
        cases ha : row.afterObserved with
        | none => simp [hb, ha] at h
        | some afterValue =>
          cases hbe : row.beforeEvidence with
          | none => simp [hb, ha, hbe] at h
          | some beforeEvidence =>
            cases hae : row.afterEvidence with
            | none => simp [hb, ha, hbe, hae] at h
            | some afterEvidence =>
              simp [hb, ha, hbe, hae, Bool.and_eq_true,
                authority.check_iff] at h
              exact ⟨hocc, haction, htarget, hlocator, hrepo, hbefore, hafter,
                beforeEvidence, afterEvidence, afterValue, hb, ha, hbe, hae, h.1, h.2⟩
  · rw [if_neg bindings] at h
    contradiction

def admit
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (rows : List (Row Occurrence Action Target Token Locator Repository Revision Evidence)) :
    Option (List (Outcome Token)) :=
  if request.wants.Nodup ∧ rows.map (·.token) = request.wants ∧
      rows.all (checkRow authority request) then
    some (rows.map fun row => ⟨row.token, false, row.afterObserved.getD false⟩)
  else none

theorem admit_eq_some_only_if
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (rows : List (Row Occurrence Action Target Token Locator Repository Revision Evidence))
    (outcomes : List (Outcome Token))
    (h : admit authority request rows = some outcomes) :
    request.wants.Nodup ∧ rows.map (·.token) = request.wants ∧
      (∀ row ∈ rows, qualifiedRow authority request row) ∧
      outcomes = rows.map (fun row => ⟨row.token, false, row.afterObserved.getD false⟩) := by
  simp only [admit] at h
  split at h <;> try contradiction
  next admitted =>
    rcases admitted with ⟨hnodup, hcensus, hall⟩
    simp at h
    subst outcomes
    refine ⟨hnodup, hcensus, ?_, rfl⟩
    intro row hrow
    have hc : checkRow authority request row = true :=
      (List.all_eq_true.mp hall) row hrow
    exact checkRow_eq_true_only_if authority request row hc

theorem missing_before_not_admitted
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence)
    (h : row.beforeObserved = none) :
    checkRow authority request row = false := by
  simp [checkRow, h]

theorem missing_after_not_admitted
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence)
    (h : row.afterObserved = none) :
    checkRow authority request row = false := by
  simp [checkRow, h]

theorem before_true_not_admitted
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence)
    (h : row.beforeObserved = some true) :
    checkRow authority request row = false := by
  simp [checkRow, h]

/-- An initial belief is intentionally not an input to `admit`; supplying one
cannot change a refused observation. -/
theorem initialBelief_cannot_supply_missing_before
    {State : Type}
    (authority : AuthorityCheck Evidence Occurrence Action Target Token Locator Repository Revision)
    (request : Request Occurrence Action Target Token Locator Repository Revision)
    (row : Row Occurrence Action Target Token Locator Repository Revision Evidence)
    (_q0 : State → Rat)
    (h : row.beforeObserved = none) :
    checkRow authority request row = false :=
  missing_before_not_admitted authority request row h

namespace Examples

def authority : AuthorityCheck Bool Nat Nat Nat Nat Nat Nat Nat where
  Admits evidence _ _ _ _ _ _ _ _ value := evidence = value
  check evidence _ _ _ _ _ _ _ _ value := evidence == value
  check_iff := by intros; simp

def request : Request Nat Nat Nat Nat Nat Nat Nat :=
  ⟨1, 2, 3, [10, 11], id, 4, 5, 6⟩

def row (token : Nat) (before after : Option Bool) (beforeEvidence afterEvidence : Option Bool) :
    Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  ⟨1, 2, 3, token, token, 4, 5, 6, before, after, beforeEvidence, afterEvidence⟩

def falseFalse := row 10 (some false) (some false) (some false) (some false)
def falseTrue := row 11 (some false) (some true) (some false) (some true)

example : admit authority request [falseFalse, falseTrue] =
    some [⟨10, false, false⟩, ⟨11, false, true⟩] := by native_decide

example : admit authority request [row 10 none (some false) none (some false), falseTrue] = none := by
  native_decide

example : admit authority request [row 10 (some false) none (some false) none, falseTrue] = none := by
  native_decide

example : admit authority request [row 10 (some true) (some true) (some true) (some true), falseTrue] = none := by
  native_decide

def staleBefore : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  { falseFalse with beforeRevision := 99 }
def staleAfter : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  { falseFalse with afterRevision := 99 }
def wrongOccurrence : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  { falseFalse with occurrence := 99 }
def wrongRepository : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  { falseFalse with repository := 99 }
def wrongLocator : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  { falseFalse with locator := 99 }

example : admit authority request [staleBefore, falseTrue] = none := by native_decide
example : admit authority request [staleAfter, falseTrue] = none := by native_decide
example : admit authority request [wrongOccurrence, falseTrue] = none := by native_decide
example : admit authority request [wrongRepository, falseTrue] = none := by native_decide
example : admit authority request [wrongLocator, falseTrue] = none := by native_decide
example : admit authority request [falseFalse, falseFalse] = none := by native_decide

/-- The after payload is flipped while retaining evidence for the old false
payload; payload-bound authority refuses it. -/
def flippedWithOldAuthority : Row Nat Nat Nat Nat Nat Nat Nat Bool :=
  row 10 (some false) (some true) (some false) (some false)
example : admit authority request [flippedWithOldAuthority, falseTrue] = none := by native_decide

end Examples

end DarkTower.WarMachine.MissionObservationAdmission
