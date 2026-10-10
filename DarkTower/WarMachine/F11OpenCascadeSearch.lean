import DarkTower.WarMachine.F11Conformance

/-! # F11 open-cascade pattern-search certificates

The admissibility judgment is an input from an authority distinct from the
search implementation.  This file deliberately supplies no similarity metric
or numeric threshold. -/

open Set
namespace DarkTower.WarMachine.Holes

inductive SearchDomainKind where
  | complete
  | bounded (limitation : String)
  deriving DecidableEq, Repr

structure SearchDomain (P : Type*) where
  members : List P
  nodup : members.Nodup
  kind : SearchDomainKind

inductive Admissibility (Evidence Reason : Type*) where
  | admissible (evidence : Evidence)
  | rejected (reason : Reason) (evidence : Evidence)

structure ExternalJudgment (P Authority Evidence Reason : Type*) where
  pattern : P
  verdict : Admissibility Evidence Reason
  authority : Authority

inductive SearchOutcome (P : Type*) where
  | chosenExisting (pattern : P)
  | noAdmissibleMatch
  deriving DecidableEq, Repr

structure OpenCascadeSearchReceipt
    (P Query Blocker CascadeId Authority Evidence Reason : Type*) where
  domain : SearchDomain P
  query : Query
  blocker : Blocker
  priorCascade : CascadeId
  searchAuthority : Authority
  judgments : List (ExternalJudgment P Authority Evidence Reason)
  priority : List P
  outcome : SearchOutcome P

def externallyAuthored [DecidableEq Authority]
    (searchAuthority : Authority)
    (j : ExternalJudgment P Authority Evidence Reason) : Prop :=
  j.authority ≠ searchAuthority

def judgedAdmissible
    (js : List (ExternalJudgment P Authority Evidence Reason)) (p : P) : Prop :=
  ∃ j ∈ js, j.pattern = p ∧ ∃ e, j.verdict = .admissible e

def judgedRejected
    (js : List (ExternalJudgment P Authority Evidence Reason)) (p : P) : Prop :=
  ∃ j ∈ js, j.pattern = p ∧ ∃ reason evidence, j.verdict = .rejected reason evidence

noncomputable def firstAdmissible
    (priority : List P)
    (js : List (ExternalJudgment P Authority Evidence Reason)) : Option P := by
  classical
  exact priority.find? (fun p => decide (judgedAdmissible js p))

structure ValidOpenCascadeSearch [DecidableEq P] [DecidableEq Authority]
    (r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason) : Prop where
  priorityCoversDomain : ∀ p, p ∈ r.priority ↔ p ∈ r.domain.members
  judgmentCoverage : r.judgments.map (·.pattern) = r.domain.members
  externalAuthority : ∀ j, j ∈ r.judgments → externallyAuthored r.searchAuthority j
  outcomeLaw : match r.outcome with
    | .chosenExisting p =>
        p ∈ r.domain.members ∧ judgedAdmissible r.judgments p ∧
          firstAdmissible r.priority r.judgments = some p
    | .noAdmissibleMatch => ∀ p ∈ r.domain.members,
        judgedRejected r.judgments p ∧ ¬ judgedAdmissible r.judgments p

theorem validNoMatch_noDomainMemberAdmissible
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (h : ValidOpenCascadeSearch r) (hout : r.outcome = .noAdmissibleMatch) :
    ∀ p ∈ r.domain.members, ¬ judgedAdmissible r.judgments p := by
  intro p hp hadm
  have hreject := h.outcomeLaw
  rw [hout] at hreject
  have hreject := hreject p hp
  exact hreject.2 hadm

theorem validSearch_judgesEveryDomainMember
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (h : ValidOpenCascadeSearch r) :
    ∀ p ∈ r.domain.members, ∃ j ∈ r.judgments, j.pattern = p := by
  intro p hp
  rw [← h.judgmentCoverage] at hp
  simpa using hp

theorem validChosen_member_admissible_and_obeysLaw
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (h : ValidOpenCascadeSearch r) (hout : r.outcome = .chosenExisting p) :
    p ∈ r.domain.members ∧ judgedAdmissible r.judgments p ∧
      firstAdmissible r.priority r.judgments = some p := by
  simpa [hout] using h.outcomeLaw

def searchLegacyReceipt : LegacyReceipt where
  citesTextOrEdges := True
  scoreAlone := False

def eraseOpenCascadeSearch [DecidableEq P]
    (r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason) :
    LegacyFindResult P :=
  let selected : Set P := match r.outcome with
    | .chosenExisting p => {p}
    | .noAdmissibleMatch => ∅
  { selected := selected
    receipts := fun p => match r.outcome with
      | .chosenExisting q => if p = q then some searchLegacyReceipt else none
      | .noAdmissibleMatch => none
    -- A bounded no-match is deliberately not repository-global absence.
    absence := match r.outcome, r.domain.kind with
      | .noAdmissibleMatch, .complete => some .noPatternAddressesThisTension
      | _, _ => none }

structure LegacyProjectionConformsAtDomain (domain : List P) (x : LegacyFindResult P) : Prop where
  containment : ∀ p, p ∈ x.selected → p ∈ domain
  selectedReceipted : ∀ p, p ∈ x.selected → (x.receipts p).isSome
  selectedNonSelfCertifying : ∀ p receipt, p ∈ x.selected →
    x.receipts p = some receipt → receipt.nonSelfCertifying

theorem validSearch_erasurePreservesLegacyConformance
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (h : ValidOpenCascadeSearch r) :
    LegacyProjectionConformsAtDomain r.domain.members (eraseOpenCascadeSearch r) := by
  classical
  constructor
  · intro p hp
    cases ho : r.outcome with
    | noAdmissibleMatch => simp [eraseOpenCascadeSearch, ho] at hp
    | chosenExisting q =>
      have hpq : p = q := by simpa [eraseOpenCascadeSearch, ho] using hp
      subst p
      exact (validChosen_member_admissible_and_obeysLaw h ho).1
  · intro p hp
    cases ho : r.outcome <;> simp [eraseOpenCascadeSearch, ho] at hp ⊢
    exact hp
  · intro p receipt hp hr
    cases ho : r.outcome <;> simp [eraseOpenCascadeSearch, ho] at hp hr
    subst p
    simp at hr
    cases hr
    simp [LegacyReceipt.nonSelfCertifying, searchLegacyReceipt]

theorem boundedNoMatch_doesNotClaimRepositoryGlobalAbsence
    [DecidableEq P]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (hout : r.outcome = .noAdmissibleMatch)
    (hbounded : r.domain.kind = .bounded limitation) :
    (eraseOpenCascadeSearch r).absence = none := by
  simp [eraseOpenCascadeSearch, hout, hbounded]

/-! Small witnesses and adversarial examples. -/

inductive ExamplePattern | a | b deriving DecidableEq, Repr
inductive ExampleAuthority | search | reviewer deriving DecidableEq, Repr

def exampleDomain : SearchDomain ExamplePattern :=
  { members := [.a, .b], nodup := by decide, kind := .bounded "top-two fixture" }

def admissibleA : ExternalJudgment ExamplePattern ExampleAuthority Unit String :=
  { pattern := .a, verdict := .admissible (), authority := .reviewer }
def rejectedB : ExternalJudgment ExamplePattern ExampleAuthority Unit String :=
  { pattern := .b, verdict := .rejected "not applicable" (), authority := .reviewer }

def chosenExample : OpenCascadeSearchReceipt ExamplePattern Unit Unit Unit
    ExampleAuthority Unit String :=
  { domain := exampleDomain, query := (), blocker := (), priorCascade := ()
    searchAuthority := .search, judgments := [admissibleA, rejectedB]
    priority := [.a, .b], outcome := .chosenExisting .a }

theorem chosenExample_valid : ValidOpenCascadeSearch chosenExample := by
  constructor <;> simp [chosenExample, exampleDomain, admissibleA, rejectedB,
    externallyAuthored, judgedAdmissible, firstAdmissible]

def omittedExample := { chosenExample with judgments := [admissibleA] }
theorem omittedExample_invalid : ¬ ValidOpenCascadeSearch omittedExample := by
  intro h
  simpa [omittedExample, chosenExample, exampleDomain, admissibleA] using h.judgmentCoverage

def selfCertifiedExample :=
  { chosenExample with judgments :=
      [{ admissibleA with authority := ExampleAuthority.search }, rejectedB] }
theorem selfCertifiedExample_invalid : ¬ ValidOpenCascadeSearch selfCertifiedExample := by
  intro h
  have hx := h.externalAuthority
    { admissibleA with authority := ExampleAuthority.search }
    (by simp [selfCertifiedExample, chosenExample])
  simp [selfCertifiedExample, chosenExample, externallyAuthored] at hx

def nonAdmissibleChosenExample := { chosenExample with outcome := SearchOutcome.chosenExisting .b }
theorem nonAdmissibleChosenExample_invalid : ¬ ValidOpenCascadeSearch nonAdmissibleChosenExample := by
  intro h
  have := h.outcomeLaw
  simp [nonAdmissibleChosenExample, chosenExample,
    judgedAdmissible, admissibleA, rejectedB] at this

def completeNoMatchExample : OpenCascadeSearchReceipt ExamplePattern Unit Unit Unit
    ExampleAuthority Unit String :=
  { domain := { exampleDomain with kind := .complete }, query := (), blocker := ()
    priorCascade := (), searchAuthority := .search
    judgments := [{ admissibleA with verdict := .rejected "no" () }, rejectedB]
    priority := [.a, .b], outcome := .noAdmissibleMatch }

theorem completeNoMatchExample_valid : ValidOpenCascadeSearch completeNoMatchExample := by
  constructor <;> simp [completeNoMatchExample, exampleDomain, admissibleA, rejectedB,
    externallyAuthored, judgedRejected, judgedAdmissible]

end DarkTower.WarMachine.Holes
