import DarkTower.WarMachine.F11Conformance

/-! Search certificates with externally supplied admissibility, pinned repository
domains, and evidence-derived legacy receipts. No similarity metric is chosen. -/

open Set
namespace DarkTower.WarMachine.Holes

structure PinnedPatternRepository (P : Type*) where
  identity : String
  version : String
  digest : String
  members : List P
  nodup : members.Nodup

inductive SearchDomainScope (repositoryMembers domainMembers : List P) where
  | complete (sameMembers : domainMembers = repositoryMembers)
  | bounded (limitation : String) (limitationNonempty : limitation ≠ "")
      (subsetRepository : ∀ p, p ∈ domainMembers → p ∈ repositoryMembers)

structure SearchDomain (P : Type*) where
  repository : PinnedPatternRepository P
  members : List P
  nodup : members.Nodup
  scope : SearchDomainScope repository.members members

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
  evidenceToLegacy : Evidence → Option LegacyReceipt
  outcome : SearchOutcome P

def externallyAuthored [DecidableEq Authority] (searchAuthority : Authority)
    (j : ExternalJudgment P Authority Evidence Reason) : Prop :=
  j.authority ≠ searchAuthority

def judgedAdmissible
    (js : List (ExternalJudgment P Authority Evidence Reason)) (p : P) : Prop :=
  ∃ j ∈ js, j.pattern = p ∧ ∃ e, j.verdict = .admissible e

def judgedRejected
    (js : List (ExternalJudgment P Authority Evidence Reason)) (p : P) : Prop :=
  ∃ j ∈ js, j.pattern = p ∧ ∃ reason evidence, j.verdict = .rejected reason evidence

def projectedJudgmentReceipt
    (js : List (ExternalJudgment P Authority Evidence Reason))
    (project : Evidence → Option LegacyReceipt) (p : P) (receipt : LegacyReceipt) : Prop :=
  ∃ j ∈ js, j.pattern = p ∧ ∃ evidence,
    j.verdict = .admissible evidence ∧ project evidence = some receipt

noncomputable def firstAdmissible
    (priority : List P)
    (js : List (ExternalJudgment P Authority Evidence Reason)) : Option P := by
  classical
  exact priority.find? (fun p => decide (judgedAdmissible js p))

structure ValidOpenCascadeSearch [DecidableEq P] [DecidableEq Authority]
    (r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason) : Prop where
  priorityNodup : r.priority.Nodup
  priorityCoversDomain : ∀ p, p ∈ r.priority ↔ p ∈ r.domain.members
  judgmentCoverage : r.judgments.map (·.pattern) = r.domain.members
  externalAuthority : ∀ j, j ∈ r.judgments → externallyAuthored r.searchAuthority j
  admissibleEvidenceProjects : ∀ j, j ∈ r.judgments → ∀ evidence,
    j.verdict = .admissible evidence → ∃ receipt,
      r.evidenceToLegacy evidence = some receipt ∧ receipt.nonSelfCertifying
  outcomeLaw : match r.outcome with
    | .chosenExisting p => p ∈ r.domain.members ∧ judgedAdmissible r.judgments p ∧
        firstAdmissible r.priority r.judgments = some p
    | .noAdmissibleMatch => ∀ p ∈ r.domain.members,
        judgedRejected r.judgments p ∧ ¬ judgedAdmissible r.judgments p

theorem validNoMatch_noDomainMemberAdmissible
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (h : ValidOpenCascadeSearch r) (hout : r.outcome = .noAdmissibleMatch) :
    ∀ p ∈ r.domain.members, ¬ judgedAdmissible r.judgments p := by
  intro p hp hadm
  have hr := h.outcomeLaw
  rw [hout] at hr
  exact (hr p hp).2 hadm

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

noncomputable def eraseOpenCascadeSearch [DecidableEq P]
    (r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason) :
    LegacyFindResult P := by
  classical
  let selected : Set P := match r.outcome with
    | .chosenExisting p => {p}
    | .noAdmissibleMatch => ∅
  exact
    { selected := selected
      receipts := fun p =>
        if h : ∃ receipt, projectedJudgmentReceipt r.judgments r.evidenceToLegacy p receipt
        then some h.choose else none
      absence := match r.outcome, r.domain.scope with
        | .noAdmissibleMatch, .complete _ => some .noPatternAddressesThisTension
        | _, _ => none }

structure LegacyProjectionConformsAtDomain (domain : List P) (x : LegacyFindResult P) : Prop where
  containment : ∀ p, p ∈ x.selected → p ∈ domain
  selectedReceipted : ∀ p, p ∈ x.selected → (x.receipts p).isSome
  selectedNonSelfCertifying : ∀ p receipt, p ∈ x.selected →
    x.receipts p = some receipt → receipt.nonSelfCertifying

theorem validSearch_erasurePreservesEvidenceProjectedLegacyConformance
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
      have : p = q := by simpa [eraseOpenCascadeSearch, ho] using hp
      subst p
      exact (validChosen_member_admissible_and_obeysLaw h ho).1
  · intro p hp
    cases ho : r.outcome with
    | noAdmissibleMatch => simp [eraseOpenCascadeSearch, ho] at hp
    | chosenExisting q =>
      have hpq : p = q := by simpa [eraseOpenCascadeSearch, ho] using hp
      subst p
      obtain ⟨j, hj, rfl, evidence, hverdict⟩ :=
        (validChosen_member_admissible_and_obeysLaw h ho).2.1
      obtain ⟨receipt, hproject, _⟩ := h.admissibleEvidenceProjects j hj evidence hverdict
      simp only [eraseOpenCascadeSearch]
      split
      · simp
      · rename_i hn
        exact False.elim (hn ⟨receipt, j, hj, rfl, evidence, hverdict, hproject⟩)
  · intro p receipt hp hreceipt
    simp only [eraseOpenCascadeSearch] at hreceipt
    split at hreceipt
    · rename_i hex
      cases hreceipt
      obtain ⟨j, hj, _, evidence, hverdict, hproject⟩ := hex.choose_spec
      obtain ⟨_, hsame, hnonself⟩ := h.admissibleEvidenceProjects j hj evidence hverdict
      rw [hproject] at hsame
      cases hsame
      exact hnonself
    · simp at hreceipt

theorem completeNoMatch_impliesRepositoryGlobalAbsence
    [DecidableEq P] [DecidableEq Authority]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (_h : ValidOpenCascadeSearch r) (hout : r.outcome = .noAdmissibleMatch)
    (hcomplete : ∃ equality, r.domain.scope = .complete equality) :
    (eraseOpenCascadeSearch r).absence = some .noPatternAddressesThisTension := by
  obtain ⟨equality, heq⟩ := hcomplete
  simp [eraseOpenCascadeSearch, hout, heq]

theorem boundedNoMatch_doesNotClaimRepositoryGlobalAbsence
    [DecidableEq P]
    {r : OpenCascadeSearchReceipt P Query Blocker CascadeId Authority Evidence Reason}
    (hout : r.outcome = .noAdmissibleMatch)
    (hbounded : ∃ limitation hn hs, r.domain.scope = .bounded limitation hn hs) :
    (eraseOpenCascadeSearch r).absence = none := by
  obtain ⟨limitation, hn, hs, heq⟩ := hbounded
  simp [eraseOpenCascadeSearch, hout, heq]

inductive ExamplePattern | a | b deriving DecidableEq, Repr
inductive ExampleAuthority | search | reviewer deriving DecidableEq, Repr
inductive ExampleEvidence | citedA | citedRejection deriving DecidableEq, Repr

def exampleRepository : PinnedPatternRepository ExamplePattern :=
  { identity := "fixture-library", version := "v1", digest := "sha256:fixture"
    members := [.a, .b], nodup := by decide }

def exampleDomain : SearchDomain ExamplePattern :=
  { repository := exampleRepository, members := [.a, .b], nodup := by decide
    scope := .bounded "top-two fixture" (by decide) (by simp [exampleRepository]) }

def exampleLegacyProjection : ExampleEvidence → Option LegacyReceipt
  | .citedA => some { citesTextOrEdges := True, scoreAlone := False }
  | .citedRejection => none

def admissibleA : ExternalJudgment ExamplePattern ExampleAuthority ExampleEvidence String :=
  { pattern := .a, verdict := .admissible .citedA, authority := .reviewer }
def rejectedB : ExternalJudgment ExamplePattern ExampleAuthority ExampleEvidence String :=
  { pattern := .b, verdict := .rejected "not applicable" .citedRejection,
    authority := .reviewer }

def chosenExample : OpenCascadeSearchReceipt ExamplePattern Unit Unit Unit
    ExampleAuthority ExampleEvidence String :=
  { domain := exampleDomain, query := (), blocker := (), priorCascade := ()
    searchAuthority := .search, judgments := [admissibleA, rejectedB]
    priority := [.a, .b], evidenceToLegacy := exampleLegacyProjection,
    outcome := .chosenExisting .a }

theorem chosenExample_valid : ValidOpenCascadeSearch chosenExample := by
  constructor <;> simp [chosenExample, exampleDomain, exampleRepository, admissibleA,
    rejectedB, externallyAuthored, judgedAdmissible, firstAdmissible,
    exampleLegacyProjection, LegacyReceipt.nonSelfCertifying]

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
  have hx := h.outcomeLaw
  simp [nonAdmissibleChosenExample, chosenExample, judgedAdmissible, admissibleA, rejectedB] at hx

def unprojectableEvidenceExample := { chosenExample with evidenceToLegacy := fun _ => none }
theorem unprojectableEvidenceExample_invalid :
    ¬ ValidOpenCascadeSearch unprojectableEvidenceExample := by
  intro h
  have hx := h.admissibleEvidenceProjects admissibleA
    (by simp [unprojectableEvidenceExample, chosenExample]) ExampleEvidence.citedA rfl
  simp [unprojectableEvidenceExample] at hx

def duplicatePriorityExample := { chosenExample with priority := [.a, .a, .b] }
theorem duplicatePriorityExample_invalid : ¬ ValidOpenCascadeSearch duplicatePriorityExample := by
  intro h
  simpa [duplicatePriorityExample, chosenExample] using h.priorityNodup

def truncatedFalselyCompleteDomain : SearchDomain ExamplePattern :=
  { repository := exampleRepository, members := [.a], nodup := by decide
    scope := .bounded "only a" (by decide) (by simp [exampleRepository]) }

theorem truncatedDomain_cannotCarryCompletenessProof :
    ¬ ∃ equality, truncatedFalselyCompleteDomain.scope = .complete equality := by
  simp [truncatedFalselyCompleteDomain]

def completeNoMatchDomain : SearchDomain ExamplePattern :=
  { repository := exampleRepository, members := [.a, .b], nodup := by decide
    scope := .complete rfl }

def completeNoMatchExample : OpenCascadeSearchReceipt ExamplePattern Unit Unit Unit
    ExampleAuthority ExampleEvidence String :=
  { domain := completeNoMatchDomain, query := (), blocker := (), priorCascade := ()
    searchAuthority := .search
    judgments := [{ admissibleA with verdict := .rejected "no" .citedRejection }, rejectedB]
    priority := [.a, .b], evidenceToLegacy := exampleLegacyProjection,
    outcome := .noAdmissibleMatch }

theorem completeNoMatchExample_valid : ValidOpenCascadeSearch completeNoMatchExample := by
  constructor <;> simp [completeNoMatchExample, completeNoMatchDomain, exampleRepository,
    admissibleA, rejectedB, externallyAuthored, judgedRejected, judgedAdmissible]

end DarkTower.WarMachine.Holes
