import DarkTower.WarMachine.R20Certificate

/-!
# Retained independence-row correspondence

This module relates the existing runtime extractor's two operations to
`R20Certificate.IndependenceConforms`: first admit an identity only when its
role receipt is present, then compare the two supplied identity values.

The runtime identity is retained as a string.  `encodePair` is deliberately a
local encoding of one supplied author/reviewer pair into `Fin 2`: the author is
zero, and the reviewer is zero exactly when its supplied identity equals the
author's, otherwise one.  It is not a global assignment of agents to `Fin 2`,
and makes no claim about the identities' external authenticity or about the
independence of their producers.

The production counterpart is futon2
`futon2.aif.wm.apparatus-certificates/identity-at` and `independence-row` at
revision `41e719d97e42a920b9d5fd91f913da83c964e9c4`.  The retained instance is
run `2026-10-23-90ca5944-3d52-4bd6-940c-fe2f6c2c8c6b`, whose author identity
is `"zai-2"` and reviewer-of-record identity is `"zai-3"`.
-/

namespace DarkTower.WarMachine.R20IndependenceRowCorrespondence

open DarkTower.WarMachine.R20Certificate

/-- Presence admission is separate from identity comparison. -/
inductive AdmittedIdentity where
  | absent
  | present (identity : String)
  deriving DecidableEq, Repr

/-- Equality-preserving encoding of one supplied pair, not a global identity map. -/
def encodePair (author reviewer : String) : Fin 2 × Fin 2 :=
  ⟨0, if reviewer = author then 0 else 1⟩

/-- Adapt the row only when both role receipts admitted their supplied identity. -/
def adapt : AdmittedIdentity → AdmittedIdentity → Option IndependenceRow
  | .present author, .present reviewer =>
      let encoded := encodePair author reviewer
      some { author := encoded.1, reviewer := encoded.2 }
  | _, _ => none

/-- The runtime extractor's presence-and-inequality semantics, stated without
borrowing the adapter under test. -/
def ExtractorAgrees (author reviewer : AdmittedIdentity) : Prop :=
  ∃ a r, author = .present a ∧ reviewer = .present r ∧ a ≠ r

theorem encodePair_preserves_equality (author reviewer : String) :
    (encodePair author reviewer).1 = (encodePair author reviewer).2 ↔ author = reviewer := by
  simp [encodePair, eq_comm]

/-- The supplied identities yield a conforming Lean row exactly when both are
present and unequal, which is the existing extractor's rule. -/
theorem adapt_conforms_iff (author reviewer : AdmittedIdentity) :
    (∃ row, adapt author reviewer = some row ∧ IndependenceConforms row) ↔
      ExtractorAgrees author reviewer := by
  cases author <;> cases reviewer <;>
    simp [adapt, ExtractorAgrees, IndependenceConforms, encodePair, eq_comm]

theorem same_identity_disagrees (identity : String) :
    ∃ row, adapt (.present identity) (.present identity) = some row ∧
      ¬ IndependenceConforms row := by
  simp [adapt, IndependenceConforms, encodePair]

theorem author_absent_cannot_agree (reviewer : AdmittedIdentity) :
    ¬ ∃ row, adapt .absent reviewer = some row ∧ IndependenceConforms row := by
  cases reviewer <;> simp [adapt]

theorem reviewer_absent_cannot_agree (author : AdmittedIdentity) :
    ¬ ∃ row, adapt author .absent = some row ∧ IndependenceConforms row := by
  cases author <;> simp [adapt]

def retainedAuthor : AdmittedIdentity := .present "zai-2"
def retainedReviewer : AdmittedIdentity := .present "zai-3"

theorem retained_pair_agrees :
    ∃ row, adapt retainedAuthor retainedReviewer = some row ∧ IndependenceConforms row := by
  rw [adapt_conforms_iff]
  exact ⟨"zai-2", "zai-3", rfl, rfl, by decide⟩

theorem retained_pair_collapsed_disagrees :
    ∃ row, adapt retainedAuthor retainedAuthor = some row ∧ ¬ IndependenceConforms row := by
  exact same_identity_disagrees "zai-2"

theorem retained_author_missing_cannot_agree :
    ¬ ∃ row, adapt .absent retainedReviewer = some row ∧ IndependenceConforms row := by
  exact author_absent_cannot_agree retainedReviewer

theorem retained_reviewer_missing_cannot_agree :
    ¬ ∃ row, adapt retainedAuthor .absent = some row ∧ IndependenceConforms row := by
  exact reviewer_absent_cannot_agree retainedAuthor

#print axioms adapt_conforms_iff
#print axioms same_identity_disagrees
#print axioms author_absent_cannot_agree
#print axioms reviewer_absent_cannot_agree
#print axioms retained_pair_agrees
#print axioms retained_pair_collapsed_disagrees
#print axioms retained_author_missing_cannot_agree
#print axioms retained_reviewer_missing_cannot_agree

end DarkTower.WarMachine.R20IndependenceRowCorrespondence
