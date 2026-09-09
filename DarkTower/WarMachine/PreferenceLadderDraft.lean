import DarkTower.WarMachine.Holes

/-!
# Preference-ladder draft

This standalone module records the portions of the Item 17 preference ladder
that are typeable before the canonical vertex reconciliation.  It deliberately
does not alter `Holes.lean`.
-/

namespace DarkTower.WarMachine.PreferenceLadderDraft

open DarkTower.WarMachine.Holes

universe u v w x

noncomputable section

/-- An observation at a pragmatic vertex.  The distinguished evidence vertex
is excluded by the proof field. `Vertex` is canonical per Item 16/18b;
the earlier people/money/organisations reading is the recorded specialization. -/
structure PragmaticObservation (V : Type u) (evidence : V)
    (Obs : V → Type v) where
  vertex : V
  pragmatic : vertex ≠ evidence
  observation : Obs vertex

/-- One carrier shared by intermediate observation preferences and terminal
disposition preferences. -/
inductive LadderOutcome (Observation : Type u) (OutcomeKind : Type v) where
  | observation : Observation → LadderOutcome Observation OutcomeKind
  | terminal : OutcomeKind → LadderOutcome Observation OutcomeKind

/-- `Cτ` is one time-indexed family over a common ladder carrier.  The final
row is constrained to terminal outcome kinds, so processual and terminal C are
two positions in one family rather than unrelated types. -/
structure PreferenceFamily (Observation : Type u) (OutcomeKind : Type v)
    (horizon : Nat) where
  Cτ : Fin (horizon + 1) →
    ProbabilityKernel Unit (LadderOutcome Observation OutcomeKind)
  terminalSupport : ∀ o ∈ (Cτ ⟨horizon, Nat.lt_succ_self horizon⟩).support (),
    ∃ d, o = .terminal d
  terminalMassZero : ∀ o,
    (Cτ ⟨horizon, Nat.lt_succ_self horizon⟩).mass () (.observation o) = 0

/-- A finitely supported normalized conditional `P(d|o)`.  `zeroSupport`
names supported outcomes whose mass is exactly zero; hence smoothing cannot be
represented by silently dropping those outcomes from support. -/
structure DispositionKernel (Observation : Type u) (OutcomeKind : Type v)
    extends ProbabilityKernel Observation OutcomeKind where
  zeroSupport : Observation → List OutcomeKind
  zeroSupport_spec : ∀ o d,
    d ∈ zeroSupport o ↔ d ∈ support o ∧ mass o d = 0

/-- The bridge identity's right-hand side:
`Q(d|π) = Σ_o P(d|o) Q(o|π)`. -/
def dispositionPredictiveMass {Policy Observation OutcomeKind : Type*}
    (P : DispositionKernel Observation OutcomeKind)
    (Q : ProbabilityKernel Policy Observation) (π : Policy) (d : OutcomeKind) : ℝ :=
  (Q.support π).map (fun o => P.mass o d * Q.mass π o) |>.sum

/-- Prop-level statement of the bridge identity for any proposed predictive
disposition mass. -/
def SatisfiesDispositionBridge {Policy Observation OutcomeKind : Type*}
    (P : DispositionKernel Observation OutcomeKind)
    (Q : ProbabilityKernel Policy Observation)
    (Qd : Policy → OutcomeKind → ℝ) : Prop :=
  ∀ π d, Qd π d = dispositionPredictiveMass P Q π d

/-- `KL[Q(d|π) || C_terminal]` on an explicit finite disposition support.
The positivity premise is exposed, as in `predictiveOutcomeRisk` at
`Holes.lean:6998-7005`; zero preferred mass is not smoothed away. -/
def dispositionRisk {Policy OutcomeKind : Type*}
    (support : Policy → List OutcomeKind)
    (Qd : Policy → OutcomeKind → ℝ)
    (Cterminal : ProbabilityKernel Unit OutcomeKind)
    (_positivePreference : ∀ π d, d ∈ support π → 0 < Cterminal.mass () d)
    (π : Policy) : ℝ :=
  (support π).map
    (fun d => Qd π d * Real.log (Qd π d / Cterminal.mass () d)) |>.sum

/-- The measured single-support limitation as a law shape: when every
observation row of `P(d|o)` is the same point mass, disposition risk must be
constant across policies.  Its empirical discharge (the measured `ln 2`
example) belongs to the executable record-fitted kernel, not this carrier. -/
def SingleSupportRiskIsPolicyConstant {Policy Observation OutcomeKind : Type*}
    (P : DispositionKernel Observation OutcomeKind)
    (Q : ProbabilityKernel Policy Observation)
    (support : Policy → List OutcomeKind)
    (Cterminal : ProbabilityKernel Unit OutcomeKind)
    (positivePreference : ∀ π d, d ∈ support π → 0 < Cterminal.mass () d) : Prop :=
  (∃ d, (∀ o, P.support o = [d] ∧ P.mass o d = 1 ∧
                  ∀ d', d' ≠ d → P.mass o d' = 0) ∧
          ∀ π, support π = [d]) →
    ∀ π ρ,
      dispositionRisk support (dispositionPredictiveMass P Q)
          Cterminal positivePreference π =
        dispositionRisk support (dispositionPredictiveMass P Q)
          Cterminal positivePreference ρ

/-- The evidential outcome facet distinguishes merely working from working
with a communicable witness, without enumerating witness media. -/
structure EvidentialFacet (Witness : Type u) where
  works : Prop
  communicableWitness : Option Witness

/-- Outcome kinds may carry arbitrary pragmatic facets together with the
evidential artifact facet.  Neither the outcome-kind vocabulary nor the
witness carrier is fixed here. -/
structure OutcomeFacets (PragmaticFacet : Type u) (Witness : Type v) where
  pragmatic : PragmaticFacet
  evidential : EvidentialFacet Witness

/-!
## Proposed replacement text for Joe's `C`-hole doc marker

`DEFERRAL UNDER ORGANIZED DISCOVERY · owner: RULINGS-walkthrough-2026-09-08
Item 17 · evidence: C591-C-as-calculation-proposal.md · Preferred observations
form a time-indexed Cτ family whose terminal member is the ruled outcome-kind
distribution.  The disposition bridge P(d|o) is to be fitted from recorded
observation-to-disposition evidence, and proposed preferences retain provenance
until an operator ruling fixes them.  This is an active discovery obligation,
not a deliberate implementation refusal.`

This text is only a proposal for Joe's sitting.  The existing marker at
`Holes.lean:152-153` is unchanged by this draft.
-/

end

end DarkTower.WarMachine.PreferenceLadderDraft
