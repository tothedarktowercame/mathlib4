import DarkTower.WarMachine.Holes

namespace DarkTower.WarMachine.F10RuledCarrier

open Holes

/-- The corrected ruled organisation-outcome vocabulary.  The authority is
`futon2:src/futon2/aif/full_loop_cohort.clj:31-33`, enforced at
`futon2:src/futon2/aif/full_loop_cohort.clj:317` and
`futon2:src/futon2/tripwire.clj:189`.  The twelve-member correction is recorded
at `futon2:holes/labs/wm-contract/aif-equations.edn:214` and explained by
`futon2:holes/labs/wm-contract/C574-F10-disposition-enumeration.md:187`: the
earlier fourteen counted literal syntax, not the vocabulary. -/
inductive FlightDisposition where
  | groundedChange | groundedNoChange | artifactOnly | abstained
  | noSelection | agentUnavailable | guardrailRefusal | dispatchFailed
  | buildFailed | substrateUnavailable | incomplete | cancelled
  deriving DecidableEq, Repr

/-- Declaration-order enumeration, following `Channel.all` at
`mathlib4:DarkTower/WarMachine/Holes.lean:1238-1241`. -/
def FlightDisposition.all : List FlightDisposition :=
  [.groundedChange, .groundedNoChange, .artifactOnly, .abstained,
   .noSelection, .agentUnavailable, .guardrailRefusal, .dispatchFailed,
   .buildFailed, .substrateUnavailable, .incomplete, .cancelled]

theorem FlightDisposition.mem_all (d : FlightDisposition) : d ∈ FlightDisposition.all := by
  rcases d <;> simp [FlightDisposition.all]

/-- Named-empty people observation slot.  The four vertices are recorded at
`futon2:holes/problems/P-validated-R5.md:116`; no people outcome carrier is
attested for this ruled C. -/
abbrev PeopleObservation := Empty

/-- Named-empty money observation slot.  The machine has no money vertex of
its own (that is VSAT's), as recorded at
`futon2:holes/problems/P-validated-R5.md:129-131`. -/
abbrev MoneyObservation := Empty

/-- Named-empty evidence carrier used only by the seed.  The evidence
enumeration is owed: the only source mention is prose at
`futon2:src/futon2/aif/arguing_worlds.clj:219`, while the epistemic-validity
region extension is recorded at
`futon2:holes/labs/wm-contract/aif-equations.edn:211`. -/
abbrev SeedEvidenceObservation := Empty

/-- Ruled tagged observation family, polymorphic in the deliberately unruled
evidence observation carrier. -/
def Obs (EvidenceObs : Type) : Vertex → Type
  | .people => PeopleObservation
  | .money => MoneyObservation
  | .organisations => FlightDisposition
  | .evidence => EvidenceObs

abbrev SeedObs := Obs SeedEvidenceObservation

def organisationOutcome (d : FlightDisposition) : Outcome SeedObs :=
  ⟨.organisations, d⟩

/-- The five dispositions observed at
`futon2:holes/labs/wm-contract/runs/D1-evidence/kl-worked-example.edn:5`. -/
def observedDispositions : List FlightDisposition :=
  [.agentUnavailable, .buildFailed, .groundedChange, .incomplete, .noSelection]

/-- The seven named zero-mass organisation outcomes: the ruled vocabulary less
the five observed dispositions. -/
def namedZeroDispositions : List FlightDisposition :=
  [.groundedNoChange, .artifactOnly, .abstained, .guardrailRefusal,
   .dispatchFailed, .substrateUnavailable, .cancelled]

/-- D3's named-empty `C_ser` occasion region (an anomaly on the board, not an
update) is kept inside organisation support, without new constructors; see
`futon2:holes/labs/wm-contract/C537-serendipity-shapes-C.md:49-59`. -/
def serendipityOccasionSupport : List FlightDisposition := []

/-! `C_int` remains outside this tagged sum: it is tick-grain channel
proprioception at `futon2:src/futon2/aif/preferences.clj:9-24`. -/

/-- One preference distribution over the tagged sum.  Its masses transcribe
`:C-seeded` at
`futon2:holes/labs/wm-contract/runs/D1-evidence/kl-worked-example.edn:11`.
That record explicitly says the seed illustrates a registry seed and is not a
ruling (`futon2:holes/labs/wm-contract/runs/D1-evidence/kl-worked-example.edn:15`). -/
noncomputable def seed : PreferenceDistribution SeedObs where
  support := fun _ => FlightDisposition.all.map organisationOutcome
  mass := fun _ o => match o with
    | ⟨.organisations, .groundedChange⟩ => 1 / 2
    | ⟨.organisations, .agentUnavailable⟩ => 1 / 8
    | ⟨.organisations, .buildFailed⟩ => 1 / 8
    | ⟨.organisations, .incomplete⟩ => 1 / 8
    | ⟨.organisations, .noSelection⟩ => 1 / 8
    | ⟨.organisations, .groundedNoChange⟩ => 0
    | ⟨.organisations, .artifactOnly⟩ => 0
    | ⟨.organisations, .abstained⟩ => 0
    | ⟨.organisations, .guardrailRefusal⟩ => 0
    | ⟨.organisations, .dispatchFailed⟩ => 0
    | ⟨.organisations, .substrateUnavailable⟩ => 0
    | ⟨.organisations, .cancelled⟩ => 0
    | _ => 0
  nonnegative := by intro _ o; rcases o with ⟨v, o⟩; cases v <;> cases o <;> norm_num
  normalised := by intro _; norm_num [FlightDisposition.all, organisationOutcome]

theorem seedMass_zero_of_mem_namedZeros (d : FlightDisposition)
    (hd : d ∈ namedZeroDispositions) : seed.mass () (organisationOutcome d) = 0 := by
  rcases d <;> simp_all [namedZeroDispositions, seed, organisationOutcome]

theorem seedMass_pos_of_mem_observed (d : FlightDisposition)
    (hd : d ∈ observedDispositions) : 0 < seed.mass () (organisationOutcome d) := by
  rcases d <;> simp_all [observedDispositions, seed, organisationOutcome]

/-- The exact side-condition consumed by `predictiveOutcomeRisk` at
`mathlib4:DarkTower/WarMachine/Holes.lean:6995`. -/
def PositivePreferenceOnSupport {PolicyIndex : Type*} (Q : PredictiveOutcomeKernel PolicyIndex SeedObs)
    (Cdist : PreferenceDistribution SeedObs) : Prop :=
  ∀ π o, o ∈ Q.support π → 0 < Cdist.mass () o

/-- The seed meets the real-valued risk side-condition exactly when predictive
support avoids all seven named zeros.  This leaves seven live obligations on a
future `Q`; it does not manufacture one. -/
theorem seed_positivePreference_iff_support_avoids_namedZeros
    {PolicyIndex : Type*} (Q : PredictiveOutcomeKernel PolicyIndex SeedObs) :
    PositivePreferenceOnSupport Q seed ↔
      ∀ π d, organisationOutcome d ∈ Q.support π → d ∉ namedZeroDispositions := by
  constructor
  · intro h π d hd hz
    have hp := h π (organisationOutcome d) hd
    rw [seedMass_zero_of_mem_namedZeros d hz] at hp
    exact (lt_irrefl 0 hp)
  · intro h π o ho
    rcases o with ⟨v, o⟩
    cases v with
    | people => exact Empty.elim o
    | money => exact Empty.elim o
    | evidence => exact Empty.elim o
    | organisations =>
        have hn := h π o ho
        rcases o <;> simp_all [namedZeroDispositions, seed, organisationOutcome]

/-- The staged carrier exists without amending `Holes.lean`, following the
two-phase precedent at `mathlib4:DarkTower/WarMachine/F12RuledCarrier.lean:66-70`. -/
theorem exists_ruledPreferenceDistribution : ∃ _ : PreferenceDistribution SeedObs, True :=
  ⟨seed, trivial⟩

end DarkTower.WarMachine.F10RuledCarrier
