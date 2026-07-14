import Mathlib
import DarkTower.BV
import DarkTower.Fill
import DarkTower.TypedHole

/-!
# The mutating-template cellular update as a DarkTower object

This file models one contextual cell update from
`evolve-sigil-with-mutating-template`.  It follows the implementation order:

1. read the left, center, and right genotype bytes together with the phenotype
   context quadruple;
2. build the four-candidate context template and combine eight allele triples,
   taking the first template match and otherwise applying the center byte's
   local truth-table rule;
3. apply balance mutation to the combined byte;
4. write the resulting genotype byte.

The combine and mutation stages are variation slots.  Each is represented by a
`TypedHole` whose positions are its semantic ports and whose dependent
directions are the fills admissible at that port.  The occupant functions pick
the fills used by this particular dynamic.

Grounding:
* `futon5/notebooks/sci-repro/src/scirepro/mutating_template.clj`;
* `futon5/notebooks/sci-repro/src/scirepro/engine.clj`, mutation mechanism;
* `futon5/256ca.el:971-986,990-1065`.
-/

namespace DarkTower

namespace MetaCAExample

/-- Observable stages of one contextual mutating-template cell update. -/
inductive Stage where
  | readLeftRule
  | readCenterRule
  | readRightRule
  | readPhenotypeContext
  | combine
  | mutate
  | write
  deriving DecidableEq, Repr

/--
The three genotype bytes and phenotype quadruple are independent simultaneous
reads.  Their values feed a serial combine, balance-mutation, and write spine.
-/
def cellUpdate : BV Stage :=
  BV.seq
    (BV.copar (BV.atom Stage.readPhenotypeContext)
      (BV.copar (BV.atom Stage.readLeftRule)
        (BV.copar (BV.atom Stage.readCenterRule) (BV.atom Stage.readRightRule))))
    (BV.seq (BV.atom Stage.combine)
      (BV.seq (BV.atom Stage.mutate) (BV.atom Stage.write)))

/-- The same serial tail with its first association exposed. -/
def updateTailLeft : BV Stage :=
  BV.seq (BV.seq (BV.atom Stage.combine) (BV.atom Stage.mutate))
    (BV.atom Stage.write)

/-- The serial tail as it occurs in `cellUpdate`. -/
def updateTailRight : BV Stage :=
  BV.seq (BV.atom Stage.combine)
    (BV.seq (BV.atom Stage.mutate) (BV.atom Stage.write))

/-- The update tail composes by the existing BV sequence associator. -/
example : BV.Cong updateTailLeft updateTailRight :=
  BV.Cong.seq_assoc (BV.atom Stage.combine) (BV.atom Stage.mutate)
    (BV.atom Stage.write)

/-! ## Combine variation slot -/

/-- Ports that jointly determine the pre-mutation output byte. -/
inductive CombinePort where
  | templateConstruction
  | alleleDecision
  | noMatchFallback
  | outputPacking
  deriving DecidableEq, Repr

/-- Candidate ways to supply the contextual template. -/
inductive TemplateConstructionFill where
  | noTemplate
  | contextQuadrupleFourCandidates
  deriving DecidableEq, Repr

/-- Candidate policies for choosing each output allele. -/
inductive AlleleDecisionFill where
  | firstTemplateMatchElseFallback
  | neighborAgreementElseFallback
  deriving DecidableEq, Repr

/-- Candidate rules used when the contextual template has no match. -/
inductive NoMatchFallbackFill where
  | centerTruthTableLocalRule
  | constantZero
  deriving DecidableEq, Repr

/-- Candidate representations of the eight selected output alleles. -/
inductive OutputPackingFill where
  | eightBitsToRuleByte
  deriving DecidableEq, Repr

/-- The direction family is dependent: each combine port accepts only its fills. -/
def CombineDirection : CombinePort -> Type
  | CombinePort.templateConstruction => TemplateConstructionFill
  | CombinePort.alleleDecision => AlleleDecisionFill
  | CombinePort.noMatchFallback => NoMatchFallbackFill
  | CombinePort.outputPacking => OutputPackingFill

/--
The combine interface is fully fed by this dynamic.  In particular, its
template fill means the ordered candidates
`[actual, flip-all actual, flip-index-1 actual, flip-indices-0-2-3 actual]`.
-/
def combineHole : TypedHole where
  poly :=
    { A := CombinePort
      B := CombineDirection }
  satiety := fun _ => SatietyGrade.canon

/-- The specific combine fills used by the mutating-template dynamic. -/
def mutatingTemplateCombineFill :
    (port : combineHole.poly.A) -> combineHole.holeType port
  | CombinePort.templateConstruction =>
      TemplateConstructionFill.contextQuadrupleFourCandidates
  | CombinePort.alleleDecision =>
      AlleleDecisionFill.firstTemplateMatchElseFallback
  | CombinePort.noMatchFallback =>
      NoMatchFallbackFill.centerTruthTableLocalRule
  | CombinePort.outputPacking =>
      OutputPackingFill.eightBitsToRuleByte

/-- The template-construction port has the intended fill type. -/
example : combineHole.holeType CombinePort.templateConstruction =
    TemplateConstructionFill :=
  rfl

/-- The per-allele decision port has the intended fill type. -/
example : combineHole.holeType CombinePort.alleleDecision = AlleleDecisionFill :=
  rfl

/-- The fallback port has the intended fill type. -/
example : combineHole.holeType CombinePort.noMatchFallback = NoMatchFallbackFill :=
  rfl

/-- The output port has the intended fill type. -/
example : combineHole.holeType CombinePort.outputPacking = OutputPackingFill :=
  rfl

/-- This dynamic occupies the template port with the contextual four-candidate fill. -/
example : mutatingTemplateCombineFill CombinePort.templateConstruction =
    TemplateConstructionFill.contextQuadrupleFourCandidates :=
  rfl

/-- A template miss is filled by the center genotype's local rule lookup. -/
example : mutatingTemplateCombineFill CombinePort.noMatchFallback =
    NoMatchFallbackFill.centerTruthTableLocalRule :=
  rfl

/-- Every combine port is fed by the reproduced dynamic. -/
example (port : CombinePort) : combineHole.satiety port = SatietyGrade.canon :=
  rfl

/-! ## Balance-mutation variation slot -/

/-- Ports that jointly determine the post-combine balance mutation. -/
inductive MutatePort where
  | populationTest
  | probabilityGate
  | bitSelection
  | selectedEffect
  | otherwiseEffect
  deriving DecidableEq, Repr

/-- Candidate tests deciding whether a byte is eligible for mutation. -/
inductive PopulationTestFill where
  | outsideTwoThroughSixOnes
  | unconditional
  deriving DecidableEq, Repr

/-- Candidate random gates for an eligible mutation. -/
inductive ProbabilityGateFill where
  | oneInTwenty
  | always
  deriving DecidableEq, Repr

/-- Candidate policies for selecting a bit to change. -/
inductive BitSelectionFill where
  | randomMajorityBitAfterFullShuffle
  | uniformAllele
  deriving DecidableEq, Repr

/-- Candidate effects applied to a rule byte. -/
inductive MutationEffectFill where
  | flipExactlyOneSelectedBit
  | leaveUnchanged
  deriving DecidableEq, Repr

/-- The direction family is dependent: each mutation port accepts only its fills. -/
def MutateDirection : MutatePort -> Type
  | MutatePort.populationTest => PopulationTestFill
  | MutatePort.probabilityGate => ProbabilityGateFill
  | MutatePort.bitSelection => BitSelectionFill
  | MutatePort.selectedEffect => MutationEffectFill
  | MutatePort.otherwiseEffect => MutationEffectFill

/--
The mutation interface is fully fed.  `outsideTwoThroughSixOnes` means more
than six ones or fewer than two ones.  Only such bytes draw the one-in-twenty
gate; a successful gate fully shuffles positions carrying the majority value,
selects the last shuffled position, and flips exactly that bit.  Every other
path returns the combined byte unchanged.
-/
def mutateHole : TypedHole where
  poly :=
    { A := MutatePort
      B := MutateDirection }
  satiety := fun _ => SatietyGrade.canon

/-- The specific mutation fills used by `balance-mutation`. -/
def balanceMutationFill :
    (port : mutateHole.poly.A) -> mutateHole.holeType port
  | MutatePort.populationTest => PopulationTestFill.outsideTwoThroughSixOnes
  | MutatePort.probabilityGate => ProbabilityGateFill.oneInTwenty
  | MutatePort.bitSelection => BitSelectionFill.randomMajorityBitAfterFullShuffle
  | MutatePort.selectedEffect => MutationEffectFill.flipExactlyOneSelectedBit
  | MutatePort.otherwiseEffect => MutationEffectFill.leaveUnchanged

/-- The population-test port has the intended fill type. -/
example : mutateHole.holeType MutatePort.populationTest = PopulationTestFill :=
  rfl

/-- The random-gate port has the intended fill type. -/
example : mutateHole.holeType MutatePort.probabilityGate = ProbabilityGateFill :=
  rfl

/-- The bit-selection port has the intended fill type. -/
example : mutateHole.holeType MutatePort.bitSelection = BitSelectionFill :=
  rfl

/-- The two effect ports share the rule-byte effect type. -/
example : mutateHole.holeType MutatePort.selectedEffect = MutationEffectFill :=
  rfl

/-- This dynamic occupies the probability port with the exact 1/20 gate. -/
example : balanceMutationFill MutatePort.probabilityGate =
    ProbabilityGateFill.oneInTwenty :=
  rfl

/-- This dynamic occupies the selection port with the implementation's full shuffle. -/
example : balanceMutationFill MutatePort.bitSelection =
    BitSelectionFill.randomMajorityBitAfterFullShuffle :=
  rfl

/-- Every balance-mutation port is fed by the reproduced dynamic. -/
example (port : MutatePort) : mutateHole.satiety port = SatietyGrade.canon :=
  rfl

/--
Nested polynomial substitution records the two serial variation slots at the
object level.  BV records their operational order separately in `cellUpdate`.
-/
def twoSlotInterface := Fill.fill mutateHole.poly combineHole.poly

/-!
## VERDICT: the current machinery is sufficient for this probe

The mutating-template update is a feed-forward two-slot diagram.  The combine
fill consumes the current neighborhood and phenotype context exactly once; its
output is then consumed by the balance-mutation fill, and the result is written.
There is no edge from mutation or write back into combine during the same cell
update.  Iteration across CA generations is external iteration of this whole
one-step object, not mid-diagram feedback.

Therefore the skeleton composes under the current machinery: `BV.seq` gives
the ordered spine, `BV.copar` groups simultaneous reads,
`BV.Cong.seq_assoc` witnesses harmless reassociation, and `Fill.fill` gives the
nested polynomial substitution for the two slots.  If a third serial slot is
added, `Fill.assocEquiv` is the specific existing equivalence needed to compare
the two nestings.

The deferred Roman coend layer described in `Comb.lean` is not needed yet.  It
would become necessary only if the next construction exposes independently
addressable holes in the middle of one shared diagram, or feeds a later output
back into an earlier open port.  At that point the missing piece is an n-hole
open-diagram type together with plugging and feedback composition; the current
`Comb.comp` is only sequential dependent-lens composition and does not provide
those operations.
-/

end MetaCAExample

end DarkTower
