import Mathlib
import DarkTower.BV
import DarkTower.Fill
import DarkTower.TypedHole

/-!
# Reproduced MetaCA dynamics as DarkTower objects

This file gives a shared basis for reproduced contextual cell updates.  Both
`evolve-sigil-with-mutating-template` and
`evolve-sigil-with-blending-baldwin` follow the implementation order:

1. read the left, center, and right genotype bytes together with the phenotype
   context quadruple;
2. combine eight allele triples using the selected policy: ordered contextual
   template matching or predecessor/successor agreement, with the center
   byte's local truth-table rule as fallback;
3. apply the selected mutation policy to the combined byte;
4. write the resulting genotype byte.

The combine and mutation stages are shared variation slots.  Each is
represented by a `TypedHole` whose positions are its semantic ports and whose
dependent directions are the fills admissible at that port.  The occupant
functions pick the fills used by each reproduced dynamic.

Grounding:
* `futon5/notebooks/sci-repro/src/scirepro/mutating_template.clj`;
* `futon5/notebooks/sci-repro/src/scirepro/baldwin.clj`;
* `futon5/notebooks/sci-repro/src/scirepro/engine.clj`, mutation mechanism;
* `futon5/256ca.el:571-591,634-686,971-986,990-1065`.
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
reads.  Their values feed a serial combine, selected mutation, and write spine.
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

/-! ## Shared mutation variation slot -/

/-- Ports that jointly determine the selected post-combine mutation. -/
inductive MutatePort where
  | populationTest
  | probabilityGate
  | bitSelection
  | selectedEffect
  | otherwiseEffect
  deriving DecidableEq, Repr

/-- Candidate conditions deciding whether and how a byte is eligible for mutation. -/
inductive PopulationTestFill where
  | outsideTwoThroughSixOnes
  | contextPresentWithFirstThreeMatchCount
  | unconditional
  deriving DecidableEq, Repr

/-- Candidate random gates for an eligible mutation. -/
inductive ProbabilityGateFill where
  | oneInTwenty
  | oneInThree
  | always
  deriving DecidableEq, Repr

/-- Candidate policies for selecting a bit to change. -/
inductive BitSelectionFill where
  | randomMajorityBitAfterFullShuffle
  | uniformAllele
  | uniformPositionWithReplacementPerFlip
  deriving DecidableEq, Repr

/-- Candidate effects applied to a rule byte. -/
inductive MutationEffectFill where
  | flipExactlyOneSelectedBit
  | flipContextMatchCountPlusTwoBits
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
The shared mutation interface is fully fed by each occupant.  For the balance
occupant, `outsideTwoThroughSixOnes` means more than six ones or fewer than two
ones.  Only such bytes draw the one-in-twenty gate; a successful gate fully
shuffles positions carrying the majority value, selects the last shuffled
position, and flips exactly that bit.  Every other path returns the combined
byte unchanged.
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

/-! ## Baldwin occupant on the shared basis -/

/--
Baldwin reuses the existing combine directions: there is no contextual
template; equal predecessor/successor bits are copied, and unequal neighbors
fall back to the center genotype's local truth-table rule.
-/
def baldwinCombineFill :
    (port : combineHole.poly.A) -> combineHole.holeType port
  | CombinePort.templateConstruction => TemplateConstructionFill.noTemplate
  | CombinePort.alleleDecision => AlleleDecisionFill.neighborAgreementElseFallback
  | CombinePort.noMatchFallback => NoMatchFallbackFill.centerTruthTableLocalRule
  | CombinePort.outputPacking => OutputPackingFill.eightBitsToRuleByte

/-- Baldwin occupies the shared template port with no template. -/
example : baldwinCombineFill CombinePort.templateConstruction =
    TemplateConstructionFill.noTemplate :=
  rfl

/-- Baldwin copies an agreed predecessor/successor bit before considering fallback. -/
example : baldwinCombineFill CombinePort.alleleDecision =
    AlleleDecisionFill.neighborAgreementElseFallback :=
  rfl

/-- Unequal Baldwin neighbors use the same center local-rule fill. -/
example : baldwinCombineFill CombinePort.noMatchFallback =
    NoMatchFallbackFill.centerTruthTableLocalRule :=
  rfl

/--
The Baldwin mutation occupant requires a nonempty context, draws the random
gate modulo three, and acts only when that draw is zero.  It counts positions
zero through two whose phenotype bit equals position three, adds two, then
performs that many sequential flips.  Every flip draws a fresh uniform
position in `0..7`; positions are sampled with replacement, so repeated draws
can cancel earlier flips.  A missing context consumes no random draw and leaves
the combined byte unchanged.
-/
def baldwinMutationFill :
    (port : mutateHole.poly.A) -> mutateHole.holeType port
  | MutatePort.populationTest =>
      PopulationTestFill.contextPresentWithFirstThreeMatchCount
  | MutatePort.probabilityGate => ProbabilityGateFill.oneInThree
  | MutatePort.bitSelection => BitSelectionFill.uniformPositionWithReplacementPerFlip
  | MutatePort.selectedEffect => MutationEffectFill.flipContextMatchCountPlusTwoBits
  | MutatePort.otherwiseEffect => MutationEffectFill.leaveUnchanged

/-- Baldwin's condition records both context presence and the exact match count. -/
example : baldwinMutationFill MutatePort.populationTest =
    PopulationTestFill.contextPresentWithFirstThreeMatchCount :=
  rfl

/-- Baldwin uses `(random 3) < 1`, represented by the one-in-three fill. -/
example : baldwinMutationFill MutatePort.probabilityGate =
    ProbabilityGateFill.oneInThree :=
  rfl

/-- `mutate-rule-n` draws each flip position uniformly and with replacement. -/
example : baldwinMutationFill MutatePort.bitSelection =
    BitSelectionFill.uniformPositionWithReplacementPerFlip :=
  rfl

/-- Baldwin performs exactly the context-match count plus two flips. -/
example : baldwinMutationFill MutatePort.selectedEffect =
    MutationEffectFill.flipContextMatchCountPlusTwoBits :=
  rfl

/-- Both policies leave the byte unchanged when their respective gate does not act. -/
example : baldwinMutationFill MutatePort.otherwiseEffect =
    balanceMutationFill MutatePort.otherwiseEffect :=
  rfl

/-- A reproduced dynamic is an occupant of the two shared variation holes. -/
structure DynamicOccupant where
  /-- The dynamic's fill at every combine port. -/
  combineFill : (port : combineHole.poly.A) -> combineHole.holeType port
  /-- The dynamic's fill at every mutation port. -/
  mutateFill : (port : mutateHole.poly.A) -> mutateHole.holeType port

/-- The mutating-template dynamic occupies the shared skeleton and holes. -/
def mutatingTemplateOccupant : DynamicOccupant where
  combineFill := mutatingTemplateCombineFill
  mutateFill := balanceMutationFill

/-- The Baldwin dynamic occupies the same shared skeleton and holes. -/
def baldwinOccupant : DynamicOccupant where
  combineFill := baldwinCombineFill
  mutateFill := baldwinMutationFill

/-- The accepted mutating-template occupant retains its four-candidate template. -/
example : mutatingTemplateOccupant.combineFill CombinePort.templateConstruction =
    TemplateConstructionFill.contextQuadrupleFourCandidates :=
  rfl

/-- The second occupant selects Baldwin's distinct random gate on the same interface. -/
example : baldwinOccupant.mutateFill MutatePort.probabilityGate =
    ProbabilityGateFill.oneInThree :=
  rfl

/-!
The common `cellUpdate`, `combineHole`, and `mutateHole` now host two reproduced
dynamics as distinct `DynamicOccupant` values.  This is a shared fill store for
later work; it does not compose or interpolate the occupants.
-/

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
