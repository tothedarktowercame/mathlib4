import DarkTower.WarMachine.MachineModelSpec

namespace DarkTower.WarMachine.MachineForwardModelWitness

open DarkTower.WarMachine.MachineModelSpec

inductive O where
  | abstained | agentUnavailable | artifactOnly | buildFailed | cancelled
  | dispatchFailed | groundedChange | groundedNoChange | guardrailRefusal
  | incomplete | noSelection | substrateUnavailable
  deriving DecidableEq

def allO : List O := [.abstained, .agentUnavailable, .artifactOnly, .buildFailed,
  .cancelled, .dispatchFailed, .groundedChange, .groundedNoChange,
  .guardrailRefusal, .incomplete, .noSelection, .substrateUnavailable]

inductive S where | addressed | falsified | foreclosed | refined | reopened | spawned | strengthened
  deriving DecidableEq

def allS : List S := [.addressed, .falsified, .foreclosed, .refined, .reopened, .spawned, .strengthened]

def advanceTwiceMass : O → ℚ
  | .abstained => (3442556320081687 : ℚ) / 36028797018963968
  | .agentUnavailable => (2683201850079625 : ℚ) / 36028797018963968
  | .artifactOnly => (5982758850052747 : ℚ) / 36028797018963968
  | .buildFailed => 0
  | .cancelled => (7589757911525539 : ℚ) / 72057594037927936
  | .dispatchFailed => 0
  | .groundedChange => (40250802085974281 : ℚ) / 72057594037927936
  | .groundedNoChange => 0
  | .guardrailRefusal => 0
  | .incomplete => 0
  | .noSelection => 0
  | .substrateUnavailable => 0

def cascadeMass : O → ℚ
  | .abstained => 0
  | .agentUnavailable => 0
  | .artifactOnly => (4712657585067217 : ℚ) / 18014398509481984
  | .buildFailed => (7589757911525539 : ℚ) / 72057594037927936
  | .cancelled => (12956161611684789 : ℚ) / 72057594037927936
  | .dispatchFailed => 0
  | .groundedChange => (16330522087224371 : ℚ) / 36028797018963968
  | .groundedNoChange => 0
  | .guardrailRefusal => 0
  | .incomplete => 0
  | .noSelection => 0
  | .substrateUnavailable => 0

def advanceTwiceTerminal : S → ℚ
  | .addressed => (3442556320081687 : ℚ) / 36028797018963968
  | .falsified => (2683201850079625 : ℚ) / 36028797018963968
  | .foreclosed => (5982758850052747 : ℚ) / 36028797018963968
  | .refined => 0
  | .reopened => (7589757911525539 : ℚ) / 72057594037927936
  | .spawned => 0
  | .strengthened => (40250802085974281 : ℚ) / 72057594037927936

def cascadeTerminal : S → ℚ
  | .addressed => 0
  | .falsified => 0
  | .foreclosed => (4712657585067217 : ℚ) / 18014398509481984
  | .refined => (7589757911525539 : ℚ) / 72057594037927936
  | .reopened => (12956161611684789 : ℚ) / 72057594037927936
  | .spawned => 0
  | .strengthened => (16330522087224371 : ℚ) / 36028797018963968

def positionalA : S → O
  | .addressed => .abstained
  | .falsified => .agentUnavailable
  | .foreclosed => .artifactOnly
  | .refined => .buildFailed
  | .reopened => .cancelled
  | .spawned => .dispatchFailed
  | .strengthened => .groundedChange

def compose (q : S → ℚ) (o : O) : ℚ :=
  (allS.map fun s => q s * if positionalA s = o then 1 else 0).sum

def advanceTwiceRow : FloatCarriedRow O where
  support := allO
  mass := advanceTwiceMass
  nonnegative := by intro o; cases o <;> norm_num [advanceTwiceMass]
  nearNormalised := by norm_num [allO, advanceTwiceMass, floatRowBound]

def cascadeRow : FloatCarriedRow O where
  support := allO
  mass := cascadeMass
  nonnegative := by intro o; cases o <;> norm_num [cascadeMass]
  nearNormalised := by norm_num [allO, cascadeMass, floatRowBound]

def advanceTwiceRepeatRow : FloatCarriedRow O := advanceTwiceRow

theorem advanceTwiceComposition (o : O) : advanceTwiceMass o = compose advanceTwiceTerminal o := by
  cases o <;> simp [advanceTwiceMass, advanceTwiceTerminal, compose, allS, positionalA]

theorem cascadeComposition (o : O) : cascadeMass o = compose cascadeTerminal o := by
  cases o <;> simp [cascadeMass, cascadeTerminal, compose, allS, positionalA]

theorem repeatedComposition (o : O) : advanceTwiceRepeatRow.mass o = advanceTwiceRow.mass o := rfl

theorem inheritedExcess :
    (allO.map advanceTwiceMass).sum - 1 = (1 : ℚ) / 36028797018963968 ∧
    (allO.map cascadeMass).sum - 1 = (1 : ℚ) / 36028797018963968 := by
  norm_num [allO, advanceTwiceMass, cascadeMass]

end DarkTower.WarMachine.MachineForwardModelWitness
