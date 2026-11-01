import DarkTower.WarMachine.Requirements

/-! Computable selection carriers, separate from the projector's assertions.
Pins are opaque identities: this checks their presence, not cryptographic authenticity.
The small fixture uses exact rounded witness scores, not the full real-data witness.
`grounded` checks G1–G4; minimisation and the other run requirements remain in Requirements.
The DarkTower library glob includes this module automatically.
-/
namespace DarkTower.WarMachine.SelectionGrounding

abbrev Id := Requirements.Id

structure FieldFact where
  ready : Bool
  cone : ℕ
  unblocks : ℕ
  pin : Id
  deriving DecidableEq, Repr

inductive FieldEntry where
  | fact (task : Id) (f : FieldFact)
  | excluded (task : Id) (reason pin : Id)
  deriving DecidableEq, Repr

inductive Step where
  | readyGate | byCone | byUnblocks
  | named (step : Id)
  deriving DecidableEq, Repr

inductive Relation where
  | focus | associated | usefulElsewhere | unrelated | unknown
  deriving DecidableEq, Repr

structure Terms where
  risk : ℚ
  ambiguity : ℚ
  novelty : ℚ
  deriving DecidableEq, Repr

structure GroundedPolicy where
  cascade : Id
  steps : List Step
  pick : Option Id
  reach : ℚ
  relation : Relation
  terms : Terms
  g : ℚ
  deriving DecidableEq, Repr

structure Grounding where
  enumerated : Finset Id
  field : List FieldEntry
  policies : List GroundedPolicy
  abstention : Terms × ℚ
  chosen : Id
  deriving DecidableEq

-- This toolchain's Finset Repr is unsafe; use a deterministic computable list.
instance : Repr Grounding where
  reprPrec g n := reprPrec (g.enumerated.sort (· ≤ ·), g.field, g.policies,
    g.abstention, g.chosen) n

def applyStep (field : List (Id × FieldFact)) : Step → Option (List (Id × FieldFact))
  | .readyGate => some (field.filter fun x => x.2.ready)
  | .byCone => some (field.insertionSort fun a b => b.2.cone ≤ a.2.cone)
  | .byUnblocks => some (field.insertionSort fun a b => b.2.unblocks ≤ a.2.unblocks)
  | .named _ => none

def candidates (g : Grounding) : List (Id × FieldFact) :=
  g.field.filterMap fun e => match e with
    | .fact t f => some (t, f)
    | .excluded _ _ _ => none

def recomputedPick (g : Grounding) (p : GroundedPolicy) : Option (Option Id) :=
  (p.steps.foldl (fun acc step => acc.bind fun xs => applyStep xs step)
    (some (candidates g))).map fun xs => xs.head?.map Prod.fst

def fieldTask : FieldEntry → Id
  | .fact t _ => t
  | .excluded t _ _ => t

def fieldConsidered (g : Grounding) : Bool :=
  decide ((g.field.map fieldTask).Nodup ∧
    (g.field.map fieldTask).toFinset = g.enumerated) &&
  g.field.all (fun e => match e with
    | .fact _ f => decide (f.pin ≠ 0)
    | .excluded _ reason pin => decide (reason ≠ 0 ∧ pin ≠ 0))

/-- `none` means unverifiable, even if a different policy has a detectable mismatch. -/
def prioritised (g : Grounding) : Option Bool :=
  if g.policies.any (fun p => (recomputedPick g p).isNone) then none
  else some (g.policies.all fun p => decide (recomputedPick g p = some p.pick))

def Terms.score (t : Terms) : ℚ := t.risk + t.ambiguity - t.novelty

def scoredFromTerms (g : Grounding) : Bool :=
  g.policies.all (fun p => decide (p.g = p.terms.score ∧ 0 ≤ p.reach ∧ p.reach ≤ 1 ∧
    (p.pick.isSome = true → p.relation ≠ .unknown))) &&
  decide (g.abstention.2 = g.abstention.1.score)

def agreesWithRunFacts (g : Grounding) (r : Requirements.RunFacts) : Bool :=
  (match r.currentDecision with
    | .pick _ c => decide (g.chosen = c)
    | _ => false) &&
  decide ((g.policies.map fun p => (p.cascade, p.g)).toFinset = r.policyG.toFinset ∧
    g.abstention.2 = r.abstentionG ∧ g.enumerated = r.enumeratedTasks)

def grounded (g : Grounding) (r : Requirements.RunFacts) : Bool :=
  fieldConsidered g && (prioritised g == some true) && scoredFromTerms g &&
    agreesWithRunFacts g r

/-- Concrete fixture: the two stable ordering compositions select different tasks. -/
def small : Grounding where
  enumerated := {1, 2, 3, 4, 5}
  field := [.fact 1 ⟨true, 9, 1, 101⟩, .fact 2 ⟨true, 4, 8, 102⟩,
    .fact 3 ⟨true, 4, 8, 103⟩, .fact 4 ⟨false, 99, 99, 104⟩, .excluded 5 7 105]
  policies := [
    ⟨70000, [.readyGate, .byCone, .byUnblocks], some 2, 1/2, .associated,
      ⟨3, 5041/10000, 1/50⟩, 34841/10000⟩,
    ⟨70001, [.readyGate, .byUnblocks, .byCone], some 1, 1/2, .associated,
      ⟨5/2, 5149/10000, 1/50⟩, 29949/10000⟩,
    ⟨70002, [.readyGate], some 1, 1/2, .associated,
      ⟨3, 5041/10000, 1/50⟩, 34841/10000⟩]
  abstention := (⟨4, 7875/10000, 0⟩, 47875/10000)
  chosen := 70001

def smallRun : Requirements.RunFacts :=
  { Requirements.selectionGood with
    currentDecision := .pick 1 70001
    policyG := [(70000, 34841/10000), (70001, 29949/10000), (70002, 34841/10000)]
    abstentionG := 47875/10000
    enumeratedTasks := small.enumerated }

theorem small_witness_grounded : grounded small smallRun = true := by native_decide

theorem small_chosen_minimum :
    small.policies.all (fun p => decide ((29949 : ℚ)/10000 ≤ p.g)) = true := by native_decide

def taskMissingFromField := { small with field := small.field.drop 1 }
def duplicateTaskInField := { small with field := small.field ++ small.field.take 1 }
def unpinnedFact := { small with field := .fact 1 ⟨true, 9, 1, 0⟩ :: small.field.drop 1 }
def exclusionWithoutReason : Grounding := { small with field := small.field.take 4 ++ [FieldEntry.excluded 5 0 105] }

theorem taskMissingFromField_G1 : fieldConsidered taskMissingFromField = false := by native_decide
theorem duplicateTaskInField_G1 : fieldConsidered duplicateTaskInField = false := by native_decide
theorem unpinnedFact_G1 : fieldConsidered unpinnedFact = false := by native_decide
theorem exclusionWithoutReason_G1 : fieldConsidered exclusionWithoutReason = false := by native_decide

def changeFirst (f : GroundedPolicy → GroundedPolicy) : Grounding :=
  { small with policies := (small.policies.take 1).map f ++ small.policies.drop 1 }

/-- The cone-first result should pick 1, not the lower-cone task 2. -/
def menuOrderPick : Grounding :=
  { small with policies := small.policies.map (fun p =>
      if p.cascade = 70001 then { p with pick := some 2 } else p) }
def pickFromEmptyGate : Grounding :=
  { small with field := small.field.map (fun e => match e with
    | .fact t f => .fact t { f with ready := false }
    | e => e) }
def namedStepUnverifiable := changeFirst fun p => { p with steps := [.named 99] }

theorem menuOrderPick_G2 : prioritised menuOrderPick = some false := by native_decide
theorem pickFromEmptyGate_G2 : prioritised pickFromEmptyGate = some false := by native_decide
theorem namedStepUnverifiable_G2 : prioritised namedStepUnverifiable = none := by native_decide
theorem namedStep_neither_true_nor_false :
    prioritised namedStepUnverifiable ≠ some true ∧
    prioritised namedStepUnverifiable ≠ some false := by native_decide

def gNotFromTerms := changeFirst fun p => { p with g := 0 }
def reachAboveOne := changeFirst fun p => { p with reach := 2 }
def pickOnUnknownRelation := changeFirst fun p => { p with relation := .unknown }

theorem gNotFromTerms_G3 : scoredFromTerms gNotFromTerms = false := by native_decide
theorem reachAboveOne_G3 : scoredFromTerms reachAboveOne = false := by native_decide
theorem pickOnUnknownRelation_G3 : scoredFromTerms pickOnUnknownRelation = false := by native_decide

def policyGDisagrees := { smallRun with policyG := [(70000, 0), (70001, 29949/10000),
  (70002, 34841/10000)] }
theorem policyGDisagrees_G4 : agreesWithRunFacts small policyGDisagrees = false := by native_decide

/-- A negative built by removing the typed exclusion, so the candidates and picks
are untouched: G1 alone refuses it. -/
def excludedTaskMissing : Grounding := { small with field := small.field.take 4 }
/-- The terms no longer sum to G while G itself still agrees with `RunFacts`. -/
def termsNotG := changeFirst fun p => { p with terms := { p.terms with novelty := 0 } }

/-- Each negative refuses exactly one of G1–G4 and leaves the other three standing,
so each requirement is a discriminator, not a passenger (claude-2, review). -/
theorem grounding_negatives_isolate :
    (fieldConsidered excludedTaskMissing = false ∧ prioritised excludedTaskMissing = some true ∧
      scoredFromTerms excludedTaskMissing = true ∧ agreesWithRunFacts excludedTaskMissing smallRun = true) ∧
    (fieldConsidered unpinnedFact = false ∧ prioritised unpinnedFact = some true ∧
      scoredFromTerms unpinnedFact = true ∧ agreesWithRunFacts unpinnedFact smallRun = true) ∧
    (fieldConsidered duplicateTaskInField = false ∧ prioritised duplicateTaskInField = some true ∧
      scoredFromTerms duplicateTaskInField = true ∧ agreesWithRunFacts duplicateTaskInField smallRun = true) ∧
    (fieldConsidered exclusionWithoutReason = false ∧ prioritised exclusionWithoutReason = some true ∧
      scoredFromTerms exclusionWithoutReason = true ∧ agreesWithRunFacts exclusionWithoutReason smallRun = true) ∧
    (fieldConsidered menuOrderPick = true ∧ prioritised menuOrderPick = some false ∧
      scoredFromTerms menuOrderPick = true ∧ agreesWithRunFacts menuOrderPick smallRun = true) ∧
    (fieldConsidered pickFromEmptyGate = true ∧ prioritised pickFromEmptyGate = some false ∧
      scoredFromTerms pickFromEmptyGate = true ∧ agreesWithRunFacts pickFromEmptyGate smallRun = true) ∧
    (fieldConsidered termsNotG = true ∧ prioritised termsNotG = some true ∧
      scoredFromTerms termsNotG = false ∧ agreesWithRunFacts termsNotG smallRun = true) ∧
    (fieldConsidered reachAboveOne = true ∧ prioritised reachAboveOne = some true ∧
      scoredFromTerms reachAboveOne = false ∧ agreesWithRunFacts reachAboveOne smallRun = true) ∧
    (fieldConsidered pickOnUnknownRelation = true ∧ prioritised pickOnUnknownRelation = some true ∧
      scoredFromTerms pickOnUnknownRelation = false ∧ agreesWithRunFacts pickOnUnknownRelation smallRun = true) ∧
    (fieldConsidered small = true ∧ prioritised small = some true ∧
      scoredFromTerms small = true ∧ agreesWithRunFacts small policyGDisagrees = false) := by
  native_decide

/-- `gNotFromTerms` changes G itself, so it also disagrees with `RunFacts`: two
requirements refuse it, which is right, and the isolating G3 negative is `termsNotG`. -/
theorem gNotFromTerms_also_G4 : agreesWithRunFacts gNotFromTerms smallRun = false := by native_decide

#print axioms small_witness_grounded
end DarkTower.WarMachine.SelectionGrounding
