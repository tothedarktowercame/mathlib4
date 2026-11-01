import DarkTower.WarMachine.Requirements

/-! Computable selection carriers, separate from the projector's assertions.
Pins are opaque identities: this checks their presence, not cryptographic authenticity.
The small fixture uses exact rounded witness scores, not the full real-data witness.
`grounded` checks G1–G4; minimisation and the other run requirements remain in Requirements.
The DarkTower library glob includes this module automatically.
-/
namespace DarkTower.WarMachine.SelectionGrounding

abbrev Id := Requirements.Id

inductive Status where
  | ready | notReady | undetermined
  deriving DecidableEq, Repr

structure FieldFact where
  status : Status
  cone : ℕ
  unblocks : ℕ
  rank : ℕ
  pin : Id
  deriving DecidableEq, Repr

/-- Field facts and exclusions describe tasks, never policies for doing them.
`all-policies-already-satisfied` is deliberately not a constructor. A projector
must reject an unknown reason; it cannot encode registry statuses as exclusions.
The futon2 witness emitter must render `giraffe/unread-new` as `.unreadNew`. -/
inductive ExclusionReason where
  | unreadNew | targetSourcePathAbsent | targetSourceConflict | targetItemLineAbsent
  | readingSourceChanged
  deriving DecidableEq, Repr

inductive FieldEntry where
  | fact (task : Id) (f : FieldFact)
  | excluded (task : Id) (reason : ExclusionReason) (pin : Id)
  deriving DecidableEq, Repr

inductive Step where
  | readyGate | byCone | byUnblocks | byRank
  | statusGate (status : Status)
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
  «class» : Id
  /-- Opaque identity of the recorded prediction; not the pick identity. -/
  prediction : Id
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
  | .readyGate => some (field.filter fun x => x.2.status == .ready)
  | .statusGate s => some (field.filter fun x => x.2.status == s)
  | .byRank => some (field.insertionSort fun a b => a.2.rank ≤ b.2.rank)
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
    | .excluded _ _ pin => decide (pin ≠ 0))

/-- `none` means unverifiable, even if a different policy has a detectable mismatch. -/
def prioritised (g : Grounding) : Option Bool :=
  if g.policies.any (fun p => (recomputedPick g p).isNone) then none
  else some (g.policies.all fun p => decide (recomputedPick g p = some p.pick))

def Terms.score (t : Terms) : ℚ := t.risk + t.ambiguity - t.novelty

def scoredFromTerms (g : Grounding) : Bool :=
  g.policies.all (fun p => decide (p.g = p.terms.score ∧ 0 ≤ p.reach ∧ p.reach ≤ 1 ∧
    (p.pick.isSome = true → p.relation ≠ .unknown))) &&
  decide (g.abstention.2 = g.abstention.1.score)

/-- Members of one policy class agree on score and prediction. Their picks may
be different: action identity is not the equivalence relation on predictions. -/
def classConsistent (g : Grounding) : Bool :=
  g.policies.all fun p => g.policies.all fun q =>
    decide (p.class = q.class → p.g = q.g ∧ p.prediction = q.prediction)

def agreesWithRunFacts (g : Grounding) (r : Requirements.RunFacts) : Bool :=
  classConsistent g && (match r.currentDecision with
    | .pick _ c => decide (g.chosen = c)
    | _ => false) &&
  decide ((g.policies.map fun p => (p.class, p.g)).toFinset = r.policyG.toFinset ∧
    g.abstention.2 = r.abstentionG ∧ g.enumerated = r.enumeratedTasks)

def grounded (g : Grounding) (r : Requirements.RunFacts) : Bool :=
  fieldConsidered g && (prioritised g == some true) && scoredFromTerms g &&
    agreesWithRunFacts g r

/-- Two step orders recompute the same pick and prediction class. A third
arrangement is the other class, so the compared policy table has two rows. -/
def small : Grounding where
  enumerated := {1, 2, 3, 4, 5}
  field := [.fact 1 ⟨.ready, 4, 1, 1, 101⟩, .fact 2 ⟨.ready, 9, 8, 2, 102⟩,
    .fact 3 ⟨.ready, 4, 8, 3, 103⟩, .fact 4 ⟨.notReady, 99, 99, 4, 104⟩,
    .excluded 5 .unreadNew 105]
  policies := [
    ⟨70000, [.readyGate, .byCone, .byUnblocks], some 2, 1/2, .associated,
      ⟨3, 5041/10000, 1/50⟩, 34841/10000, 90000, 80000⟩,
    ⟨70001, [.readyGate, .byUnblocks, .byCone], some 2, 1/2, .associated,
      ⟨3, 5041/10000, 1/50⟩, 34841/10000, 90000, 80000⟩,
    ⟨70002, [.readyGate], some 1, 1/2, .associated,
      ⟨5/2, 5149/10000, 1/50⟩, 29949/10000, 90001, 80001⟩]
  abstention := (⟨4, 7875/10000, 0⟩, 47875/10000)
  chosen := 90001

def smallRun : Requirements.RunFacts :=
  { Requirements.selectionGood with
    currentDecision := .pick 1 90001
    policyG := [(90000, 34841/10000), (90001, 29949/10000)]
    abstentionG := 47875/10000
    enumeratedTasks := small.enumerated }

theorem small_witness_grounded : grounded small smallRun = true := by native_decide

theorem small_chosen_minimum :
    small.policies.all (fun p => decide ((29949 : ℚ)/10000 ≤ p.g)) = true := by native_decide

def taskMissingFromField := { small with field := small.field.drop 1 }
def duplicateTaskInField := { small with field := small.field ++ small.field.take 1 }
def unpinnedFact := { small with field := .fact 1 ⟨.ready, 4, 1, 1, 0⟩ :: small.field.drop 1 }
def exclusionWithoutPin : Grounding := { small with field := small.field.take 4 ++ [FieldEntry.excluded 5 .unreadNew 0] }

theorem taskMissingFromField_G1 : fieldConsidered taskMissingFromField = false := by native_decide
theorem duplicateTaskInField_G1 : fieldConsidered duplicateTaskInField = false := by native_decide
theorem unpinnedFact_G1 : fieldConsidered unpinnedFact = false := by native_decide
theorem exclusionWithoutPin_G1 : fieldConsidered exclusionWithoutPin = false := by native_decide

def changeFirst (f : GroundedPolicy → GroundedPolicy) : Grounding :=
  { small with policies := (small.policies.take 1).map f ++ small.policies.drop 1 }

/-- The ordered result should pick 2, not the lower-cone menu-first task 1. -/
def menuOrderPick : Grounding :=
  { small with policies := small.policies.map (fun p =>
      if p.cascade = 70000 then { p with pick := some 1 } else p) }
def pickFromEmptyGate : Grounding :=
  { small with field := small.field.map (fun e => match e with
    | .fact t f => .fact t { f with status := .notReady }
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

def policyGDisagrees := { smallRun with policyG := [(90000, 0), (90001, 29949/10000)] }
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
    (fieldConsidered exclusionWithoutPin = false ∧ prioritised exclusionWithoutPin = some true ∧
      scoredFromTerms exclusionWithoutPin = true ∧ agreesWithRunFacts exclusionWithoutPin smallRun = true) ∧
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

theorem small_two_class_rows : small.policies.length = 3 ∧ smallRun.policyG.length = 2 ∧
    agreesWithRunFacts small smallRun = true := by native_decide

/-- G1–G3 still hold and the recorded distinct pairs match. Only the internal
class consistency obligation prevents contradictory scores in one class. -/
def conflictingClassG := changeFirst fun p => { p with g := 0, terms := ⟨0, 0, 0⟩ }
def conflictingClassRun := { smallRun with policyG := [(90000, 0), (90000, 34841/10000), (90001, 29949/10000)] }
theorem conflictingClassG_G4 : agreesWithRunFacts conflictingClassG conflictingClassRun = false := by native_decide
theorem conflictingClassG_isolated : fieldConsidered conflictingClassG = true ∧
    prioritised conflictingClassG = some true ∧ scoredFromTerms conflictingClassG = true ∧
    (conflictingClassG.policies.map fun p => (p.class, p.g)).toFinset = conflictingClassRun.policyG.toFinset := by native_decide

def conflictingClassPrediction := changeFirst fun p => { p with prediction := 999 }
theorem conflictingClassPrediction_G4 : agreesWithRunFacts conflictingClassPrediction smallRun = false := by native_decide

theorem class_agreement_does_not_require_same_pick :
    agreesWithRunFacts menuOrderPick smallRun = true := by native_decide

#print axioms small_witness_grounded
end DarkTower.WarMachine.SelectionGrounding
