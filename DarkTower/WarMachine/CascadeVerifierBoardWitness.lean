import Mathlib.Data.List.Basic

/-!
# N1 cascade verifier: no act arm under the declared verb semantics

Board-as-data from futon3c/agents/cascade_verifier_board.clj. The runtime
looks up an extensible atom-backed registry. Absence of a ZAP chip alone does
NOT constrain replacements of other verbs. We prove the effect-set theorem
for the declared semantics and exhibit that missing registry premise.
Effects here are proposals, never proof of what an arbitrary I/O handler does.
-/
namespace DarkTower.WarMachine.CascadeVerifierBoardWitness

inductive Verb where
  | smellBacklog | lookDebt | sing | yield | zap
  deriving DecidableEq, Repr
inductive Effect where
  | observe | verifyRequest | report | yieldTurn | typedNone | commit | zap
  deriving DecidableEq, Repr
structure Chip where
  id : String
  verb : Verb
  target : Option String := none
  onTrue : Option String := none
  onFalse : Option String := none
  deriving DecidableEq, Repr
structure Row where
  chip : Chip
  branch : Bool
  effects : List Effect
  deriving DecidableEq, Repr

abbrev Registry := Verb → Bool → List Effect

def allowed (e : Effect) : Prop :=
  e = .observe ∨ e = .verifyRequest ∨ e = .report ∨ e = .yieldTurn ∨ e = .typedNone

def declared : Registry
  | .smellBacklog, _ => [.observe]
  | .lookDebt, true => [.verifyRequest]
  | .lookDebt, false => [.typedNone]
  | .sing, _ => [.report]
  | .yield, _ => [.yieldTurn]
  | .zap, _ => [.commit]

def board : List Chip :=
  [⟨"ck/smell", .smellBacklog, none, some "ck/look-first", some "ck/sing-clear"⟩,
   ⟨"ck/look-first", .lookDebt, some "wm-choice/c-grain", some "ck/sing-debt", some "ck/yield"⟩,
   ⟨"ck/sing-clear", .sing, none, some "ck/yield", none⟩,
   ⟨"ck/sing-debt", .sing, none, some "ck/yield", none⟩,
   ⟨"ck/yield", .yield, none, none, none⟩]

def NoZap (chips : List Chip) : Prop := ∀ c ∈ chips, c.verb ≠ .zap

theorem boardHasNoZap : NoZap board := by simp [NoZap, board]

/-- Any finite, non-ZAP board uses only allowed effects under declared verbs.
This proves the subset from verb implementations, rather than assuming safety
as part of what it means for an execution row to exist. -/
theorem declaredEffectsAllowed (chips : List Chip) (h : NoZap chips)
    (c : Chip) (hc : c ∈ chips) (branch : Bool) (e : Effect)
    (he : e ∈ declared c.verb branch) : allowed e := by
  have hn := h c hc
  cases hv : c.verb <;> cases branch <;> simp_all [declared, allowed]

/-- Successful dispatches from chips in the board. This overapproximates routes:
therefore safety holds for every actual route and arbitrary finite prefixes,
provided the executor uses this registry and board. -/
inductive Executes (registry : Registry) (chips : List Chip) : List Row → Prop where
  | empty : Executes registry chips []
  | next {trace} (c : Chip) (branch : Bool) :
      c ∈ chips → Executes registry chips trace →
      Executes registry chips (trace ++ [⟨c, branch, registry c.verb branch⟩])

theorem traceEffectsAllowed (chips : List Chip) (h : NoZap chips)
    (trace : List Row) (run : Executes declared chips trace) :
    ∀ row ∈ trace, ∀ e ∈ row.effects, allowed e := by
  induction run with
  | empty => simp
  | next c branch hc run ih =>
      intro row hr e he
      rcases List.mem_append.mp hr with hprev | hlast
      · exact ih row hprev e he
      · have eq : row = ⟨c, branch, declared c.verb branch⟩ := by simpa using hlast
        subst row
        exact declaredEffectsAllowed chips h c hc branch e he

theorem cascadeHasNoActEffects (trace : List Row) (run : Executes declared board trace) :
    ∀ row ∈ trace, Effect.commit ∉ row.effects ∧ Effect.zap ∉ row.effects := by
  intro row hr
  have safe := traceEffectsAllowed board boardHasNoZap trace run row hr
  constructor
  · intro he; simpa [allowed] using safe .commit he
  · intro he; simpa [allowed] using safe .zap he

/-- Counterexample to dropping the registry premise: register-verb! can replace
smell-backlog without changing any board bytes or the board's digest. -/
def replacedRegistry : Registry := fun _ _ => [.commit]
def replacementRow : Row := ⟨board[0], false, [.commit]⟩
theorem noZapAloneIsInsufficient :
    NoZap board ∧ Executes replacedRegistry board [replacementRow] ∧
      Effect.commit ∈ replacementRow.effects := by
  refine ⟨boardHasNoZap, ?_, by simp [replacementRow]⟩
  exact Executes.next (board[0]) false (by decide) Executes.empty

/-! ## Retained production fixture, not a new verification of the debt itself -/
def boardDigest := "sha256:3a806b34dd46e94c4b91adead7b86105d7e0c682452392375a3cfbf90b863664"
def firstRequest := "wm-choice/c-grain"
def requestPointer := "futon2/holes/labs/wm-contract/aif-equations.edn:1"
def requestBasis := "a6d551bb9bfbc4ca451f3071710e3490926c369266ccccfe5bb4e87c80d3c09d"
def debtCount : Nat := 324

def fixtureRows : List Row :=
  [⟨board[0], true, [.observe]⟩,
   ⟨board[1], true, [.verifyRequest]⟩,
   ⟨board[3], true, [.report]⟩,
   ⟨board[4], true, [.yieldTurn]⟩]

theorem fixtureExecutes : Executes declared board fixtureRows := by
  have h1 := Executes.next (board[0]) true (by decide) (Executes.empty (registry := declared) (chips := board))
  have h2 := Executes.next (board[1]) true (by decide) h1
  have h3 := Executes.next (board[3]) true (by decide) h2
  have h4 := Executes.next (board[4]) true (by decide) h3
  exact h4

def followsWires : List Row → Bool
  | [] => false
  | [r] => r.chip.verb == .yield
  | r :: n :: rest =>
      (if r.branch then r.chip.onTrue else r.chip.onFalse) == some n.chip.id &&
        followsWires (n :: rest)

theorem fixtureWired : followsWires fixtureRows = true := by decide

theorem fixtureEffectsAllowed :
    ∀ row ∈ fixtureRows, ∀ e ∈ row.effects, allowed e :=
  traceEffectsAllowed board boardHasNoZap fixtureRows fixtureExecutes

def deltas : List Int :=
  [Int.ofNat debtCount - 324, Int.ofNat fixtureRows.length - 4,
   Int.ofNat (fixtureRows.flatMap Row.effects |>.filter (· == .verifyRequest)).length - 1,
   Int.ofNat (fixtureRows.flatMap Row.effects |>.filter (· == .commit)).length,
   Int.ofNat (fixtureRows.flatMap Row.effects |>.filter (· == .zap)).length]
theorem fixtureDeltasZero : deltas = [0, 0, 0, 0, 0] := by decide

def verbTag : Verb → String
  | .smellBacklog => "smell-backlog" | .lookDebt => "look-debt"
  | .sing => "sing" | .yield => "yield" | .zap => "zap"
def effectTag : Effect → String
  | .observe => "observe" | .verifyRequest => "verify-request" | .report => "report"
  | .yieldTurn => "yield-turn" | .typedNone => "typed-none" | .commit => "commit" | .zap => "zap"
#eval do
  IO.println ("BOARD|" ++ boardDigest)
  IO.println "END|end/yield"
  IO.println ("DEBT|" ++ toString debtCount)
  IO.println (String.intercalate "|" ["REQUEST", firstRequest, requestPointer, requestBasis, "dated-not-revalidated", "1"])
  IO.println "METERS|1|5|0"
  for c in board do
    IO.println (String.intercalate "|" ["CHIP", c.id, verbTag c.verb, c.target.getD "", c.onTrue.getD "", c.onFalse.getD ""])
  for r in fixtureRows do
    IO.println (String.intercalate "|" ["ROW", r.chip.id, verbTag r.chip.verb, toString r.branch, boardDigest,
      String.intercalate "," (r.effects.map effectTag)])
#print axioms boardHasNoZap
#print axioms declaredEffectsAllowed
#print axioms traceEffectsAllowed
#print axioms cascadeHasNoActEffects
#print axioms noZapAloneIsInsufficient
#print axioms fixtureExecutes
#print axioms fixtureWired
#print axioms fixtureEffectsAllowed
#print axioms fixtureDeltasZero
end DarkTower.WarMachine.CascadeVerifierBoardWitness
