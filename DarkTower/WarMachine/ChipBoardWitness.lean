import Mathlib.Data.List.Basic

/-!
# Chip-board v0: construction, witnesses and limits

Source: futon3c `agents/chip_board.clj` and `agents/inbox_zero_board.clj`.
This is a manually related model, not a proof that Clojure implements Lean.
`Repo = Option String` deliberately retains Clojure's missing/nil repo case.
Digests are opaque string carriers; no cryptographic property is assumed.
The trace fixture is the projection of run-2026-09-12.txt checked by the
companion readback script. FEEL targets come from the resolved board, since
v0 trace rows do not themselves contain FEEL args.
-/
namespace DarkTower.WarMachine.ChipBoardWitness

abbrev Repo := Option String
inductive Verb where
  | keypress | smell | look | feel | compareMove | zap | sing | yield | terminal
  deriving DecidableEq, Repr
inductive Effect where
  | commit (repo : Repo) | observe | report | refusal | yieldTurn
  deriving DecidableEq, Repr
structure Chip where
  id : String
  verb : Verb
  repo : Repo := none
  onTrue : Option String := none
  onFalse : Option String := none
  deriving DecidableEq, Repr
structure Board where
  chips : List Chip
  entry : String
  digest : String
  deriving DecidableEq, Repr
structure Row where
  chip : String
  verb : Verb
  branch : Bool
  digest : String
  repo : Repo := none
  effects : List Effect := []
  deriving DecidableEq, Repr
inductive Terminal where
  | yield | done
  deriving DecidableEq, Repr
inductive End where
  | terminal (target : Terminal) | fuelExhausted | stepCap
  deriving DecidableEq, Repr
structure Certificate where
  boardDigest : String
  inputsDigest : String
  trace : List Row
  ending : End
  deriving DecidableEq, Repr

def observation : Verb → Bool
  | .keypress | .smell | .look | .feel | .compareMove => true
  | _ => false

def wire (c : Chip) (b : Bool) : Option String := if b then c.onTrue else c.onFalse

def checkTwoWires (b : Board) : Bool :=
  b.chips.all fun c => !observation c.verb || (c.onTrue.isSome && c.onFalse.isSome)

/-- Presence of both arms, not the stronger claim that extra keys are rejected. -/
theorem checkedObservationHasEitherWire (b : Board) (h : checkTwoWires b = true)
    (c : Chip) (hc : c ∈ b.chips) (ho : observation c.verb = true) (arm : Bool) :
    ∃ target, wire c arm = some target := by
  have h' := (List.all_eq_true.mp h) c hc
  cases ht : c.onTrue <;> cases hf : c.onFalse <;> cases arm <;>
    simp_all [wire]

/-- Exact priority in the runtime loop. This classifies RETURNED ends, not faults.
Unknown verbs, unwired actions and effect-handler exceptions can still throw. -/
def endAt (terminal : Option Terminal) (steps cap : Nat) (fuel : Int) : Option End :=
  match terminal with
  | some t => some (.terminal t)
  | none => if steps ≥ cap then some .stepCap
            else if fuel = 0 then some .fuelExhausted else none

theorem terminalBeforeCaps : endAt (some .yield) 64 64 0 = some (.terminal .yield) := rfl
theorem stepCapBeforeFuel : endAt none 64 64 0 = some .stepCap := rfl
theorem fuelEnd : endAt none 3 64 0 = some .fuelExhausted := rfl
theorem negativeFuelDoesNotExhaust : endAt none 3 64 (-1) = none := rfl

/-- Abstraction of each successful verb call. Branch decisions for observations
are supplied by the observation packet; effects irrelevant to the hazard are
abstracted to tags. Non-target values and implementation exceptions are outside
this successful-call relation. It does NOT assume the hazard as a premise. -/
inductive Step : Repo → Row → Repo → Prop where
  | feelIdle (s r : Repo) (id digest : String) :
      Step s ⟨id, .feel, false, digest, r, []⟩ r
  | feelLive (s r : Repo) (id digest : String) :
      Step s ⟨id, .feel, true, digest, r, []⟩ s
  | zapYes (s r : Repo) (id digest : String) (eq : s = r) :
      Step s ⟨id, .zap, true, digest, r, [.commit r]⟩ s
  | zapNo (s r : Repo) (id digest : String) (ne : s ≠ r) :
      Step s ⟨id, .zap, false, digest, r, [.refusal]⟩ s
  | other (s : Repo) (row : Row)
      (notFeel : row.verb ≠ .feel)
      (noCommit : ∀ r, Effect.commit r ∉ row.effects) : Step s row s

inductive Executes : Repo → List Row → Prop where
  | initial : Executes none []
  | next {s t trace row} : Executes s trace → Step s row t → Executes t (trace ++ [row])

def HasFeel (trace : List Row) (r : Repo) : Prop :=
  ∃ row ∈ trace, row.verb = .feel ∧ row.branch = false ∧ row.repo = r

def Certified (s : Repo) (trace : List Row) : Prop :=
  ∀ r : String, s = some r → HasFeel trace (some r)

/-- Every named commit has an earlier idle-FEEL for the same named repo.
Snoc construction makes 'earlier' strict, rather than allowing the current row. -/
inductive NamedSafe : List Row → Prop where
  | empty : NamedSafe []
  | next {trace row} : NamedSafe trace →
      (∀ r : String, Effect.commit (some r) ∈ row.effects → HasFeel trace (some r)) →
      NamedSafe (trace ++ [row])

lemma hasFeel_append {trace : List Row} {r : Repo} (h : HasFeel trace r) (row : Row) :
    HasFeel (trace ++ [row]) r := by
  obtain ⟨a, ha, hp⟩ := h
  exact ⟨a, List.mem_append_left _ ha, hp⟩

lemma stepPreservesCertified {s t : Repo} {trace : List Row} {row : Row}
    (h : Certified s trace) (step : Step s row t) : Certified t (trace ++ [row]) := by
  cases step with
  | feelIdle s id digest =>
      intro name hr
      exact ⟨⟨id, .feel, false, digest, t, []⟩, List.mem_append_right _ (by simp), rfl, rfl, hr⟩
  | feelLive r id digest =>
      intro name hr
      exact hasFeel_append (h name hr) _
  | zapYes r id digest eq =>
      intro name hr
      exact hasFeel_append (h name hr) _
  | zapNo r id digest ne =>
      intro name hr
      exact hasFeel_append (h name hr) _
  | other row nf nc =>
      intro name hr
      exact hasFeel_append (h name hr) _

lemma stepNamedCommit {s t : Repo} {trace : List Row} {row : Row}
    (h : Certified s trace) (step : Step s row t) :
    ∀ r : String, Effect.commit (some r) ∈ row.effects → HasFeel trace (some r) := by
  cases step with
  | feelIdle => simp
  | feelLive => simp
  | zapNo => simp
  | zapYes repo id digest eq =>
      intro name hm
      have he : some name = repo := by simpa using hm
      exact h name (eq.trans he.symm)
  | other row nf nc =>
      intro name hm
      exact False.elim (nc (some name) hm)

theorem executorNamedHazard {s : Repo} {trace : List Row} (h : Executes s trace) :
    Certified s trace ∧ NamedSafe trace := by
  induction h with
  | initial =>
      constructor
      · intro r hr; cases hr
      · exact .empty
  | next execution step ih =>
      exact ⟨stepPreservesCertified ih.1 step, .next ih.2 (stepNamedCommit ih.1 step)⟩

/-- The unrestricted v0 claim is false: initial missing cert equals missing repo. -/
def nilZap : Row := ⟨"z", .zap, true, "opaque", none, [.commit none]⟩
theorem nilZapExecutesWithoutFeel :
    Step none nilZap none ∧ Effect.commit none ∈ nilZap.effects ∧ ¬ HasFeel [] none := by
  exact ⟨.zapYes none none "z" "opaque" rfl, by simp [nilZap], by simp [HasFeel]⟩

/-- Matches verify-trace's dissoc :effects projection; board-resolved repo is
also absent from raw runtime rows. Replay equality is NOT effect equality. -/
def replayView (r : Row) := (r.chip, r.verb, r.branch, r.digest)
def forgedZap : Row := { nilZap with effects := [.commit (some "foreign")] }
theorem replayDoesNotCertifyEffects :
    replayView nilZap = replayView forgedZap ∧ nilZap.effects ≠ forgedZap.effects := by
  constructor
  · rfl
  · decide

/-! ## Pinned production readback: six rows, yield, one named commit proposal -/
def boardDigest := "sha256:a09756448d0dfb11eb1cdd8e11ef03c2be473c836cd4e8f82b6e222e5fff52b4"
def inputsDigest := "sha256:cb45070fa6189bec07bae3784eba70ea60d0382fd6c16dcd92d6dd30cc42dbd9"
def fixtureRows : List Row :=
  [⟨"ck/keypress", .keypress, false, boardDigest, none, []⟩,
   ⟨"ck/smell", .smell, true, boardDigest, none, [.observe]⟩,
   ⟨"ck/look-first", .look, true, boardDigest, some "futon5a", [.observe]⟩,
   ⟨"ck/feel-target", .feel, false, boardDigest, some "futon5a", []⟩,
   ⟨"ck/zap-commit", .zap, true, boardDigest, some "futon5a", [.commit (some "futon5a")]⟩,
   ⟨"ck/yield", .yield, true, boardDigest, none, [.yieldTurn]⟩]

def fixtureBoard : Board := ⟨[
  ⟨"ck/keypress", .keypress, none, some "ck/yield", some "ck/smell"⟩,
  ⟨"ck/smell", .smell, none, some "ck/look-first", some "ck/sing-clean"⟩,
  ⟨"ck/look-first", .look, some "futon5a", some "ck/feel-target", some "ck/yield"⟩,
  ⟨"ck/feel-target", .feel, some "futon5a", some "ck/sing-flag-live", some "ck/zap-commit"⟩,
  ⟨"ck/zap-commit", .zap, some "futon5a", some "ck/yield", some "ck/yield"⟩,
  ⟨"ck/sing-clean", .sing, none, some "ck/yield", none⟩,
  ⟨"ck/sing-flag-live", .sing, none, some "ck/yield", none⟩,
  ⟨"ck/yield", .yield, none, none, none⟩], "ck/keypress", boardDigest⟩

/-- Check the actual selected wires between fixture rows. The final row is
restricted to the YIELD verb this fixture really executed. -/
def followsWires (b : Board) : List Row → Bool
  | [] => false
  | [last] => last.verb == .yield
  | row :: next :: rest =>
      match b.chips.find? (fun c => c.id == row.chip) with
      | none => false
      | some c => c.verb == row.verb && wire c row.branch == some next.chip &&
          followsWires b (next :: rest)

theorem fixtureFollowsWires :
    fixtureRows.head?.map Row.chip = some fixtureBoard.entry ∧
      followsWires fixtureBoard fixtureRows = true := by decide

theorem fixtureTwoWires : checkTwoWires fixtureBoard = true := by decide

def fixture : Certificate := ⟨boardDigest, inputsDigest, fixtureRows, .terminal .yield⟩

theorem fixtureExecutes : Executes (some "futon5a") fixtureRows := by
  have h0 := Executes.initial
  have h1 := Executes.next h0 (Step.other none (fixtureRows[0]) (by decide) (by intro r; simp [fixtureRows]))
  have h2 := Executes.next h1 (Step.other none (fixtureRows[1]) (by decide) (by intro r; simp [fixtureRows]))
  have h3 := Executes.next h2 (Step.other none (fixtureRows[2]) (by decide) (by intro r; simp [fixtureRows]))
  have h4 := Executes.next h3 (Step.feelIdle none (some "futon5a") "ck/feel-target" boardDigest)
  have h5 := Executes.next h4 (Step.zapYes (some "futon5a") (some "futon5a") "ck/zap-commit" boardDigest rfl)
  have h6 := Executes.next h5 (Step.other (some "futon5a") (fixtureRows[5]) (by decide) (by intro r; simp [fixtureRows]))
  exact h6

theorem fixtureNamedHazard : NamedSafe fixtureRows := (executorNamedHazard fixtureExecutes).2

def fixtureDeltas : List Int :=
  [Int.ofNat fixture.trace.length - 6,
   Int.ofNat (fixture.trace.filter (fun r => r.verb == .feel)).length - 1,
   Int.ofNat (fixture.trace.filter (fun r => r.effects.contains (.commit (some "futon5a")))).length - 1,
   if fixture.ending = .terminal .yield then 0 else 1,
   if fixture.trace.all (fun r => r.digest == fixture.boardDigest) then 0 else 1]
theorem fixtureDeltasZero : fixtureDeltas = [0, 0, 0, 0, 0] := by decide

/-- Machine-readable projection; companion script compares these lines to the
retained EDN, including board-resolved args and all branch/digest fields. -/
def verbTag : Verb → String
  | .keypress => "keypress" | .smell => "smell" | .look => "look" | .feel => "feel"
  | .compareMove => "compare-move" | .zap => "zap" | .sing => "sing"
  | .yield => "yield" | .terminal => "terminal"
def effectTag : Effect → String
  | .commit r => "commit:" ++ r.getD "<nil>"
  | .observe => "observe" | .report => "report" | .refusal => "refusal"
  | .yieldTurn => "yield-turn"
def rowLine (r : Row) : String := String.intercalate "|"
  ["ROW", r.chip, verbTag r.verb, toString r.branch, r.digest,
   r.repo.getD "", String.intercalate "," (r.effects.map effectTag)]
def chipLine (c : Chip) : String := String.intercalate "|"
  ["CHIP", c.id, verbTag c.verb, c.repo.getD "", c.onTrue.getD "", c.onFalse.getD ""]
#eval do
  IO.println ("BOARD|" ++ fixture.boardDigest)
  IO.println ("INPUTS|" ++ fixture.inputsDigest)
  IO.println "END|end/yield"
  for c in fixtureBoard.chips do IO.println (chipLine c)
  for r in fixture.trace do IO.println (rowLine r)
#print axioms fixtureFollowsWires
#print axioms fixtureTwoWires
#print axioms checkedObservationHasEitherWire
#print axioms executorNamedHazard
#print axioms nilZapExecutesWithoutFeel
#print axioms replayDoesNotCertifyEffects
#print axioms fixtureExecutes
#print axioms fixtureNamedHazard
#print axioms fixtureDeltasZero
end DarkTower.WarMachine.ChipBoardWitness
