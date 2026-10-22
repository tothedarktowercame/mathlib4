import DarkTower.WarMachine.CascadeUncertainEval
import DarkTower.WarMachine.Proof2.ContainmentOrder

/-!
# Competing cascades for one m40 excursion step

The step is G7 of `E-prove-memory-useful`: every minus40 memory version gains
the turn id and act id it was written in. That adds required fields to a
record shape live agents already write and other code re-validates, so the
step can go wrong in a way the earlier example could not express: records
already on disk are refused (the incident behind
`futon3/library/memory/no-tightening-while-held`).

Three valid cascades, each built from interpreted patterns in its own context:

* `delegate`: the agent-library cascade (`CascadeScoringExamples.agentPats`)
  with an implementation step by the dispatched seat that does not check the
  validators, so implementing also breaks live records;
* `delegateChecked`: the same, with `no-tightening-while-held` before the
  dispatch, so the packet carries the validator sites;
* `inPlace`: no dispatch; `no-tightening-while-held` then implement, then
  `verify-in-the-serving-process`, then evidence, trail, ledger, handoff.

The outcome observed at each epoch has two parts, whether G7 is handed off and
whether live records are broken, and the preference is over the four
combinations (`C4`). Every pattern has `θ = 4/5`; each cascade's G is computed
with the co-application transition, as in `CascadeUncertainEval` (an exact
rational transcription; risk in `Float`). The descendant sets that define the
frontier are computed from the containment order (`descOf`).
-/

namespace DarkTower.WarMachine.CascadeCompetitorsEval

open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeUncertainEval

/-- Tokens: 0 scoped, 1 intentAgreed, 2 dispatched, 3 evidenced, 4 ledgered,
5 trailed, 6 handedOff (goal), 7 validatorsFound, 8 implemented,
9 verifiedLive, 10 brokeLive (the hazard). -/
abbrev Tok := Fin 11

def ip (consumes produces : Finset Tok) (forbids : Finset Tok := ∅) : InterpretedPattern Tok :=
  ⟨consumes, produces, forbids, 1, zero_le_one, le_rfl⟩

variable {n : ℕ}

/-- Everything a pattern's products lead to, by containment (iterated `n`
times, enough for `n` patterns). -/
def descOf (pats : Fin n → InterpretedPattern Tok) : Fin n → Finset (Fin n) := fun p =>
  let succ : Finset (Fin n) → Finset (Fin n) := fun S =>
    S ∪ Finset.univ.filter fun b => ∃ a ∈ S, ((pats a).produces ∩ (pats b).consumes).Nonempty
  let first := Finset.univ.filter fun b => b ≠ p ∧ ((pats p).produces ∩ (pats b).consumes).Nonempty
  succ^[n] first

/-- Delegate, unchecked: scope, intent, dispatch, implement (breaks live
records), evidence, trail, ledger, handoff. -/
def delegate : Fin 8 → InterpretedPattern Tok
  | 0 => ip ∅ {0}                 -- scope-before-action
  | 1 => ip {0} {1}               -- intent-handshake-is-binding
  | 2 => ip {1} {2}               -- coordination-has-cost
  | 3 => ip {2} {8, 10}           -- the seat implements, validators unchecked
  | 4 => ip {8} {3}               -- evidence-over-assertion
  | 5 => ip {2} {5}               -- trail-enables-return
  | 6 => ip {3} {4}               -- provisional-claims-ledger
  | 7 => ip {3, 4, 5} {6}         -- handoff-preserves-context

/-- Delegate, checked: no-tightening-while-held before the dispatch. -/
def delegateChecked : Fin 9 → InterpretedPattern Tok
  | 0 => ip ∅ {0}
  | 1 => ip {0} {1}
  | 2 => ip {0} {7}               -- no-tightening-while-held
  | 3 => ip {1, 7} {2}            -- dispatch carries the validator sites
  | 4 => ip {2} {8}               -- the seat implements, validators known
  | 5 => ip {8} {3}
  | 6 => ip {2} {5}
  | 7 => ip {3} {4}
  | 8 => ip {3, 4, 5} {6}

/-- In place: scope, no-tightening-while-held, implement, verify in the serving
process, evidence, trail, ledger, handoff. -/
def inPlace : Fin 8 → InterpretedPattern Tok
  | 0 => ip ∅ {0}
  | 1 => ip {0} {7}               -- no-tightening-while-held
  | 2 => ip {0, 7} {8}            -- implement, validators known
  | 3 => ip {8} {9}               -- verify-in-the-serving-process
  | 4 => ip {9} {3}               -- evidence (from the live check)
  | 5 => ip {0} {5}               -- trail, from the start
  | 6 => ip {3} {4}
  | 7 => ip {3, 4, 5} {6}

/-- The preference over (handed off, live records broken). -/
def C4 : Bool × Bool → Float
  | (true, false) => 0.90
  | (true, true) => 0.01
  | (false, false) => 0.08
  | (false, true) => 0.01

def outcomeDist (d : CascadeUncertainEval.Dist Tok) : List ((Bool × Bool) × Float) :=
  [(true, false), (true, true), (false, false), (false, true)].map fun o =>
    (o, toF ((d.filter fun sw => decide ((6 : Tok) ∈ sw.1) = o.1 ∧
      decide ((10 : Tok) ∈ sw.1) = o.2).map (·.2)).sum)

/-- The epoch's risk: KL of the predicted outcome from `C4`. -/
def risk4 (d : CascadeUncertainEval.Dist Tok) : Float :=
  ((outcomeDist d).map fun (o, q) => if q == 0 then 0 else q * Float.log (q / C4 o)).sum

def gOver (step : CascadeUncertainEval.Dist Tok → CascadeUncertainEval.Dist Tok) (T : ℕ) : Float :=
  ((List.range T).map fun t => risk4 (step^[t + 1] {((∅ : Finset Tok), 1)})).sum

def handedOff (step : CascadeUncertainEval.Dist Tok → CascadeUncertainEval.Dist Tok) (T : ℕ) : List ℚ :=
  (List.range T).map fun t => goalProb (6 : Tok) (step^[t + 1] {((∅ : Finset Tok), 1)})

def θ45' : Fin k → ℚ := fun _ => 4 / 5

def stepDelegate := stepCo delegate (descOf delegate) θ45'
def stepDelegateChecked := stepCo delegateChecked (descOf delegateChecked) θ45'
def stepInPlace := stepCo inPlace (descOf inPlace) θ45'

#eval (handedOff stepDelegate 10, gOver stepDelegate 10)
#eval (handedOff stepDelegateChecked 10, gOver stepDelegateChecked 10)
#eval (handedOff stepInPlace 10, gOver stepInPlace 10)

/-- Check: at θ = 1, the epoch at which each first hands off. -/
def θ1' : Fin k → ℚ := fun _ => 1
#eval handedOff (stepCo delegate (descOf delegate) θ1') 10
#eval handedOff (stepCo delegateChecked (descOf delegateChecked) θ1') 10
#eval handedOff (stepCo inPlace (descOf inPlace) θ1') 10

end DarkTower.WarMachine.CascadeCompetitorsEval
