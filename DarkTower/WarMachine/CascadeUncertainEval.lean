import DarkTower.WarMachine.CascadeCoScoringExamples

/-!
# Uncertain patterns: evaluating the two transitions with `θ < 1`

`CascadeCoScoringExamples` proves the scores for `θ = 1`, where G only counts
epochs. With `θ < 1` the epoch at which the goal is reached is a distribution,
and the real-valued G in `CascadeEFE` cannot be evaluated by `#eval`. This
module is an exact rational transcription of the two transitions, evaluated:

* `stepCo`: co-application (`Proof2.CoApplicationKernel.coApplyKernel`): each
  subset `S` of the enabled frontier succeeds with weight
  `∏_{S} θ · ∏_{F∖S} (1−θ)` and adds its products. The frontier is computed from
  the descendant tables `descJoin` / `descAgent`, which
  `CascadeCoScoringExamples` checks closed under the containment order (so an
  enabled pattern with an enabled descendant is excluded, as in
  `enabledFrontier`).
* `stepList`: the first-enabled list kernel (`CascadeTransition.patternKernel`
  of the first enabled pattern): fire with `θ`, stay with `1 − θ`.

`goalProb` is the predicted probability that the goal is established at an
epoch; with the outcome read with certainty, ambiguity is zero and the epoch's
G is the KL divergence of `Bernoulli(goalProb)` from `C = (9/10, 1/10)`
(`CascadeEFE.risk`), evaluated in `Float` by `epochG`.

Not proved here: that `stepCo` equals `coApplyKernel` for `θ < 1` (the `θ = 1`
case is `coApply_one`). The evaluations are a transcription, labelled as one.
-/

namespace DarkTower.WarMachine.CascadeUncertainEval

open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeScoringExamples
open DarkTower.WarMachine.CascadeCoScoringExamples

variable {n : ℕ} {V : Type} [Fintype V] [DecidableEq V]

/-- A predicted distribution over states, as weighted states (duplicates allowed). -/
abbrev Dist (V : Type) := Multiset (Finset V × ℚ)

def frontierQ (pats : Fin n → InterpretedPattern V) (desc : Fin n → Finset (Fin n))
    (s : Finset V) : Finset (Fin n) :=
  Finset.univ.filter fun p => guard (pats p) s ∧ ∀ q ∈ desc p, ¬ guard (pats q) s

def stepCo (pats : Fin n → InterpretedPattern V) (desc : Fin n → Finset (Fin n))
    (θ : Fin n → ℚ) (d : Dist V) : Dist V :=
  d.bind fun sw =>
    let F := frontierQ pats desc sw.1
    F.powerset.val.map fun S =>
      (sw.1 ∪ S.biUnion (fun p => (pats p).produces),
        sw.2 * (∏ p ∈ S, θ p) * ∏ p ∈ F \ S, (1 - θ p))

def firstIdx (pats : Fin n → InterpretedPattern V) : List (Fin n) → Finset V → Option (Fin n)
  | [], _ => none
  | p :: ps, s => if guard (pats p) s then some p else firstIdx pats ps s

def stepList (pats : Fin n → InterpretedPattern V) (prec : List (Fin n)) (θ : Fin n → ℚ)
    (d : Dist V) : Dist V :=
  d.bind fun sw =>
    match firstIdx pats prec sw.1 with
    | none => {sw}
    | some p => {(sw.1 ∪ (pats p).produces, sw.2 * θ p), (sw.1, sw.2 * (1 - θ p))}

def goalProb (goal : V) (d : Dist V) : ℚ :=
  ((d.filter fun sw => goal ∈ sw.1).map (·.2)).sum

def toF (q : ℚ) : Float := Float.ofInt q.num / Float.ofNat q.den

/-- KL divergence of `Bernoulli p` from `(c, 1 − c)`: the epoch's risk. -/
def epochG (p c : Float) : Float :=
  (if p == 0 then 0 else p * Float.log (p / c)) +
    (if p == 1 then 0 else (1 - p) * Float.log ((1 - p) / (1 - c)))

/-- Goal probability at epochs `1 .. T`. -/
def trajectory (step : Dist V → Dist V) (goal : V) (T : ℕ) : List ℚ :=
  (List.range T).map fun t => goalProb goal (step^[t + 1] {((∅ : Finset V), 1)})

def totalGF (ps : List ℚ) : Float := (ps.map fun p => epochG (toF p) 0.9).sum

/-! ## θ = 4/5 for every pattern -/

def θ45 : Fin k → ℚ := fun _ => 4 / 5

/-- Join of three: co-application against the list. -/
def joinCo : List ℚ := trajectory (stepCo join3 descJoin θ45) 3 3
def joinList : List ℚ := trajectory (stepList join3 [2, 1, 0] θ45) 3 3
def chainCo : List ℚ := trajectory (stepCo chain3 descChain θ45) 3 3

/-- The seven agent patterns (m40 G7) over 8 epochs. -/
def agentCo : List ℚ := trajectory (stepCo agentPats descAgent θ45) 6 8
def agentList : List ℚ := trajectory (stepList agentPats agentAll θ45) 6 8

#eval (joinCo, totalGF joinCo)
#eval (joinList, totalGF joinList)
#eval (chainCo, totalGF chainCo)
#eval (agentCo, totalGF agentCo)
#eval (agentList, totalGF agentList)

/-- Check: at `θ = 1` the transcription reproduces the proved trajectories. -/
def θ1 : Fin k → ℚ := fun _ => 1
#eval trajectory (stepCo agentPats descAgent θ1) 6 8
#eval trajectory (stepList agentPats agentAll θ1) 6 8

end DarkTower.WarMachine.CascadeUncertainEval
