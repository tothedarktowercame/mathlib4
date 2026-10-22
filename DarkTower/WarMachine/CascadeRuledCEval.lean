import DarkTower.WarMachine.CascadeCompetitorsEval
import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.PatternTheta

/-!
# The three G7 cascades against the ruled class preference

This classification is claude-7's interpretation reading, not an inferred
classification theorem: at horizon H = 10, a state is focused exactly when
handedOff (token 6) holds and brokeLive (token 10) does not. Every other
terminal state is stopTheLine. R15StrategicTarget's docstring treats failure
to reach a target as stop-the-line; breaking live records is a target failure
in this reading. Before H, the outcome is notYetEvaluated. No other classes
are assigned, and no preference mass is renormalized over the two outcomes.

The full five-class preference is CTauClassPreference.classPreference:
waiting before H, then the ruled 55/35/5/5 terminal weights. Pre-horizon risk
is zero (the waiting point mass against itself), so the total G here is the
horizon KL. This keeps the original exact rational co-application transition
and uses Float only for logarithms and softmax. It is an evaluation, not a
proof equating this executable transcription with the real-valued kernel.

Every pattern uses PatternTheta.thetaOf on claude-7's attested, unreviewed
reading (4 success and 1 failure pseudo-count, no witnessed fires). The
rational theta is proved to be 4/5. The theta=1 override is a separate,
reading-free deterministic sanity check, not claimed as a learned value.

The illustrative C4 comparison summed all ten epochs and ranked inPlace
(G≈17.47), delegateChecked (≈17.89), delegate (≈33.80). This ruled horizon-only
comparison keeps that ranking: inPlace (G≈0.519021), delegateChecked
(≈0.535999), delegate (≈2.995732). Its softmax weights are approximately
0.483750, 0.475606, 0.040644 respectively. The scores have a different
preference and time schedule and should not be subtracted from the C4 scores.
-/

namespace DarkTower.WarMachine.CascadeRuledCEval

open CascadeTransition CascadeUncertainEval CascadeCompetitorsEval
open CTauClassPreference

def horizon : ℕ := 10

def reading : PatternTheta.ThetaReading where
  priorS := 4
  priorF := 1
  success_positive := by decide
  failure_positive := by decide
  readingAttestation := "claude-7 reading, 2026-10-22, unreviewed; ~/notes/lean-led/CASCADE-agent-patterns-m40-G7-2026-10-22.md"

theorem reading_theta : PatternTheta.thetaOf reading [] = (4 / 5 : ℚ) := by
  norm_num [PatternTheta.theta_nil, reading]

/-- The exact rational parameter consumed by the co-application transcription. -/
def readingTheta : Fin n → ℚ := fun _ => PatternTheta.thetaOf reading []

/-- Use the same token interpretation with theta also carried in the pattern. -/
def readPattern (p : InterpretedPattern Tok) : InterpretedPattern Tok :=
  PatternTheta.interpretWithTheta p.consumes p.produces p.forbids reading []

def terminalClass (s : Finset Tok) : EndingClass :=
  if (6 : Tok) ∈ s ∧ (10 : Tok) ∉ s then .focused else .stopTheLine

def terminalDistribution (d : CascadeUncertainEval.Dist Tok) : Distribution := fun c =>
  ((d.filter fun sw => terminalClass sw.1 = c).map (·.2)).sum

/-- All epochs in the comparison are in 1..H. Before H the reading emits waiting. -/
def predictionAt (tau : ℕ) (d : CascadeUncertainEval.Dist Tok) : Distribution :=
  if tau = horizon then terminalDistribution d else waitingPreference

theorem pre_horizon_risk_zero (tau : ℕ) (h : tau < horizon) (d : CascadeUncertainEval.Dist Tok) :
    classRisk (predictionAt tau d) (classPreference horizon tau) = 0 := by
  simpa [predictionAt, Nat.ne_of_lt h] using
    CTauClassPreference.pre_horizon_risk_zero horizon tau h

def classes : List EndingClass :=
  [.focused, .related, .unrelated, .stopTheLine, .notYetEvaluated]

/-- Float KL transcription; zero predicted mass contributes zero even at C=0. -/
def riskFloat (q c : Distribution) : Float :=
  (classes.map fun k =>
    if q k = 0 then 0 else toF (q k) * Float.log (toF (q k) / toF (c k))).sum

def finalPrediction (pats : Fin n → InterpretedPattern Tok) : Distribution :=
  let interpreted := fun i => readPattern (pats i)
  let descendants := Array.ofFn (descOf interpreted)
  let step := stepCo interpreted (fun i => descendants[i.val]!) readingTheta
  predictionAt horizon (step^[horizon] {((∅ : Finset Tok), 1)})

/-- Full distribution retained exactly; score uses all five ruled preferences. -/
def score (pats : Fin n → InterpretedPattern Tok) : List (EndingClass × ℚ) × Float :=
  let q := finalPrediction pats
  (classes.map (fun c => (c, q c)), riskFloat q (classPreference horizon horizon))

#eval ("delegate", score delegate)
#eval ("delegateChecked", score delegateChecked)
#eval ("inPlace", score inPlace)

/-- Uniform E and beta=1: normalized exp(-G); the common E cancels. -/
def weights : List (String × Float) :=
  let gs := [("delegate", (score delegate).2),
             ("delegateChecked", (score delegateChecked).2),
             ("inPlace", (score inPlace).2)]
  let unnormalized := gs.map fun (name, g) => (name, Float.exp (-g))
  let z := (unnormalized.map (·.2)).sum
  unnormalized.map fun (name, w) => (name, w / z)

#eval weights

/-- Reading-free theta=1 override, solely for checking the deterministic limit. -/
def deterministicCheck (pats : Fin n → InterpretedPattern Tok) :
    List (EndingClass × ℚ) :=
  let descendants := Array.ofFn (descOf pats)
  let step := stepCo pats (fun i => descendants[i.val]!) (fun _ => (1 : ℚ))
  let q := terminalDistribution (step^[horizon] {((∅ : Finset Tok), 1)})
  classes.map fun c => (c, q c)

#eval ("theta=1 check: delegate", deterministicCheck delegate)
#eval ("theta=1 check: delegateChecked", deterministicCheck delegateChecked)
#eval ("theta=1 check: inPlace", deterministicCheck inPlace)

#print axioms reading_theta
#print axioms pre_horizon_risk_zero

end DarkTower.WarMachine.CascadeRuledCEval
