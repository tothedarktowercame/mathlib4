import DarkTower.WarMachine.ScanLearning
import DarkTower.WarMachine.ScanModelReduction
import DarkTower.WarMachine.ScanShadow

/-!
# Learned scan functions at the machine boundary

These typed adapters bind the admitted pure arms of `scan-learn/step`,
`scan-bmr/score`, and `scan-shadow/shadow-row`. EDN decoding, duplicate run
ids, absent/malformed channels, non-finite JVM doubles, receipts, and trace
recording are machine-only boundaries and are not modeled here.

Every theorem below is definitional (`rfl`): each machine carrier is the theory
declaration under a machine-facing name, so these theorems add no mathematical
content. What ties the Clojure to the theory is a reading of the cited
futon2 lines against the theory declarations; nothing here executes or checks
the Clojure.
-/

namespace DarkTower.WarMachine.Proof2.ScanLearningAtMachine

open DarkTower.WarMachine.DirichletLearning
open DarkTower.WarMachine.ScanLearning
open DarkTower.WarMachine.ScanModelReduction
open DarkTower.WarMachine.ScanShadow

noncomputable section

variable {K O S : Type*}

/-- Machine carrier for `scan-learn/status-log-likelihoods`. -/
def machineStatusLogLikelihoods [Fintype K] [Fintype O] [Nonempty O]
    (used : Finset K) (alpha : K → DirichletParams O S) (counts : K → O → ℕ) : S → ℝ :=
  fun s => ∑ k ∈ used, dirichletMultinomialLogPredictive
    (fun o => (alpha k).conc o s) (fun o => (alpha k).pos o s) (counts k)

theorem machineStatusLogLikelihoods_eq [Fintype K] [Fintype O] [Nonempty O]
    (used : Finset K) (alpha : K → DirichletParams O S) (counts : K → O → ℕ) :
    machineStatusLogLikelihoods used alpha counts =
      fun s => scanStatusLogLikelihood used alpha counts s := by rfl

/-- Admitted `scan-learn/step` carrier: the posterior only. The count update of
each used key is `ScanLearning.scanAccumulate` (see `scanAccumulate_conc`) and
is not composed here. -/
def machineScanStep [Fintype S] [DecidableEq S]
    (rho : ℝ) (ll : S → ℝ) (q0 : S → ℝ) := scanPosterior rho ll q0

theorem machineScanStep_eq [Fintype S] [DecidableEq S]
    (rho : ℝ) (ll : S → ℝ) (q0 : S → ℝ) :
    machineScanStep rho ll q0 = scanPosterior rho ll q0 := rfl

/-- One-channel carrier for `scan-bmr/score`: recorded choice and eligibility. -/
def machineScanBmr (floor ticks : ℕ) (deltaTied : ℝ) (hand : HandSetResult) :
    ScanBmrChoice × Prop :=
  let choice := scanBmrChoice deltaTied hand
  (choice, scanBmrEligible floor ticks choice)

theorem machineScanBmr_choice (floor ticks : ℕ) (deltaTied : ℝ) (hand : HandSetResult) :
    (machineScanBmr floor ticks deltaTied hand).1 = scanBmrChoice deltaTied hand := by rfl

theorem machineScanBmr_eligible (floor ticks : ℕ) (deltaTied : ℝ) (hand : HandSetResult) :
    (machineScanBmr floor ticks deltaTied hand).2 =
      scanBmrEligible floor ticks (scanBmrChoice deltaTied hand) := by rfl

/-- Machine carrier for the recorded-only `scan-shadow/shadow-row`. -/
def machineScanShadow [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S] (mu : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) :=
  scanShadow mu used adopted alpha counts

theorem machineScanShadow_eq [Fintype K] [DecidableEq K] [Fintype O] [Nonempty O]
    [Fintype S] [DecidableEq S] (mu : S → ℝ) (used adopted : Finset K)
    (alpha : K → DirichletParams O S) (counts : K → O → ℕ) :
    machineScanShadow mu used adopted alpha counts = scanShadow mu used adopted alpha counts := rfl

#print axioms machineStatusLogLikelihoods_eq
#print axioms machineScanStep_eq
#print axioms machineScanBmr_choice
#print axioms machineScanBmr_eligible
#print axioms machineScanShadow_eq

end
end DarkTower.WarMachine.Proof2.ScanLearningAtMachine
