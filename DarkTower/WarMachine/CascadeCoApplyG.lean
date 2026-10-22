import DarkTower.WarMachine.CascadeEFE
import DarkTower.WarMachine.CascadeCoScoringExamples
import DarkTower.WarMachine.CTauClassPreference
import DarkTower.WarMachine.Proof2.CoApplicationKernel
import DarkTower.WarMachine.Proof2.ContainmentOrder

/-!
# Co-application expected free energy at one comparison horizon

Da Costa et al. define expected free energy as a sum over future epochs
`τ` (`refs/dacosta2020.txt:1403`, equation 42).  Friston et al. define a
policy by its action at each epoch, `u = π(t)`
(`refs/friston2017.txt:323-340`, equation 2.1).  Those sources state the
epoch-wise horizon; they do not choose this module's finite carrier, its
containment order, or the 55/35/5/5 class schedule.  We model one comparison
by giving every candidate the same `H`, and use the ruled class schedule from
`CTauClassPreference` at epoch `t + 1`.  In particular, we do not normalise by
candidate length.

The live cascade route currently takes a pattern-count-derived horizon per
candidate (`futon2/src/futon2/aif/cascade_shape_g.clj:310`).  This module is a
specification of SPEC U2(a), not a claim that the live route conforms.

The transition is the enabled-frontier co-application kernel, not
`CascadeEFE.policyKernel`'s first-enabled list kernel.  A non-acyclic
containment order is a typed refusal; it is never silently scored by the list
kernel.
-/

namespace DarkTower.WarMachine.CascadeCoApplyG

open scoped BigOperators
open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CTauClassPreference
open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.Proof2.CoApplicationKernel

noncomputable section

inductive Refusal where
  | missingInterpretation
  | inadmissibleRisk
  | cyclicContainment
  deriving DecidableEq, Repr

/-- A candidate supplies its interpreted patterns, state prior, and class
observation kernel.  `none` preserves `CascadeEFE.scoreCascade`'s explicit
missing-interpretation refusal. -/
structure Candidate (ι V : Type*) [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] where
  patterns : Option (ι → InterpretedPattern V)
  initial : ProbabilityKernel Unit (Finset V)
  observation : ProbabilityKernel (Finset V) EndingClass

def coKernel {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) : ProbabilityKernel (Finset V) (Finset V) :=
  finiteKernel (coApplyKernel pat (containmentOrder pat))
    (coApplyKernel_nonneg pat (containmentOrder pat))
    (coApplyKernel_rowsum pat (containmentOrder pat))

def listKernel {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (precedence : List ι) :
    ProbabilityKernel (Finset V) (Finset V) :=
  finiteKernel (fun s s' => cascadeKernel (precedence.map pat) s s')
    (cascadeKernel_nonneg (precedence.map pat))
    (cascadeKernel_rowsum (precedence.map pat))

/-- The finite class preference at one member of a positive horizon. -/
def classKernel (H : ℕ) (t : Fin H) : ProbabilityKernel Unit EndingClass :=
  { support := fun _ => [.focused, .related, .unrelated, .stopTheLine, .notYetEvaluated]
    mass := fun _ ending => (classPreference H (t.val + 1) ending : ℝ)
    nonnegative := by
      have hH : 1 ≤ H := Nat.succ_le_iff.mpr
        (lt_of_le_of_lt (Nat.zero_le t.val) t.isLt)
      have ht : 1 ≤ t.val + 1 := Nat.succ_le_succ (Nat.zero_le t.val)
      have hle : t.val + 1 ≤ H := Nat.succ_le_iff.mpr t.isLt
      intro _ ending
      exact_mod_cast (classPreference_probability H (t.val + 1) hH ht hle).1 ending
    normalised := by
      intro _
      by_cases terminal : t.val + 1 = H
      · norm_num [classPreference, terminal, terminalPreference]
      · norm_num [classPreference, terminal, waitingPreference]
    support_nodup := by decide
    mass_eq_zero_of_not_mem := by
      intro _ ending h
      cases ending <;> simp_all }

def scoreWithKernel {V : Type*} [Fintype V] [DecidableEq V]
    (initial : ProbabilityKernel Unit (Finset V))
    (observation : ProbabilityKernel (Finset V) EndingClass)
    (transition : ProbabilityKernel (Finset V) (Finset V)) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) : Except Refusal ℝ := by
  classical
  exact if h : ∀ t : Fin H, PreferenceRiskSeparation.riskAdmissible
      (push (prediction initial transition (t.val + 1)) observation) (c t) then
    .ok (totalG initial transition observation H c h)
  else .error .inadmissibleRisk

/-- Co-application scoring with exactly the legacy refusal meanings plus the
new `cyclicContainment` refusal. -/
def scoreCascadeCo {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (candidate : Candidate ι V) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) : Except Refusal ℝ := by
  classical
  exact match candidate.patterns with
  | none => .error .missingInterpretation
  | some pat => if _ : acyclicDescent (containmentOrder pat) then
      scoreWithKernel candidate.initial candidate.observation (coKernel pat) H c
    else .error .cyclicContainment

/-- The old first-enabled comparison, retained only to state the chain
agreement theorem; it is not the canonical score for non-chains. -/
def scoreCascadeList {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (candidate : Candidate ι V) (precedence : List ι) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) : Except Refusal ℝ := by
  classical
  exact match candidate.patterns with
  | none => .error .missingInterpretation
  | some pat => scoreWithKernel candidate.initial candidate.observation (listKernel pat precedence) H c

theorem coKernel_eq_listKernel_of_chain {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V) (precedence : List ι)
    (hchain : chainCondition pat (containmentOrder pat) (precedence.map pat)) :
    coKernel pat = listKernel pat precedence := by
  unfold coKernel listKernel finiteKernel
  congr 1
  funext s s'
  exact coApplyKernel_eq_cascadeKernel_of_chain hchain s s'

theorem scoreCascadeCo_eq_scoreCascadeList_of_chain {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (candidate : Candidate ι V) (precedence : List ι) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit EndingClass) (pat : ι → InterpretedPattern V)
    (hp : candidate.patterns = some pat) (hacyclic : acyclicDescent (containmentOrder pat))
    (hchain : chainCondition pat (containmentOrder pat) (precedence.map pat)) :
    scoreCascadeCo candidate H c = scoreCascadeList candidate precedence H c := by
  simp only [scoreCascadeCo, scoreCascadeList, hp, dif_pos hacyclic]
  rw [coKernel_eq_listKernel_of_chain pat precedence hchain]

/-- The three-pattern join is the concrete non-chain control.  The list score
is `2 log 10 + log (10/9)` (`CascadeScoringExamples.join3_score`), while the
co-applied score is `log 10 + 2 log (10/9)` (`join3_co`), so the two kernels
must not be identified outside the chain theorem. -/
theorem join3_co_differs_from_list :
    totalG (point ∅)
        (CascadeCoScoringExamples.coK CascadeScoringExamples.join3
          (containmentOrder CascadeScoringExamples.join3))
        (CascadeScoringExamples.obsK 3) 3
        (fun _ => CascadeScoringExamples.prefK (9 / 10) (by norm_num) (by norm_num))
        (CascadeCoScoringExamples.adm_all ∅ 3 3) ≠
      2 * Real.log 10 + Real.log (10 / 9) := by
  rw [CascadeCoScoringExamples.join3_co]
  exact ne_of_lt CascadeCoScoringExamples.join_beats_chain

/-- Every element of a comparison uses its supplied common horizon. -/
def compareAtHorizon {ι V : Type*} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (H : ℕ) (cands : List (Candidate ι V)) : List (Except Refusal ℝ) :=
  cands.map fun candidate => scoreCascadeCo candidate H (classKernel H)

theorem compareAtHorizon_uses_H {ι V : Type*} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (H : ℕ) (cands : List (Candidate ι V)) :
    compareAtHorizon H cands = cands.map (fun candidate => scoreCascadeCo candidate H (classKernel H)) := rfl

/-! ## Bad case: the cyclic containment order

If the acyclicity branch in `scoreCascadeCo` were removed, the cyclic pattern
library below would reach `scoreWithKernel` and obtain a numeric score or an
unrelated risk refusal.  The theorem below is the broken safety theorem for
that bad definition: the actual definition returns `cyclicContainment` first.
-/

def cyclicCandidate : Candidate Bool (Fin 2) where
  patterns := some Proof2.ContainmentOrder.cyclePat
  initial := point ∅
  observation := finiteKernel (fun _ ending => if ending = .focused then 1 else 0)
    (by intro _ ending; split_ifs <;> norm_num)
    (by intro; simp)

theorem cyclic_order_refused (H : ℕ) (c : Fin H → ProbabilityKernel Unit EndingClass) :
    scoreCascadeCo cyclicCandidate H c = .error .cyclicContainment := by
  simp [scoreCascadeCo, cyclicCandidate, Proof2.ContainmentOrder.twoPatternCycleIsNotAcyclic]

end
end DarkTower.WarMachine.CascadeCoApplyG
