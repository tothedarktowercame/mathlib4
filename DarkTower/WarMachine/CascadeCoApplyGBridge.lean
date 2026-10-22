import DarkTower.WarMachine.CascadeCoApplyG
import DarkTower.WarMachine.CascadeScoringExamples

/-!
# Bridge from `CascadeEFE.scoreCascade` to the token-state list kernel

Friston et al. specify policy-conditioned transitions, `P(s[t+1] | s[t], π)`
(`refs/friston2017.txt:323-340`).  This module does not add a second
interpretation carrier: `modelOf` is the token-state construction already used
by `CascadeScoringExamples`.  The modelling choice is that the same
`InterpretedPattern` supplies both that list model and co-application.

`ProbabilityKernel` includes a support list as well as masses.  The legacy
`policyKernel` preserves the selected pattern's finite support; `listKernel`
uses full finite support.  Thus the bridge proves equality of all transition
masses, rather than a false structural equality of support representations.
Lifting that mass relation through `prediction`, support-sensitive risk
admission, and `CascadeEFE.scoreCascade` is intentionally not claimed here.
-/

namespace DarkTower.WarMachine.CascadeCoApplyGBridge

open DarkTower.WarMachine.Holes
open DarkTower.WarMachine.CascadeEFE
open DarkTower.WarMachine.CascadeTransition
open DarkTower.WarMachine.CascadeCoApplyG
open DarkTower.WarMachine.Proof2.ContainmentOrder
open DarkTower.WarMachine.CascadeScoringExamples

noncomputable section

def modelOf {ι V : Type} [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (start : Finset V) (goal : V) :
    Model ι (Finset V) Bool :=
  model pat start goal

/-- The same interpreted-pattern construction with the candidate's actual
observation channel.  This changes only the observation codomain; it does not
introduce another pattern interpretation carrier. -/
def modelOfCandidate {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (candidate : Candidate ι V) :
    Model ι (Finset V) CTauClassPreference.EndingClass where
  initial := candidate.initial
  observation := candidate.observation
  guard := fun p s => decide (CascadeTransition.guard (pat p) s)
  interpretation := fun p => some (patK (pat p))

def policyOf {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (acyclic : acyclicDescent (containmentOrder pat))
    (precedence : List ι) : Policy ι where
  cascade := { nodes := {p | p ∈ precedence}, addedByOrganise := ∅
               edges := containmentOrder pat, acyclic := acyclic, precedence := precedence }
  nodeDecidable := fun p => inferInstanceAs (Decidable (p ∈ precedence))

theorem firing_policyOf {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (acyclic : acyclicDescent (containmentOrder pat))
    (precedence : List ι) : firing (policyOf pat acyclic precedence) = precedence := by
  simp [firing, policyOf]

theorem choose_mass_eq_cascadeKernel {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (start : Finset V) (goal : V)
    (precedence : List ι) (s s' : Finset V) :
    (choose (modelOf pat start goal)
      (precedence.map fun p => (p, patK (pat p))) s).mass () s' =
      cascadeKernel (precedence.map pat) s s' := by
  induction precedence with
  | nil => simp [choose, cascadeKernel, firstEnabled, point, finiteKernel]
  | cons p ps ih =>
    by_cases enabled : guard (pat p) s
    · simp [choose, cascadeKernel, firstEnabled, modelOf, model, enabled, patK, finiteKernel]
    · simpa [choose, cascadeKernel, firstEnabled, modelOf, model, enabled] using ih

theorem policyKernel_mass_eq_listKernel {ι V : Type} [Fintype ι] [DecidableEq ι] [Fintype V] [DecidableEq V]
    (pat : ι → InterpretedPattern V) (start : Finset V) (goal : V)
    (acyclic : acyclicDescent (containmentOrder pat)) (precedence : List ι)
    (s s' : Finset V) :
    ∃ b, policyKernel (modelOf pat start goal) (policyOf pat acyclic precedence) = some b ∧
      b.mass s s' = (listKernel pat precedence).mass s s' := by
  have hr : resolve (modelOf pat start goal) precedence =
      some (precedence.map fun p => (p, patK (pat p))) := by
    simpa [modelOf] using resolve_model pat start goal precedence
  unfold policyKernel
  rw [firing_policyOf, hr]
  refine ⟨_, rfl, ?_⟩
  exact choose_mass_eq_cascadeKernel pat start goal precedence s s'

/-- Refusal translation from the co-score to the legacy scorer.  The bridge
has no image for `cyclicContainment`: `policyOf` requires acyclicity before a
legacy policy can be constructed, so that refusal is deliberately absent from
the legacy codomain rather than being mislabeled as inadmissible risk. -/
def toLegacyRefusal : CascadeCoApplyG.Refusal → Option CascadeEFE.Refusal
  | .missingInterpretation => some .missingInterpretation
  | .inadmissibleRisk => some .inadmissibleRisk
  | .cyclicContainment => none

/-- On a chain, the co-kernel and the actual legacy policy kernel have the
same transition masses.  This is the bridge needed before lifting the result
through `prediction`, risk admission, and `CascadeEFE.scoreCascade` itself. -/
theorem co_mass_eq_policyKernel_of_chain {ι V : Type} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V) (start : Finset V) (goal : V)
    (acyclic : acyclicDescent (containmentOrder pat)) (precedence : List ι)
    (hchain : Proof2.CoApplicationKernel.chainCondition pat (containmentOrder pat)
      (precedence.map pat)) (s s' : Finset V) :
    ∃ b, policyKernel (modelOf pat start goal) (policyOf pat acyclic precedence) = some b ∧
      (coKernel pat).mass s s' = b.mass s s' := by
  obtain ⟨b, hb, hmass⟩ := policyKernel_mass_eq_listKernel pat start goal acyclic precedence s s'
  refine ⟨b, hb, ?_⟩
  rw [coKernel_eq_listKernel_of_chain pat precedence hchain]
  exact hmass.symm

/-! ## Reversed-precedence control

Reversing a *chain* list does not break the mass bridge: at each state there
is still only one enabled pattern, so both `choose` and `cascadeKernel` skip
disabled/achieved entries identically.  What it does not establish is an
arbitrary-order comparison law; the non-chain `join3` control in
`CascadeCoApplyG.join3_co_differs_from_list` remains the theorem that blocks
that generalisation.
-/

theorem reversed_chain_still_has_list_mass_bridge (s s' : Finset CascadeScoringExamples.Tok) :
    ∃ b, policyKernel (modelOf CascadeScoringExamples.chain3 ∅ 3)
      (policyOf CascadeScoringExamples.chain3
        (acyclicDescent_of_stratification _ CascadeScoringExamples.s3) [0, 1, 2]) = some b ∧
      b.mass s s' = (listKernel CascadeScoringExamples.chain3 [0, 1, 2]).mass s s' :=
  policyKernel_mass_eq_listKernel _ _ _
    (acyclicDescent_of_stratification _ CascadeScoringExamples.s3) _ _ _

end
end DarkTower.WarMachine.CascadeCoApplyGBridge
