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
The lift through `prediction`, risk admission and `CascadeEFE.scoreCascade` is
`scoreCascadeCo_toOption_eq_scoreCascade_of_chain` below (added in claude-7's review):
every quantity the score reads depends on the transition only through its masses.
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

/-! ## Lifting the mass bridge to the score (claude-7, review)

Everything `totalG` reads depends on the transition only through its masses:
`push` and `prediction` (after epoch 0) are `finiteKernel`s built from masses,
`risk` and `ambiguity` are mass sums, and the support that `riskAdmissible` reads
is the support of a `push`. So equal transition masses give equal scores, whatever
support lists the two transition kernels carry. -/

theorem push_mass_congr {X Y : Type*} [Fintype X] [Fintype Y]
    (q : ProbabilityKernel Unit X) (b b' : ProbabilityKernel X Y)
    (h : ∀ x y, b.mass x y = b'.mass x y) : push q b = push q b' := by
  have hf : (fun (_ : Unit) y => ∑ x, q.mass () x * b.mass x y) =
      (fun (_ : Unit) y => ∑ x, q.mass () x * b'.mass x y) := by
    funext _ y; simp [h]
  unfold push
  congr 1

theorem prediction_mass_congr {X : Type*} [Fintype X]
    (q : ProbabilityKernel Unit X) (b b' : ProbabilityKernel X X)
    (h : ∀ x y, b.mass x y = b'.mass x y) : ∀ t, prediction q b t = prediction q b' t
  | 0 => rfl
  | t + 1 => by
    show push (prediction q b t) b = push (prediction q b' t) b'
    rw [prediction_mass_congr q b b' h t]
    exact push_mass_congr _ b b' h

/-- The legacy policy kernel does not read the observation channel, so the
candidate's model and the token model give the same transition. -/
theorem policyKernel_candidate_eq {ι V : Type} [Fintype ι] [DecidableEq ι]
    [Fintype V] [DecidableEq V] (pat : ι → InterpretedPattern V) (candidate : Candidate ι V)
    (start : Finset V) (goal : V) (pi : Policy ι) :
    policyKernel (modelOfCandidate pat candidate) pi = policyKernel (modelOf pat start goal) pi := by
  have hres : ∀ l, resolve (modelOfCandidate pat candidate) l = resolve (modelOf pat start goal) l := by
    intro l
    induction l with
    | nil => rfl
    | cons p ps ih => rw [resolve, resolve, ih]; rfl
  have hch : ∀ bs (x : Finset V), choose (modelOfCandidate pat candidate) bs x =
      choose (modelOf pat start goal) bs x := by
    intro bs x
    induction bs with
    | nil => rfl
    | cons pb rest ih =>
      obtain ⟨p, b⟩ := pb
      rw [choose, choose, ih]; rfl
  unfold policyKernel
  rw [hres]
  cases resolve (modelOf pat start goal) (firing pi) with
  | none => rfl
  | some bs => simp only [hch]

/-- **The bridge at the score.** On a chain, the co-application score and the real
`CascadeEFE.scoreCascade` give the same value, and refuse together (on a chain, the
only refusal either can make is inadmissible risk). -/
theorem scoreCascadeCo_toOption_eq_scoreCascade_of_chain {ι V : Type} [Fintype ι]
    [DecidableEq ι] [Fintype V] [DecidableEq V]
    (candidate : Candidate ι V) (pat : ι → InterpretedPattern V)
    (hp : candidate.patterns = some pat) (acyclic : acyclicDescent (containmentOrder pat))
    (precedence : List ι)
    (hchain : Proof2.CoApplicationKernel.chainCondition pat (containmentOrder pat)
      (precedence.map pat)) (start : Finset V) (goal : V) (H : ℕ)
    (c : Fin H → ProbabilityKernel Unit CTauClassPreference.EndingClass) :
    (scoreCascadeCo candidate H c).toOption =
      (CascadeEFE.scoreCascade (modelOfCandidate pat candidate)
        (policyOf pat acyclic precedence) H c).toOption := by
  classical
  obtain ⟨b, hb, -⟩ := co_mass_eq_policyKernel_of_chain pat start goal acyclic precedence
    hchain ∅ ∅
  have hmass : ∀ x y, (coKernel pat).mass x y = b.mass x y := fun x y => by
    obtain ⟨b', hb', hm⟩ := co_mass_eq_policyKernel_of_chain pat start goal acyclic precedence
      hchain x y
    rw [hb] at hb'; cases hb'; exact hm
  have hpred := prediction_mass_congr candidate.initial (coKernel pat) b hmass
  have hb2 : policyKernel (modelOfCandidate pat candidate) (policyOf pat acyclic precedence) =
      some b := by rw [policyKernel_candidate_eq pat candidate start goal]; exact hb
  unfold scoreCascadeCo CascadeEFE.scoreCascade scoreWithKernel
  simp only [hp, acyclic, dite_true, hb2]
  show (if h : ∀ t : Fin H, PreferenceRiskSeparation.riskAdmissible
      (push (prediction candidate.initial (coKernel pat) (t.val + 1)) candidate.observation) (c t)
      then Except.ok (totalG candidate.initial (coKernel pat) candidate.observation H c h)
      else Except.error CascadeCoApplyG.Refusal.inadmissibleRisk).toOption =
    (if h : ∀ t : Fin H, PreferenceRiskSeparation.riskAdmissible
      (push (prediction candidate.initial b (t.val + 1)) candidate.observation) (c t)
      then Except.ok (totalG candidate.initial b candidate.observation H c h)
      else Except.error CascadeEFE.Refusal.inadmissibleRisk).toOption
  have hfun : (fun t : ℕ => prediction candidate.initial (coKernel pat) t) =
      (fun t => prediction candidate.initial b t) := funext hpred
  simp only [CascadeEFE.totalG, CascadeEFE.stepG, CascadeEFE.risk, CascadeEFE.ambiguity, hpred]
  split_ifs <;> rfl

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
#print axioms scoreCascadeCo_toOption_eq_scoreCascade_of_chain

end DarkTower.WarMachine.CascadeCoApplyGBridge
