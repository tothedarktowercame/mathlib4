import Mathlib.Data.Rat.Defs
import Mathlib.Tactic

namespace DarkTower.WarMachine.OuterCascadePolicyObjective
abbrev Id := Nat
abbrev Nats := ℚ

structure PolicyIdentity where
  occurrencePolicy : Id
  target : Id
  cascadeDigest : Id
  deriving DecidableEq

/-- Exact rational adapter for categorical Dirichlet one-observation EIG.
The persisted `psi`/`log` evaluations make the nats formula executable. -/
structure InformationCertificate where
  policy : PolicyIdentity
  alpha : List ℚ
  alphaTotal : ℚ
  probability : List ℚ
  psiSucc : List ℚ
  logProbability : List ℚ
  psiTotalSucc : ℚ
  eig : ℚ
  unitsNats : Bool
  deriving DecidableEq

def InformationCertificate.formula (i : InformationCertificate) : ℚ :=
  (List.zipWith (fun p x => p * (x.1 - x.2))
    i.probability (List.zip i.psiSucc i.logProbability)).sum - i.psiTotalSucc

def InformationCertificate.Valid (i : InformationCertificate) : Prop :=
  i.alpha ≠ [] ∧ (∀ a ∈ i.alpha, 0 < a) ∧
  i.alphaTotal = i.alpha.sum ∧
  i.probability = i.alpha.map (fun a => a / i.alphaTotal) ∧
  i.psiSucc.length = i.alpha.length ∧
  i.logProbability.length = i.alpha.length ∧
  i.eig = i.formula ∧ 0 ≤ i.eig ∧ i.unitsNats = true

instance (i : InformationCertificate) : Decidable i.Valid := by
  unfold InformationCertificate.Valid InformationCertificate.formula
  infer_instance

structure LnE where
  resource : Nats
  cadence : Nats
  continuation : Nats
  deriving DecidableEq
def LnE.total (e : LnE) : Nats := e.resource + e.cadence + e.continuation

structure Evidence where
  policy : PolicyIdentity
  risk : Nats
  ambiguity : Nats
  novelty : Nats
  information : InformationCertificate
  lnE : LnE
  gamma : Nats
  deriving DecidableEq

def Evidence.G (e : Evidence) : Nats := e.risk + e.ambiguity - e.novelty
def Evidence.objective (e : Evidence) : Nats := e.gamma * e.G - e.lnE.total
def Evidence.logit (e : Evidence) : Nats := -e.objective
def Evidence.Valid (e : Evidence) : Prop :=
  0 ≤ e.risk ∧ 0 ≤ e.ambiguity ∧ 0 ≤ e.novelty ∧
  e.information.Valid ∧ e.information.policy = e.policy ∧
  e.novelty = e.information.eig ∧ 0 < e.gamma
instance (e : Evidence) : Decidable e.Valid := by unfold Evidence.Valid; infer_instance

structure Menu where
  identities : List PolicyIdentity
  deriving DecidableEq
structure Carrier where
  menu : Menu
  evidence : List Evidence
  deriving DecidableEq
def Carrier.Valid (c : Carrier) : Prop :=
  c.menu.identities ≠ [] ∧ c.menu.identities.Nodup ∧
  (c.evidence.map (·.policy)).Nodup ∧
  List.Perm (c.evidence.map (·.policy)) c.menu.identities ∧
  ∀ e ∈ c.evidence, e.Valid
instance (c : Carrier) : Decidable c.Valid := by unfold Carrier.Valid; infer_instance

structure SelectionCertificate where selected : Evidence deriving DecidableEq
def SelectionCertificate.Valid (s : SelectionCertificate) (c : Carrier) : Prop :=
  c.Valid ∧ s.selected ∈ c.evidence ∧ ∀ candidate ∈ c.evidence,
    candidate ≠ s.selected → s.selected.objective < candidate.objective
instance (s : SelectionCertificate) (c : Carrier) : Decidable (s.Valid c) := by
  unfold SelectionCertificate.Valid; infer_instance

theorem selected_is_unique_strict_minimum (c : Carrier) (s : SelectionCertificate)
    (h : s.Valid c) (candidate : Evidence) (hc : candidate ∈ c.evidence)
    (hne : candidate ≠ s.selected) : s.selected.objective < candidate.objective :=
  h.2.2 candidate hc hne
theorem logit_order_iff_objective_order (a b : Evidence) :
    a.logit > b.logit ↔ a.objective < b.objective := by simp [Evidence.logit]

def uniformInformation (policy : PolicyIdentity) (logTwo : ℚ := 1) : InformationCertificate :=
  { policy := policy, alpha := [1, 1], alphaTotal := 2,
    probability := [1/2, 1/2], psiSucc := [1, 1],
    logProbability := [-logTwo, -logTwo], psiTotalSucc := 3/2,
    eig := logTwo - 1/2, unitsNats := true }
theorem uniform_information_valid (policy : PolicyIdentity) :
    (uniformInformation policy).Valid := by
  simp [uniformInformation, InformationCertificate.Valid, InformationCertificate.formula]
  norm_num
theorem binary_uniform_eig_formula (policy : PolicyIdentity) (logTwo : ℚ) :
    (uniformInformation policy logTwo).formula = logTwo - 1/2 := by
  norm_num [uniformInformation, InformationCertificate.formula]
  ring
theorem categorical_eig_control (policy : PolicyIdentity) :
    (uniformInformation policy).eig = (1 - 1/2 : ℚ) := by norm_num [uniformInformation]
def alteredUniformInformation (policy : PolicyIdentity) : InformationCertificate :=
  { uniformInformation policy with eig := 3/4 }
theorem altered_categorical_eig_invalid (policy : PolicyIdentity) :
    ¬ (alteredUniformInformation policy).Valid := by
  norm_num [alteredUniformInformation, uniformInformation,
    InformationCertificate.Valid, InformationCertificate.formula]

def neutral : LnE := ⟨0, 0, 0⟩
def base (id target digest : Nat) (risk ambiguity novelty : ℚ) (lnE : LnE) : Evidence :=
  let policy : PolicyIdentity := ⟨id, target, digest⟩
  { policy := policy, risk := risk, ambiguity := ambiguity, novelty := novelty,
    information := { uniformInformation policy with eig := novelty }, lnE := lnE, gamma := 1 }
theorem novelty_changes_G :
    (base 1 7 11 3 2 2 neutral).G < (base 2 7 12 3 2 1 neutral).G := by
  norm_num [Evidence.G, base, neutral]
def priorA : Evidence := base 1 7 11 2 1 (1/2) ⟨0, 0, 0⟩
def priorB : Evidence := base 2 7 12 2 1 (1/2) ⟨1, 0, 0⟩
theorem lnE_changes_objective_not_G :
    priorA.G = priorB.G ∧ priorB.objective < priorA.objective := by
  norm_num [priorA, priorB, Evidence.G, Evidence.objective, LnE.total, base]
theorem above_one_G_unclamped :
    (base 1 7 11 5 1 (1/2) neutral).G > 1 ∧
    (base 2 7 12 4 1 (1/2) neutral).G < (base 1 7 11 5 1 (1/2) neutral).G := by
  norm_num [Evidence.G, base, neutral]

def tiedA : Evidence := base 1 7 11 2 1 (1/2) neutral
def tiedB : Evidence := base 2 7 12 2 1 (1/2) neutral
def tiedCarrier : Carrier :=
  { menu := { identities := [tiedA.policy, tiedB.policy] }, evidence := [tiedA, tiedB] }
def tiedSelection : SelectionCertificate := ⟨tiedA⟩
theorem exact_tie_invalid : ¬ tiedSelection.Valid tiedCarrier := by
  intro h
  have hlt := h.2.2 tiedB (by simp [tiedCarrier]) (by decide)
  norm_num [Evidence.objective, Evidence.G, LnE.total, tiedSelection,
    tiedA, tiedB, base, neutral] at hlt

def Projects (selected : Evidence) (policy target digest : Id) : Prop :=
  selected.policy = ⟨policy, target, digest⟩
theorem digest_substitution_invalid (e : Evidence) (policy target digest' : Id)
    (h : digest' ≠ e.policy.cascadeDigest) : ¬ Projects e policy target digest' := by
  intro hp
  have hd := congrArg PolicyIdentity.cascadeDigest hp
  exact h hd.symm

end DarkTower.WarMachine.OuterCascadePolicyObjective
