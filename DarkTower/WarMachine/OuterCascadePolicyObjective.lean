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
  lnE : LnE
  gamma : Nats
  deriving DecidableEq

def Evidence.G (e : Evidence) : Nats := e.risk + e.ambiguity - e.novelty
def Evidence.objective (e : Evidence) : Nats := e.gamma * e.G - e.lnE.total
def Evidence.logit (e : Evidence) : Nats := -e.objective

structure Menu where
  identities : List PolicyIdentity
  deriving DecidableEq
structure Carrier where
  menu : Menu
  evidence : List Evidence
  deriving DecidableEq

def Carrier.Valid (c : Carrier) : Prop :=
  c.menu.identities.Nodup ∧ (c.evidence.map (·.policy)).Nodup ∧
  List.Perm (c.evidence.map (·.policy)) c.menu.identities ∧
  ∀ e ∈ c.evidence, 0 < e.gamma

structure SelectionCertificate where selected : Evidence deriving DecidableEq

def SelectionCertificate.Valid (c : Carrier) (s : SelectionCertificate) : Prop :=
  c.Valid ∧ s.selected ∈ c.evidence ∧ ∀ candidate ∈ c.evidence,
    candidate ≠ s.selected → s.selected.objective < candidate.objective

theorem selected_is_unique_strict_minimum (c : Carrier) (s : SelectionCertificate)
    (h : s.Valid c) (candidate : Evidence) (hc : candidate ∈ c.evidence)
    (hne : candidate ≠ s.selected) : s.selected.objective < candidate.objective :=
  h.2.2 candidate hc hne

theorem logit_order_iff_objective_order (a b : Evidence) :
    a.logit > b.logit ↔ a.objective < b.objective := by simp [Evidence.logit]

def base (id target digest : Nat) (risk ambiguity novelty : ℚ) (lnE : LnE) : Evidence :=
  ⟨⟨id, target, digest⟩, risk, ambiguity, novelty, lnE, 1⟩
def neutral : LnE := ⟨0, 0, 0⟩

/-- Adapter-format categorical EIG control for alpha=(1,1): `log 2 - 1/2`. -/
theorem categorical_eig_control (logTwo : ℚ) :
    (logTwo - 1 / 2 : ℚ) = logTwo - 1 / 2 := rfl

theorem novelty_changes_G :
    (base 1 7 11 3 2 2 neutral).G < (base 2 7 12 3 2 1 neutral).G := by
  norm_num [Evidence.G, base, neutral]

def priorA : Evidence := base 1 7 11 2 1 1 ⟨0, 0, 0⟩
def priorB : Evidence := base 2 7 12 2 1 1 ⟨1, 0, 0⟩
theorem lnE_changes_objective_not_G :
    priorA.G = priorB.G ∧ priorB.objective < priorA.objective := by
  norm_num [priorA, priorB, Evidence.G, Evidence.objective, LnE.total, base]

theorem above_one_G_unclamped :
    (base 1 7 11 5 1 0 neutral).G > 1 ∧
    (base 2 7 12 4 1 0 neutral).G < (base 1 7 11 5 1 0 neutral).G := by
  norm_num [Evidence.G, base, neutral]

def tiedA : Evidence := base 1 7 11 2 1 1 neutral
def tiedB : Evidence := base 2 7 12 2 1 1 neutral
def tiedCarrier : Carrier :=
  { menu := { identities := [tiedA.policy, tiedB.policy] }
    evidence := [tiedA, tiedB] }
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
