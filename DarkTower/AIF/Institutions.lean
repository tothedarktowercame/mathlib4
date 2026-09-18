import DarkTower.AIF.Terms

/-!
# Institutions inside AIF — the IAD adjudication

Commissioned by Joe, 2026-09-18: design requirements unfold from the apex
thesis (`futon2:holes/labs/wm-contract/runs/U88-cascade-live/apex-thesis-pinned.json`,
in force 2026-09-06 — "Can a community of humans and machines doing
open-ended work leave an account of itself structured enough that the work
can steer itself — so that activity becomes inference rather than
motion?"; clusters A "records carry warrant", B "one queryable
self-account", C "feedback reaches every participant", D "accountable
next-action choice"). These requirements bind *specific kinds of work*,
not everything universally — which is what institutions are for — and
Joe's preference is partly about *how* outcomes are pursued
(`futon2:holes/NOTE-joes-view-of-C.md` §1, Half 2). The question put to
this module: **can Ostrom's IAD specifically fit inside the declared AIF
formalism?**

## Verdict: partial fit, with a precise and informative boundary

IAD distinguishes three levels of rules. They land differently:

1. **Operational level — FITS, inside the census.** A rule-in-use in the
   Crawford–Ostrom grammar (Attributes·Deontic·aIm·Condition·Or-else) types
   over the census as `InstitutionalStatement` below. Its force has exactly
   four AIF-native landing sites, all census objects:
   - *policy-set boundary*: must/must-not prunes Π (prior support — a
     prior, so AIF-native);
   - *habit prior E*: soft habitual force;
   - *preference C via sanction*: a RULE (statement with or-else) is one
     whose sanction outcomes the generative model realises and C
     dis-prefers — the norm/rule distinction (sanctionless/sanctioned) is
     therefore *typed*: a norm's force is only preferential, a rule's
     passes through the model;
   - *guards in B*: condition-scoped impossibility (the machine's
     `CascadeTransition.guard` is already this).
   These are the three enforcement grades Joe named on 2026-09-17
   (peripheral impossibility / institutional check-and-deny / soft
   preference), plus the habit channel.

2. **Trajectory-grain requirements — FIT VIA AUGMENTATION (`Monitor`).**
   Cluster-A/C-style requirements ("every record carried warrant",
   "feedback reached every participant") are predicates over
   *trajectories*, and do not decompose as `Σ_τ C_τ(o_τ)`. The standard
   remedy is typed below: an institutional `Monitor` (bookkeeping
   automaton) rides along in the state and — crucially — in the
   *observation*; the augmented model is again a `ForwardModel`, the
   trajectory predicate becomes a *state* property of the monitor, and the
   requirement becomes ordinary step-preference on the augmented outcome
   space (`Preference.withInstitution`). The two marginal theorems prove
   the augmentation is conservative: the institution *observes* the work,
   it does not change the physics.

3. **The enabling condition, made formal.** AIF preferences live on
   observations. So institutional preference can steer behaviour **only
   if compliance is observed** — the monitor state must be lifted into
   `O`. Cluster A ("records carry warrant") is therefore not one
   requirement among four: it is the *precondition* for institutional
   steering of any kind in this formalism. If the account is not in the
   record, no C can prefer it.

4. **Collective-choice level — PARTIAL, lands in learning.** Rules about
   changing operational rules are *model revision* (the monitor, the
   sanctions, the guards are parameters/structure of the generative
   model). Inside AIF that is the learning layer (Dirichlet accumulation,
   model reduction) — currently `:learning` is unruled in the registry, so
   this is honestly OPEN, not claimed.

5. **Constitutional level — DOES NOT fit inside the model, and should
   not.** Who may change the rules of rule-change is, in this stack, the
   operator's ruling ("ruling as the fixing act", C591). Formally it is
   outside any fixed generative model. IAD *predicts* an outermost level
   that the model cannot internalise; the stack has one. The fit fails
   here in exactly the way IAD says something must.

Deliberate scope limits: single-agent. IAD's multi-participant action
situations (positions, boundary and aggregation rules) belong to the
R11 hierarchical/shared-budget layer — OPEN pointer, not claimed here.
-/

namespace DarkTower.AIF

open DarkTower.WarMachine.PolicyRollout

variable {S O U : Type*} [Fintype S] [DecidableEq S] [Fintype O] [DecidableEq O]

/-! ## Deontics and institutional statements (operational level) -/

/-- Crawford–Ostrom deontic operators: permitted, obliged, forbidden. -/
inductive Deontic
  | may
  | must
  | mustNot
  deriving DecidableEq, Repr

/-- An institutional statement over the census types — the ADIC core of the
Crawford–Ostrom grammar. `condition` is the Condition (and, single-agent,
the Attributes); `aim` is the aIm, a class of actions. A statement with a
sanction (`Rule` below) adds the Or-else. -/
structure InstitutionalStatement (S U : Type*) where
  /-- When/where the statement binds (state predicate). -/
  condition : S → Prop
  /-- The action class the deontic governs. -/
  aim : U → Prop
  deontic : Deontic

/-- One-step violation: the statement binds and the action defies the
deontic. `may` is never violated — permission only widens. -/
def InstitutionalStatement.violatedAt (stmt : InstitutionalStatement S U)
    (s : S) (u : U) : Prop :=
  stmt.condition s ∧
    match stmt.deontic with
    | .may => False
    | .must => ¬ stmt.aim u
    | .mustNot => stmt.aim u

/-- A norm: institutional force is preferential only (lands in `E` or `C`);
no sanction is realised by the world model. -/
abbrev Norm (S U : Type*) := InstitutionalStatement S U

/-- A rule: an institutional statement whose Or-else is a set of sanction
outcomes the generative model realises (and `C` dis-prefers). The
norm/rule distinction of the grammar is this field's presence. -/
structure Rule (S O U : Type*) extends InstitutionalStatement S U where
  /-- The sanction outcomes (`Or else`). -/
  sanction : Finset O

/-! ## Monitors: trajectory requirements as observable bookkeeping -/

/-- An institutional monitor: bookkeeping as a deterministic automaton over
machine states. `step m s'` is the ledger after the world moves to `s'`.
This is the typed form of a design requirement that binds a *trajectory*
(apex clusters A/C): the monitor tracks satisfaction, and the trajectory
predicate becomes a state property of `M`. -/
structure Monitor (S M : Type*) where
  init : M
  step : M → S → M

variable {M : Type*} [Fintype M] [DecidableEq M]

/-- The augmented generative model: the monitor rides along in the hidden
state AND in the observation — institutional bookkeeping is part of the
record (apex cluster A as a formal precondition: preference lives on
observations, so compliance must be observed to be preferable). -/
def Monitor.augment (mon : Monitor S M) (Mdl : ForwardModel S O U) :
    ForwardModel (S × M) (O × M) U where
  B := fun u p p' => if p'.2 = mon.step p.2 p'.1 then Mdl.B u p.1 p'.1 else 0
  B_nonneg := by
    intro u p p'
    split
    · exact Mdl.B_nonneg u p.1 p'.1
    · exact le_refl 0
  B_rowsum := by
    intro u p
    rw [Fintype.sum_prod_type]
    calc ∑ s' : S, ∑ m' : M,
          (if m' = mon.step p.2 s' then Mdl.B u p.1 s' else 0)
        = ∑ s' : S, Mdl.B u p.1 s' := by
          refine Finset.sum_congr rfl fun s' _ => ?_
          simp [Finset.sum_ite_eq']
      _ = 1 := Mdl.B_rowsum u p.1
  A := fun p q => if q.2 = p.2 then Mdl.A p.1 q.1 else 0
  A_nonneg := by
    intro p q
    split
    · exact Mdl.A_nonneg p.1 q.1
    · exact le_refl 0
  A_colsum := by
    intro p
    rw [Fintype.sum_prod_type]
    calc ∑ o : O, ∑ m' : M, (if m' = p.2 then Mdl.A p.1 o else 0)
        = ∑ o : O, Mdl.A p.1 o := by
          refine Finset.sum_congr rfl fun o _ => ?_
          simp [Finset.sum_ite_eq']
      _ = 1 := Mdl.A_colsum p.1
  q₀ := fun p => if p.2 = mon.init then Mdl.q₀ p.1 else 0
  q₀_nonneg := by
    intro p
    split
    · exact Mdl.q₀_nonneg p.1
    · exact le_refl 0
  q₀_sum := by
    rw [Fintype.sum_prod_type]
    calc ∑ s : S, ∑ m : M, (if m = mon.init then Mdl.q₀ s else 0)
        = ∑ s : S, Mdl.q₀ s := by
          refine Finset.sum_congr rfl fun s _ => ?_
          simp [Finset.sum_ite_eq']
      _ = 1 := Mdl.q₀_sum

/-- Conservativity of the observation model: marginalising the bookkeeping
out of the augmented likelihood recovers the base likelihood exactly. The
institution observes; it does not change what the world shows. -/
theorem Monitor.augment_A_marginal (mon : Monitor S M)
    (Mdl : ForwardModel S O U) (p : S × M) (o : O) :
    ∑ m' : M, (mon.augment Mdl).A p (o, m') = Mdl.A p.1 o := by
  simp [Monitor.augment, Finset.sum_ite_eq']

/-- Conservativity of the dynamics: marginalising the bookkeeping out of
the augmented transition recovers the base transition exactly. -/
theorem Monitor.augment_B_marginal (mon : Monitor S M)
    (Mdl : ForwardModel S O U) (u : U) (p : S × M) (s' : S) :
    ∑ m' : M, (mon.augment Mdl).B u p (s', m') = Mdl.B u p.1 s' := by
  simp [Monitor.augment, Finset.sum_ite_eq']

/-! ## Institutional preference on the augmented outcomes -/

/-- Institutional preference: base outcome preference plus a step-indexed
weight on the monitor's ledger. A trajectory-grain design requirement,
tracked by its monitor, becomes ordinary step-preference here — inside the
book's `G`, no new functional. -/
def Preference.withInstitution (C : Preference O) (w : ℕ → M → ℝ) :
    Preference (O × M) :=
  ⟨fun τ q => C.log τ q.1 + w τ q.2⟩

omit [Fintype O] [DecidableEq O] [Fintype M] [DecidableEq M] in
@[simp] theorem Preference.withInstitution_log (C : Preference O)
    (w : ℕ → M → ℝ) (τ : ℕ) (o : O) (m : M) :
    (C.withInstitution w).log τ (o, m) = C.log τ o + w τ m := rfl

end DarkTower.AIF
