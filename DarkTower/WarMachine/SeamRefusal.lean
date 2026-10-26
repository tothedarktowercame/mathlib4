import Mathlib.Tactic

/-!
# Typed values across a seam (defect lines R6, R9)

Source: `~/notes/wm-next/outer-selection/DEFECTS-reading-era.md` R6, R9
(claude-9, 2026-10-26).

R6.  A refusal at a seam carries the producer's reason and cause unchanged; a
consumer may wrap but not rename or drop.  Observed on machinery-142
attempt-002 (`002-selection.edn`): the learning state's belief retains
`:status :refused :reason :learning-authority-unavailable` with `:details`
(`ClassCastException`, "Default comparator requires nil, Number, or Comparable:
#{}"); the policy the selection read is a fresh
`{:status :refused :reason :learning-authority-unavailable :kind
:cascade-live-policy-menu-v1}` with no details.  The consumer also maps every
non-produced belief, including `:learning-authority-schema-invalid`, to the
same reason.

R9.  The authored answer at the held-cascade seam has a function type; a
non-function value is a typed refusal there, not a downstream protocol
failure.  Observed on the fc464172 resume (2026-10-23, zai-2 job
`invoke-1792764980051-2660-61df01f8`): the answer named `"var": "clauses"`, a
bare `def` map, and the failure surfaced later as a protocol error.  Repair
futon2 `ae9e71584` exists; this clause pins it.
-/

namespace DarkTower.WarMachine.SeamRefusal

abbrev Id := Nat

/-- The producer's belief (`outer_learning_runtime/load-shadow`): produced with
its source pin, or refused with a reason and the retained cause (the digest of
`:details`). -/
inductive ProducerBelief where
  | produced (sourcePin : Id)
  | refused (reason : Id) (cause : Id)
  deriving DecidableEq, Repr

/-- The consumer's output (`outer_policy_provider_runtime/provide`).  The cause
slot is `Option` on purpose: the observed consumer map has no such key, and
`Carries` requires it to be present.  `wrapper` is the consumer's own tag
(`:kind`), which it may add. -/
inductive ConsumerOutcome where
  | produced (sourcePin : Id)
  | refused (reason : Id) (cause : Option Id) (wrapper : Option Id)
  deriving DecidableEq, Repr

def carries : ProducerBelief → ConsumerOutcome → Bool
  | .produced p, .produced q => p == q
  | .refused r c, .refused r' c' _ => r' == r && c' == some c
  | _, _ => false

/-- R6.  The consumer carries the producer's value: the same pin when produced;
when refused, the same reason and the cause present and equal.  Wrapping is
free; renaming and dropping are not. -/
def Carries (p : ProducerBelief) (c : ConsumerOutcome) : Prop := carries p c = true

instance (p : ProducerBelief) (c : ConsumerOutcome) : Decidable (Carries p c) := by
  unfold Carries
  infer_instance

theorem dropped_cause_not_carried (r c : Id) (w : Option Id) :
    ¬ Carries (.refused r c) (.refused r none w) := by
  simp [Carries, carries]

theorem renamed_reason_not_carried (r r' c : Id) (c' w : Option Id) (h : r' ≠ r) :
    ¬ Carries (.refused r c) (.refused r' c' w) := by
  simp [Carries, carries, h]

theorem wrapped_refusal_carried (r c : Id) (w : Option Id) :
    Carries (.refused r c) (.refused r (some c) w) := by
  simp [Carries, carries]

/-- A refusal is never carried as a production, whatever the pin. -/
theorem refusal_not_carried_as_produced (r c q : Id) :
    ¬ Carries (.refused r c) (.produced q) := by
  simp [Carries, carries]

/-! ### Control: machinery-142 attempt-002

Reason ids: 1 `:learning-authority-unavailable`, 2 `:learning-authority-schema-invalid`.
Cause 7 stands for the digest of the retained `:details` map (path, error class,
error message); wrapper 3 for `:kind :cascade-live-policy-menu-v1`. -/

def m142Producer : ProducerBelief := .refused 1 7
def m142Consumer : ConsumerOutcome := .refused 1 none (some 3)

theorem m142_not_carried : ¬ Carries m142Producer m142Consumer := by decide

/-- The same join wording applied to a schema-invalid belief renames it. -/
theorem m142_schema_invalid_collapsed :
    ¬ Carries (.refused 2 9) m142Consumer := by decide

/-- What the repair produces: details passed through, the kind tag kept. -/
theorem m142_repaired_carried :
    Carries m142Producer (.refused 1 (some 7) (some 3)) := by decide

/-! ## R9: the authored answer must be a function -/

/-- The value shape the loader resolves the named var to. -/
inductive AuthoredValue where
  | function
  | map
  | set
  | keyword
  deriving DecidableEq, Repr

inductive LoaderRefusal where
  | patchVarUnavailable
  | patchVarNotAFunction
  deriving DecidableEq, Repr

inductive LoaderOutcome where
  | loaded (var : Id)
  | refused (reason : LoaderRefusal)
  deriving DecidableEq, Repr

/-- Resolution at the seam is a function of the value's shape.  `none` is a var
that does not resolve. -/
def resolve (var : Id) : Option AuthoredValue → LoaderOutcome
  | none => .refused .patchVarUnavailable
  | some .function => .loaded var
  | some _ => .refused .patchVarNotAFunction

/-- A loader record claims an outcome for an authored value; it is valid only
when the outcome is what resolution gives. -/
def LoaderClaim.Valid (var : Id) (authored : Option AuthoredValue)
    (claim : LoaderOutcome) : Prop :=
  claim = resolve var authored

instance (var : Id) (authored : Option AuthoredValue) (claim : LoaderOutcome) :
    Decidable (LoaderClaim.Valid var authored claim) := by
  unfold LoaderClaim.Valid
  infer_instance

theorem non_function_never_loaded (var : Id) (v : AuthoredValue) (h : v ≠ .function) :
    resolve var (some v) ≠ .loaded var := by
  cases v <;> simp_all [resolve]

theorem non_function_loaded_claim_invalid (var : Id) (v : AuthoredValue)
    (h : v ≠ .function) : ¬ LoaderClaim.Valid var (some v) (.loaded var) := by
  unfold LoaderClaim.Valid
  exact fun hc => non_function_never_loaded var v h hc.symm

/-! ### Control: the fc464172 resume

Var 41 stands for `futon2.aif.wm.authored.req-fbad4b8b/clauses`, a `def` map. -/

theorem fc464172_loaded_claim_invalid :
    ¬ LoaderClaim.Valid 41 (some .map) (.loaded 41) := by decide

theorem fc464172_refused_at_seam :
    resolve 41 (some .map) = .refused .patchVarNotAFunction := rfl

/-- The three `ifn?` shapes the repair refuses synthetically. -/
theorem ifn_shapes_refused :
    resolve 41 (some .map) = .refused .patchVarNotAFunction ∧
    resolve 41 (some .set) = .refused .patchVarNotAFunction ∧
    resolve 41 (some .keyword) = .refused .patchVarNotAFunction := by decide

end DarkTower.WarMachine.SeamRefusal
