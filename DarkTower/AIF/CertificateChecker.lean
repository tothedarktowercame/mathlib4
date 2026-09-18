import DarkTower.AIF.Certificates

/-!
# Executable checker for run certificates — the green half of the witness lane

`DarkTower/AIF/Certificates.lean` (frozen core) states what a valid
`GCertificate` IS, over ℝ, as a `Prop`. This module makes that checkable
against bytes a producer actually emitted (WIRE-1,
`futon2:src/futon2/aif/cascade_model_manifest.clj` `horizon-g-sparse-cert`):

1. a **rational mirror** of each certificate shape (`GCertificateQ`,
   `SelectionCertificateQ`) — emitted values are decimal literals, and a
   decimal literal is an exact rational, so the recorded run elaborates
   with no rounding step;
2. an **executable check** (`GCertificateQ.check : ℚ → GCertificateQ →
   Bool`) mirroring each clause of the frozen `valid`;
3. a **soundness theorem** (`check_sound`): `check ε c = true` implies the
   frozen `GCertificate.valid ε` holds of the cast certificate. This is
   the type check Joe commissioned — a generated witness file is a data
   literal plus one `decide`, and its acceptance is a theorem about the
   frozen specification, not about this module's opinion of it.

Soundness only, deliberately: a certificate the checker rejects is not
thereby proven invalid — the witness lane certifies runs, it does not
acquit them. A run whose emission recorded `:infinite` risk has no finite
mirror and is refused upstream by the witness generator; its Lean home is
`horizonEFE_eq_top_iff`, not finite arithmetic.

This module is NOT part of the frozen core (`scripts/aif-core-pins.txt`):
it consumes the frozen spec and may grow per certificate shape.
-/

namespace DarkTower.AIF

/-- Rational mirror of `GStep`: one recorded horizon step. -/
structure GStepQ where
  risk : ℚ
  riskStatus : QuantityStatus
  ambiguity : ℚ
  ambiguityStatus : QuantityStatus
  deriving DecidableEq, Repr

/-- Rational mirror of `GCertificate`: the emitted per-candidate record,
field for field. -/
structure GCertificateQ where
  horizon : ℕ
  steps : List GStepQ
  total : ℚ
  cForm : CForm
  ratesAllZero : Bool
  universeSize : ℕ
  deriving DecidableEq, Repr

/-- Cast a recorded step into the specification shape. Statuses carry over
unchanged; values cast ℚ → ℝ. -/
def GStepQ.toGStep (s : GStepQ) : GStep :=
  { risk := (s.risk : ℝ), riskStatus := s.riskStatus,
    ambiguity := (s.ambiguity : ℝ), ambiguityStatus := s.ambiguityStatus }

/-- Cast a recorded certificate into the specification shape. -/
def GCertificateQ.toGCertificate (c : GCertificateQ) : GCertificate :=
  { horizon := c.horizon
    steps := c.steps.map GStepQ.toGStep
    total := (c.total : ℝ)
    cForm := c.cForm
    ratesAllZero := c.ratesAllZero
    universeSize := c.universeSize }

/-- Executable form of the honesty clause: a step claiming a named
zero-reduction must record ambiguity exactly 0. -/
def GStepQ.ambiguityHonest (s : GStepQ) : Bool :=
  match s.ambiguityStatus with
  | .reducedIdenticallyZero _ => decide (s.ambiguity = 0)
  | _ => true

/-- Does this step claim a named zero-reduction for ambiguity? -/
def GStepQ.claimsZeroReduction (s : GStepQ) : Bool :=
  match s.ambiguityStatus with
  | .reducedIdenticallyZero _ => true
  | _ => false

/-- The sum the emitted total is checked against. -/
def GCertificateQ.stepSum (c : GCertificateQ) : ℚ :=
  (c.steps.map fun s => s.risk + s.ambiguity).sum

/-- The executable check, clause for clause with `GCertificate.valid`:
shape, positivity of the horizon, arithmetic within tolerance `ε`,
zero-reduction honesty, and the rates precondition behind any claimed
zero-reduction. The tolerance clause is the two-sided bound rather than
`|·|`; soundness recovers the absolute value via `abs_sub_le_iff`.

Witness files discharge `check ε c = true` by `native_decide`: this
toolchain's kernel does not reduce ℚ arithmetic at all (`Rat.add` gets
stuck under `decide` even on `1/3 + 1/6 = 1/2` — probed 2026-09-18), so
compiled evaluation is the honest route, with the compiler thereby in the
trusted base for the Bool step only; what is *claimed* is still the frozen
`GCertificate.valid`, via `check_sound`. -/
def GCertificateQ.check (ε : ℚ) (c : GCertificateQ) : Bool :=
  decide (c.steps.length = c.horizon) &&
  decide (0 < c.horizon) &&
  decide (c.total - c.stepSum ≤ ε) &&
  decide (c.stepSum - c.total ≤ ε) &&
  c.steps.all GStepQ.ambiguityHonest &&
  (!(c.steps.any GStepQ.claimsZeroReduction) || c.ratesAllZero)

/-- Executable form of `GCertificate.riskComputedThroughout` — Joe's
detectability example: every recorded step's risk status is `computed`. -/
def GCertificateQ.checkRiskComputed (c : GCertificateQ) : Bool :=
  c.steps.all fun s => decide (s.riskStatus = .computed)

private theorem cast_sum_risk_amb (l : List GStepQ) :
    (((l.map fun s => s.risk + s.ambiguity).sum : ℚ) : ℝ)
      = ((l.map GStepQ.toGStep).map fun s => s.risk + s.ambiguity).sum := by
  induction l with
  | nil => simp
  | cons s t ih =>
      simp only [List.map_cons, List.sum_cons, Rat.cast_add, ih, GStepQ.toGStep]

/-- **Soundness**: a certificate the executable check accepts satisfies the
frozen real-valued specification at the cast tolerance. -/
theorem GCertificateQ.check_sound {ε : ℚ} {c : GCertificateQ}
    (h : c.check ε = true) : c.toGCertificate.valid (ε : ℝ) := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hlen, hpos⟩, hup⟩, hdown⟩, hhon⟩, hrates⟩ := h
  refine ⟨?_, of_decide_eq_true hpos, ?_, ?_, ?_⟩
  · simpa [toGCertificate] using of_decide_eq_true hlen
  · have hq : |c.total - c.stepSum| ≤ ε :=
      abs_sub_le_iff.mpr ⟨of_decide_eq_true hup, of_decide_eq_true hdown⟩
    have hr := (Rat.cast_le (K := ℝ)).mpr hq
    rw [Rat.cast_abs, Rat.cast_sub] at hr
    rw [GCertificateQ.stepSum, cast_sum_risk_amb] at hr
    exact hr
  · intro s hs r hstat
    rcases List.mem_map.mp (by simpa [toGCertificate] using hs) with ⟨s', hs', rfl⟩
    have hst : s'.ambiguityStatus = .reducedIdenticallyZero r := hstat
    have h0 := List.all_eq_true.mp hhon s' hs'
    rw [GStepQ.ambiguityHonest, hst] at h0
    have : s'.ambiguity = 0 := of_decide_eq_true h0
    simp [GStepQ.toGStep, this]
  · rintro ⟨s, hs, r, hstat⟩
    rcases List.mem_map.mp (by simpa [toGCertificate] using hs) with ⟨s', hs', rfl⟩
    have hst : s'.ambiguityStatus = .reducedIdenticallyZero r := hstat
    have hclaims : c.steps.any GStepQ.claimsZeroReduction = true :=
      List.any_eq_true.mpr ⟨s', hs', by simp [GStepQ.claimsZeroReduction, hst]⟩
    rw [hclaims] at hrates
    show c.ratesAllZero = true
    simpa using hrates

/-- **Soundness** of the detectability check: acceptance witnesses that
risk was computed at every recorded step, in the frozen predicate. -/
theorem GCertificateQ.checkRiskComputed_sound {c : GCertificateQ}
    (h : c.checkRiskComputed = true) :
    c.toGCertificate.riskComputedThroughout := by
  intro s hs
  rcases List.mem_map.mp (by simpa [toGCertificate] using hs) with ⟨s', hs', rfl⟩
  exact of_decide_eq_true (List.all_eq_true.mp h s' hs')

/-- Rational mirror of `SelectionCertificate`: the selection seam's inputs
(β, E, F), for the record shape WIRE-f-on-tick is to emit. -/
structure SelectionCertificateQ where
  betaDeclared : ℚ
  habit : ℚ
  habitStatus : QuantityStatus
  f : ℚ
  fStatus : QuantityStatus
  deriving DecidableEq, Repr

/-- Cast into the specification shape. -/
def SelectionCertificateQ.toSelectionCertificate (c : SelectionCertificateQ) :
    SelectionCertificate :=
  { betaDeclared := (c.betaDeclared : ℝ)
    habit := (c.habit : ℝ), habitStatus := c.habitStatus
    f := (c.f : ℝ), fStatus := c.fStatus }

/-- Executable check, clause for clause with `SelectionCertificate.valid`. -/
def SelectionCertificateQ.check (c : SelectionCertificateQ) : Bool :=
  decide (0 < c.betaDeclared) &&
  (match c.habitStatus with
   | .declaredNeutral => decide (c.habit = 1)
   | _ => true) &&
  (match c.fStatus with
   | .declaredNeutral => decide (c.f = 0)
   | _ => true)

/-- **Soundness** for the selection certificate. -/
theorem SelectionCertificateQ.check_sound {c : SelectionCertificateQ}
    (h : c.check = true) : c.toSelectionCertificate.valid := by
  simp only [check, Bool.and_eq_true] at h
  obtain ⟨⟨hbeta, hhabit⟩, hf⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · have hb : (0 : ℚ) < c.betaDeclared := of_decide_eq_true hbeta
    show (0 : ℝ) < (c.betaDeclared : ℝ)
    exact_mod_cast hb
  · intro hn
    have hn' : c.habitStatus = .declaredNeutral := hn
    rw [hn'] at hhabit
    have : c.habit = 1 := of_decide_eq_true hhabit
    simp [toSelectionCertificate, this]
  · intro hn
    have hn' : c.fStatus = .declaredNeutral := hn
    rw [hn'] at hf
    have : c.f = 0 := of_decide_eq_true hf
    simp [toSelectionCertificate, this]

end DarkTower.AIF
