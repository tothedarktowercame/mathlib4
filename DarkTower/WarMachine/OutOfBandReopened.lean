import DarkTower.WarMachine.OutOfBandFix

/-!
# A reopened injury consults out-of-band evidence too (L5-25b)

Source: click `wm-click-21ae0429…` (claude-2, 2026-11-01 23:22Z).  Lean
first; `meta_self_heal_production/open-out-of-band-route!` and
`out_of_band_fix/checked-medic-operation` conform in the same packet.
Additions only, beside `OutOfBandFix`.

**What happened.**  Injury `d984347f…` had one self-heal author attempt
(entry 153, `:claimed`) fail on the provider, which appended entry 154,
`:reopened` at attempt 2, awaiting a fresh attempt; the one-attempt cap
then refused every fresh attempt.  The owner's fix (futon2 `21c40aff1`)
and its acceptance artifact were retained beside the injury, and the next
click did not consult them: `open-out-of-band-route!` served only an entry
whose state is `:open` (`(= :open (:state entry))`), so the retained
artifact was never read and the click went to diagnosis, which the provider
refused again.  Two further mismatches were waiting behind the guard: the
medic payload hard-coded `:predecessor-entry-id nil`, while the latest
occurrence of a reopened injury has the claimed entry as its predecessor
(`transition->medic-entry`: `(:entry-id previous)` ↦ `"153"`), and the
route read the cause pin off the raw latest entry, which only the opening
entry carries.

**The model.**  `OutOfBandFix.routeOpen` decides what a presented artifact
does; this module decides WHICH active occurrence presents it.  An
occurrence awaiting a fresh attempt (`open`, or `reopened` after a failed
one) consults the evidence; an occurrence inside a live attempt (`claimed`,
`enacted`, `authored`, `reviewed`) does not, so an attempt in flight is not
interrupted.  `Occurrence` carries what the medic payload must bind: the
latest ordinal, its predecessor (`none` for an opening, `some` for a
reopening) and the cause pin, which is the opening's whatever the latest
entry carries.  `boundPayload` reads them off the occurrence;
`hardcodedPayload` is the deployed builder.
-/

namespace DarkTower.WarMachine.OutOfBandReopened

open DarkTower.WarMachine.OutOfBandFix (OpenArtifact OpenRoute routeOpen OutOfBandFixReceipt discharges)

/-- The active states of `meta_injury_ledger/active-states`. -/
inductive ActiveState where
  | open | claimed | authored | reviewed | enacted | reopened
  deriving DecidableEq, Repr

/-- Which active occurrence presents retained out-of-band evidence: one that
awaits a fresh attempt. -/
def consultsOutOfBand : ActiveState → Bool
  | .open | .reopened => true
  | .claimed | .authored | .reviewed | .enacted => false

/-- The deployed guard: `:open` only. -/
def currentConsults : ActiveState → Bool
  | .open => true
  | _ => false

/-- The click's route for an active occurrence in state `s` with artifact `a`:
consult (`routeOpen`) or go to diagnosis. -/
def routeActive (consults : ActiveState → Bool) (s : ActiveState) (a : OpenArtifact) : OpenRoute :=
  if consults s then routeOpen a else .diagnosis

theorem reopened_current_goes_to_diagnosis (a : OpenArtifact) :
    routeActive currentConsults .reopened a = .diagnosis := rfl

theorem reopened_repaired_consults (a : OpenArtifact) :
    routeActive consultsOutOfBand .reopened a = routeOpen a := rfl

theorem open_unchanged (a : OpenArtifact) :
    routeActive consultsOutOfBand .open a = routeActive currentConsults .open a := rfl

/-- A live attempt is not interrupted under either guard. -/
theorem live_attempt_not_interrupted (a : OpenArtifact) :
    routeActive consultsOutOfBand .claimed a = .diagnosis ∧
    routeActive consultsOutOfBand .enacted a = .diagnosis ∧
    routeActive consultsOutOfBand .authored a = .diagnosis ∧
    routeActive consultsOutOfBand .reviewed a = .diagnosis := ⟨rfl, rfl, rfl, rfl⟩

/-- The repaired guard extends the deployed one. -/
theorem repaired_extends_current (s : ActiveState) (h : currentConsults s = true) :
    consultsOutOfBand s = true := by
  cases s <;> simp_all [currentConsults, consultsOutOfBand]

/-- A checked, discharging artifact on a reopened injury discharges under the
repaired guard and was refused to diagnosis under the deployed one. -/
theorem reopened_checked_discharges (r : OutOfBandFixReceipt) (h : discharges r = true) :
    routeActive consultsOutOfBand .reopened (.checked r) = .medicDischarge ∧
    routeActive currentConsults .reopened (.checked r) = .diagnosis := by
  constructor
  · simp [routeActive, consultsOutOfBand, routeOpen, h]
  · rfl

/-! ## The payload binding -/

abbrev Ordinal := Nat
abbrev PinId := Nat

/-- The latest occurrence of an injury as the medic state reads it
(`transition->medic-entry`): its ordinal, its same-injury predecessor, and
its cause pin (inherited from the opening). -/
structure Occurrence where
  ordinal : Ordinal
  predecessor : Option Ordinal
  cause : PinId
  deriving DecidableEq, Repr

/-- What the genuine-repair payload must bind for `local-binding?`. -/
structure Binding where
  entry : Ordinal
  predecessor : Option Ordinal
  cause : PinId
  deriving DecidableEq, Repr

/-- The deployed builder: the latest ordinal, `nil` predecessor, and the cause
pin read off the raw latest entry (`none` when that entry carries none). -/
def hardcodedPayload (o : Occurrence) (rawCause : Option PinId) : Option Binding :=
  rawCause.map fun c => ⟨o.ordinal, none, c⟩

/-- The repaired builder reads the occurrence. -/
def boundPayload (o : Occurrence) : Binding := ⟨o.ordinal, o.predecessor, o.cause⟩

/-- `local-binding?`: the payload names the current occurrence, its
predecessor and its cause. -/
def binds (o : Occurrence) (b : Binding) : Bool :=
  b.entry == o.ordinal && b.predecessor == o.predecessor && b.cause == o.cause

theorem bound_binds (o : Occurrence) : binds o (boundPayload o) = true := by
  simp [binds, boundPayload]

/-- Entry 152's cause pin ↦ 4300 (`43ce01bc…`); entry 154 is the reopening
after the claimed entry 153; the raw entry 154 carries no cause pin. -/
def entry154 : Occurrence := ⟨154, some 153, 4300⟩

/-- The deployed builder cannot bind entry 154: no cause on the raw entry;
and had it one, the `nil` predecessor would still mismatch. -/
theorem entry154_hardcoded_fails :
    hardcodedPayload entry154 none = none ∧
    (hardcodedPayload entry154 (some 4300)).map (binds entry154) = some false := by decide

theorem entry154_bound_binds : binds entry154 (boundPayload entry154) = true := by decide

/-- An opening (entry 143 ↦ `⟨143, none, 7700⟩`, the 7d5e374e discharge):
the two builders agree, so the deployed discharges are unchanged. -/
theorem opening_builders_agree (ord : Ordinal) (c : PinId) :
    hardcodedPayload ⟨ord, none, c⟩ (some c) = some (boundPayload ⟨ord, none, c⟩) := rfl

#print axioms reopened_checked_discharges
#print axioms repaired_extends_current
#print axioms entry154_hardcoded_fails
#print axioms entry154_bound_binds
#print axioms opening_builders_agree

end DarkTower.WarMachine.OutOfBandReopened
