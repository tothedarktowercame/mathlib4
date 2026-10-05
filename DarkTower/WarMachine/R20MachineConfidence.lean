import DarkTower.WarMachine.R20InteroceptiveTripwire
import DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal

/-!
# R20 machine confidence

## The role

`p4ng/sec-catalog.tex`, "Interoceptive Tripwires (R20)", says that "a genuine
trip should lower the system's confidence in its own machinery until the
finding is discharged".  This module states that clause from retained trip
dispositions through a confidence factor.

The factor law is **ruled** by codex-26 under Joe's delegation in
`futon2/holes/labs/wm-contract/LEAD-DECISIONS-2026-09-12.md`, section 1:
`m(0)=1`, `m(k)=1/2` for positive `k`, where `k` counts distinct durable open
genuine trip identities.  That source calls it "a declared engineering
response, not an estimated/calibrated law".

Its placement into policy precision is **not adopted**.  The same ruling says
"No new beta equation is adopted merely by commissioning that investigation",
and `SPEC-row18-interoceptive-policy-precision-proposal-v1.md` says "proposal
only".  Consequently every result below which uses `adjustedPriorRate` is
labelled as conditional on the row-18 proposal's placement.  These theorems do
not adopt that placement and do not claim that posterior gamma falls;
`priorMeanReductionDoesNotImplyPosteriorGammaReduction` proves why.  Posterior
ordering additionally needs the hypotheses discharged by
`InteroceptivePolicyPrecisionUniqueRoot` and
`InteroceptivePolicyPrecisionVariance`.

## Runtime boundary

The carrier transcribes `futon2/src/futon2/aif/interoceptive_commitment.clj`
at Futon2 commit `0f9587532031beb50a21091cc41cd10f4a16ff63`.
`confidence-snapshot` computes `:machine-confidence` from production trip
actions and joined repair status.  A source search
`rg -n ':machine-confidence|machine-confidence' futon2/src futon2/scripts`
found only that producer and a report/adjudication script: no production
consumer composes the factor into policy precision, agreeing with
`TN-paper05-09-11-r20-closure-path-2026-09-15.md`.

This module does not state the paper's wire-demotion clause: no runtime record
says that a trip was blessed as a model revision.  Nor does it identify this
quantity with R7 precision: J1 retired the R7-to-R14 conflation, and the
conditional mathematics here acts on R14's policy precision.
-/

namespace DarkTower.WarMachine.R20MachineConfidence

open DarkTower.WarMachine.InteroceptivePolicyPrecisionProposal

/-- Runtime `:trip/action`. -/
inductive TripAction where
  | record | stopLine | parkAndSummon | discharge
  deriving DecidableEq, Repr

/-- Joined runtime `:repair/status`, or no joined repair status. -/
inductive RepairStatus where
  | open | awaitingValidation | resolved | superseded
  deriving DecidableEq, Repr

/-- One retained trip/disposition row. `tripId` stands for `:trip/id`; `action`
for `:trip/action`; `productionAuthority` for the joined authority class being
`:production`; and `repairStatus` for the joined `:repair/status`, if any. -/
structure TripDisposition where
  tripId : Nat
  action : TripAction
  productionAuthority : Bool
  repairStatus : Option RepairStatus
  deriving DecidableEq, Repr

/-- Runtime genuine actions are stop-line, park-and-summon, and discharge;
`:record` and non-production authority are excluded. -/
def Genuine (trip : TripDisposition) : Prop :=
  trip.productionAuthority = true ∧ trip.action ≠ .record

/-- Runtime terminal repair statuses are resolved and superseded. -/
def Discharged (trip : TripDisposition) : Prop :=
  trip.repairStatus = some .resolved ∨ trip.repairStatus = some .superseded

/-- A genuine trip remains open exactly while it lacks a terminal disposition. -/
def OpenGenuine (trip : TripDisposition) : Prop := Genuine trip ∧ ¬ Discharged trip

instance (trip : TripDisposition) : Decidable (Genuine trip) := by
  unfold Genuine
  infer_instance
instance (trip : TripDisposition) : Decidable (Discharged trip) := by
  unfold Discharged
  infer_instance
instance (trip : TripDisposition) : Decidable (OpenGenuine trip) := by
  unfold OpenGenuine
  infer_instance

/-- Every genuine trip has a joined repair status. The runtime snapshot
refuses (`:interoceptive/missing-finding-join`, `:interoceptive/missing-repair-join`)
when this fails, following the ruling's "Unknown/unreadable trip authority is
unavailable, never k=0". This module has no "unavailable" outcome: a genuine
trip with no joined status is not `Discharged`, so it is counted as open
(`unjoined_genuine_counts_as_open`), which also never reads as zero.
`SnapshotConforms` is the runtime's criterion only for a `JoinComplete` list;
for an incomplete one the runtime reports no factor at all. -/
def JoinComplete (trips : List TripDisposition) : Prop :=
  ∀ trip ∈ trips, Genuine trip → trip.repairStatus ≠ none

/-- Distinct open genuine identities. Duplicate observations of one `:trip/id`
contribute only once. -/
def openGenuineIds (trips : List TripDisposition) : Finset Nat :=
  ((trips.filter fun trip => decide (OpenGenuine trip)).map (·.tripId)).toFinset

def openGenuineCount (trips : List TripDisposition) : Nat :=
  (openGenuineIds trips).card

/-- A family of admissible confidence laws. The ruled fixed-half law is one
instance; a later evidence-derived positive law can use the same interface. -/
structure ConfidenceLaw where
  m : Nat → ℚ
  zero : m 0 = 1
  positive : ∀ k, 0 < k → 0 < m k ∧ m k < 1

/-- The ruled row-18 engineering factor. -/
def fixedHalf : ConfidenceLaw where
  m k := if k = 0 then 1 else 1 / 2
  zero := by simp
  positive := by intro k hk; norm_num [Nat.ne_of_gt hk]

def confidenceFactor (law : ConfidenceLaw) (trips : List TripDisposition) : ℚ :=
  law.m (openGenuineCount trips)

/-- Duplicate observations of one open genuine trip count once. -/
theorem duplicate_identity_counts_once (trip : TripDisposition) (h : OpenGenuine trip) :
    openGenuineCount [trip, trip] = 1 := by
  simp [openGenuineCount, openGenuineIds, h]

/-- A genuine trip whose repair join is missing counts as open: absence of the
disposition is never read as discharge. -/
theorem unjoined_genuine_counts_as_open (trip : TripDisposition)
    (genuine : Genuine trip) (unjoined : trip.repairStatus = none)
    (rest : List TripDisposition) :
    0 < openGenuineCount (trip :: rest) := by
  have isOpen : OpenGenuine trip := ⟨genuine, by simp [Discharged, unjoined]⟩
  have member : trip.tripId ∈ openGenuineIds (trip :: rest) := by
    simp [openGenuineIds, isOpen]
  exact Finset.card_pos.mpr ⟨_, member⟩

theorem no_open_genuine_factor (law : ConfidenceLaw) (trips : List TripDisposition)
    (h : openGenuineCount trips = 0) : confidenceFactor law trips = 1 := by
  simp [confidenceFactor, h, law.zero]

/-- Under the row-18 proposal's placement, no open genuine trip leaves the
policy-precision prior rate unchanged. -/
theorem no_open_genuine_unadjusted_rate (law : ConfidenceLaw)
    (trips : List TripDisposition) (betaPrior : ℝ)
    (h : openGenuineCount trips = 0) :
    adjustedPriorRate betaPrior (confidenceFactor law trips : ℝ) = betaPrior := by
  rw [no_open_genuine_factor law trips h]
  simpa using noInteroceptionReduction betaPrior

theorem positive_open_factor_lt_one (law : ConfidenceLaw) (trips : List TripDisposition)
    (h : 0 < openGenuineCount trips) : confidenceFactor law trips < 1 :=
  (law.positive _ h).2

/-- Under the row-18 proposal's placement, an open genuine trip strictly lowers
the Gamma prior's mean precision. This is not a posterior-gamma claim. -/
theorem positive_open_lowers_prior_mean (law : ConfidenceLaw)
    (trips : List TripDisposition) {betaPrior : ℝ} (hbeta : 0 < betaPrior)
    (hopen : 0 < openGenuineCount trips) :
    1 / adjustedPriorRate betaPrior (confidenceFactor law trips : ℝ) <
      1 / betaPrior := by
  have hmQ := law.positive _ hopen
  have hmpos : (0 : ℝ) < (confidenceFactor law trips : ℝ) := by exact_mod_cast hmQ.1
  have hmlt : (confidenceFactor law trips : ℝ) < 1 := by exact_mod_cast hmQ.2
  rw [adjustedPriorMean (ne_of_gt hbeta) (ne_of_gt hmpos)]
  have hinv : 0 < (1 / betaPrior) := one_div_pos.mpr hbeta
  nlinarith

theorem fixedHalf_positive_factor (trips : List TripDisposition)
    (hopen : 0 < openGenuineCount trips) :
    confidenceFactor fixedHalf trips = 1 / 2 := by
  simp [confidenceFactor, fixedHalf, Nat.ne_of_gt hopen]

/-- Under the row-18 proposal's placement, the ruled positive-open factor makes
the prior mean exactly half its unadjusted value. -/
theorem fixedHalf_positive_prior_mean (trips : List TripDisposition)
    {betaPrior : ℝ} (hbeta : 0 < betaPrior)
    (hopen : 0 < openGenuineCount trips) :
    1 / adjustedPriorRate betaPrior (confidenceFactor fixedHalf trips : ℝ) =
      (1 / 2 : ℝ) * (1 / betaPrior) := by
  have hm : confidenceFactor fixedHalf trips = 1 / 2 :=
    fixedHalf_positive_factor trips hopen
  rw [hm]
  simpa using (adjustedPriorMean (betaPrior := betaPrior) (m := (1 / 2 : ℝ))
    (ne_of_gt hbeta) (by norm_num))

theorem all_genuine_discharged_restores (law : ConfidenceLaw)
    (trips : List TripDisposition)
    (h : ∀ trip ∈ trips, Genuine trip → Discharged trip) :
    confidenceFactor law trips = 1 := by
  apply no_open_genuine_factor law trips
  have hempty : trips.filter (fun trip => decide (OpenGenuine trip)) = [] := by
    induction trips with
    | nil => simp
    | cons trip rest ih =>
        have hnot : ¬ OpenGenuine trip := by
          intro hopen
          exact hopen.2 (h trip (by simp) hopen.1)
        simp only [List.filter_cons, decide_eq_false hnot, Bool.false_eq_true, ↓reduceIte]
        apply ih
        intro item hmem
        exact h item (by simp [hmem])
  simp [openGenuineCount, openGenuineIds, hempty]

def openTrip (id : Nat) : TripDisposition :=
  ⟨id, .stopLine, true, some .open⟩

def dischargedTrip (id : Nat) : TripDisposition :=
  ⟨id, .stopLine, true, some .resolved⟩

def recordTrip (id : Nat) (status : Option RepairStatus) : TripDisposition :=
  ⟨id, .record, true, status⟩

def nonproductionTrip (id : Nat) (action : TripAction)
    (status : Option RepairStatus) : TripDisposition :=
  ⟨id, action, false, status⟩

def resolvedTrip (id : Nat) (action : TripAction) : TripDisposition :=
  ⟨id, action, true, some .resolved⟩

theorem discharge_one_of_two_stays_below_one (law : ConfidenceLaw) (a b : Nat) :
    confidenceFactor law [dischargedTrip a, openTrip b] < 1 := by
  apply positive_open_factor_lt_one
  simp [openGenuineCount, openGenuineIds, dischargedTrip, openTrip, Genuine,
    Discharged, OpenGenuine]

theorem adding_record_does_not_lower (law : ConfidenceLaw) (trips : List TripDisposition)
    (id : Nat) (status : Option RepairStatus) :
    confidenceFactor law (recordTrip id status :: trips) =
      confidenceFactor law trips := by
  simp [confidenceFactor, openGenuineCount, openGenuineIds, recordTrip,
    OpenGenuine, Genuine]

theorem adding_nonproduction_does_not_lower (law : ConfidenceLaw)
    (trips : List TripDisposition) (id : Nat) (action : TripAction)
    (status : Option RepairStatus) :
    confidenceFactor law (nonproductionTrip id action status :: trips) =
      confidenceFactor law trips := by
  simp [confidenceFactor, openGenuineCount, openGenuineIds, nonproductionTrip,
    OpenGenuine, Genuine]

theorem adding_discharged_does_not_lower (law : ConfidenceLaw)
    (trips : List TripDisposition) (id : Nat) (action : TripAction)
    (haction : action ≠ .record) :
    confidenceFactor law (resolvedTrip id action :: trips) =
      confidenceFactor law trips := by
  simp [confidenceFactor, openGenuineCount, openGenuineIds, resolvedTrip,
    OpenGenuine, Genuine, Discharged, haction]

/-- The retained snapshot conforms when its reported factor is exactly the
declared law at the distinct open-genuine identity count. -/
def SnapshotConforms (law : ConfidenceLaw) (trips : List TripDisposition)
    (factor : ℚ) : Prop := factor = confidenceFactor law trips

theorem open_trip_reporting_one_fails :
    ¬ SnapshotConforms fixedHalf [openTrip 7] 1 := by
  norm_num [SnapshotConforms, confidenceFactor, fixedHalf, openGenuineCount,
    openGenuineIds, openTrip, OpenGenuine, Genuine, Discharged] <;> decide

theorem record_only_reporting_half_fails :
    ¬ SnapshotConforms fixedHalf
      [{ tripId := 7, action := .record, productionAuthority := true,
         repairStatus := none }] (1 / 2) := by
  norm_num [SnapshotConforms, confidenceFactor, fixedHalf, openGenuineCount,
    openGenuineIds, OpenGenuine, Genuine]

theorem fixedHalf_open_trip_conforms :
    SnapshotConforms fixedHalf [openTrip 7] (1 / 2) := by
  norm_num [SnapshotConforms, confidenceFactor, fixedHalf, openGenuineCount,
    openGenuineIds, openTrip, OpenGenuine, Genuine, Discharged] <;> decide

end DarkTower.WarMachine.R20MachineConfidence
