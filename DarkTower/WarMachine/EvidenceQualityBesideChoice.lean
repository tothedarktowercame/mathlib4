import Mathlib.Data.Rat.Floor
import Mathlib.Tactic

/-!
# Evidence quality is recorded beside the canonical choice (U4)

Source: decision sheet 2026-10-26 item 3, option (a) (Joe); DEFECTS U4;
packet from claude-9, 2026-10-26.  Witness mode: this module states the law,
and futon2 at `1508815f2` conforms to it.

The outer canonical choice is a function of four sealed inputs: the sealed
policy menu, the canonical-G frontier, the click's draw, and the Q6
exclusions (`outer_canonical_selection/evaluate frontier menu draw
excluded-keys`).  The policy evidence (`outer_policy_evidence/join`) is a
separate value recorded beside the choice.  Its quality is `computed` when
every sealed menu policy is joined, or `partial` naming the policies dropped
(`[:policy :policy-evidence :status] :partial`, the dropped digests under
`[:frontier :term-absent :policies]`).  `select-live`
(`meta_live_outer_selector.clj:867`, `:924`) admits evidence of either quality
before the canonical check, and the canonical frontier is produced from the
sealed menu alone (`outer-canonical-g/produce sealed-menu`, line 851), so
completeness of the evidence cannot change the choice; it changes only what
is recorded beside it.

Three laws:

1. `choice_same_under_any_quality`: the same (menu, frontier, draw,
   exclusions) give the same choice beside `computed` and beside
   `partial ds`, for every `ds`.  `choose` takes no evidence argument; the
   record stores the evidence beside `choose inputs`.
2. `partial_names_every_dropped`, `computed_iff_nothing_dropped`,
   `join_partial_dropped_exact`: a `partial ds` record names every dropped
   digest, and a record is `computed` only when nothing was dropped (a
   partial join is never a silent `computed`).
3. `refusal_same_under_any_quality`, `refusal_reasons`,
   `partial_admitted`: the refusal set of the choice is the five reasons of
   `evaluate`, none of which names evidence quality, and the evidence gate
   admits `partial` (`#{:computed :partial}`).

Modelling notes.  Scores and the draw are rationals; the Clojure's doubles
are read as the decimals the receipt prints.  A frontier row scores a menu
entry when the row is `:scored`, its digest is the entry's digest, and its
action pin agrees (`evaluate`'s `score-entry`; the pin agreement is folded
into the digest equality here).  Tie-break within the minima is the
`⌊u · n⌋`-th tied row in sealed-menu order, as in `SelectionDraw`.  The join
models dropping by the declaration only (a menu digest absent from the
declaration's `:policies`), which is the pinned test's case; absence of
durable records is the same `:absent` row status in the Clojure and takes
the same `:partial` route.

Pinned beside this at futon2 HEAD by
`outer_policy_runtime_selection_test/partial-evidence-is-recorded-beside-the-canonical-choice`.
The control there: two menu policies tied on canonical G, the second's digest
dropped from the declaration, the click seed `7` sealed as the draw.  The
seed draws `u = 0.7306990420600421` (`java.util.Random(7).nextDouble`), so
`⌊2u⌋ = 1` and the second entry is chosen: the chosen policy is the one
whose evidence was dropped, which is exactly what option (a) permits.  The
test pins that the chosen digest is a menu digest, not which one.
-/

namespace DarkTower.WarMachine.EvidenceQualityBesideChoice

abbrev Digest := String

/-- A sealed menu row: `:policy-id`, the `:policy-key` Q6 excludes by, and the
`:cascade-digest` of its action. -/
structure MenuEntry where
  policyId : String
  policyKey : String
  digest : Digest
  deriving DecidableEq, Repr

/-- The sealed pre-choice menu, pinned by `:menu-pin`. -/
structure Menu where
  menuPin : String
  entries : List MenuEntry
  deriving DecidableEq, Repr

/-- A canonical-G frontier row: scored with a finite `G`, or a typed refusal
(never a numeric score). -/
inductive RowStatus where
  | scored (G : ℚ)
  | refused
  deriving DecidableEq, Repr

structure FrontierRow where
  policyId : String
  digest : Digest
  status : RowStatus
  deriving DecidableEq, Repr

/-- The canonical-G frontier as `evaluate` reads it. -/
structure Frontier where
  produced : Bool
  menuPin : String
  rows : List FrontierRow
  deriving DecidableEq, Repr

/-- The click's sealed draw (`:u`). -/
structure Draw where
  u : ℚ
  deriving DecidableEq, Repr

def Draw.Valid (d : Draw) : Prop := 0 ≤ d.u ∧ d.u < 1

instance (d : Draw) : Decidable d.Valid := by unfold Draw.Valid; infer_instance

/-- The four inputs of the canonical choice.  Evidence is not among them. -/
structure ChoiceInputs where
  menu : Menu
  frontier : Frontier
  draw : Option Draw
  /-- Policy keys excluded by Q6 (`:excluded-keys`). -/
  excluded : List String
  deriving DecidableEq, Repr

/-- The refusal reasons of `evaluate`, exactly.  None names evidence. -/
inductive Refusal where
  | canonicalFrontierUnavailable
  | canonicalFrontierMenuMismatch
  | noScoredCanonicalPolicy
  | repeatChoiceAfterRefusal
  | invalidCanonicalTieDraw
  deriving DecidableEq, Repr

inductive Choice where
  | selected (action : MenuEntry) (draw : Option Draw)
  | noChoice (reason : Refusal)
  deriving DecidableEq, Repr

/-- `score-entry`: the frontier's finite score for a menu entry, when the row
for its policy is scored and carries the entry's digest. -/
def scoreOf (f : Frontier) (e : MenuEntry) : Option ℚ :=
  match f.rows.find? (fun r => r.policyId == e.policyId) with
  | some r =>
    match r.status with
    | .scored g => if r.digest = e.digest then some g else none
    | .refused => none
  | none => none

def scored (f : Frontier) (es : List MenuEntry) : List (MenuEntry × ℚ) :=
  es.filterMap (fun e => (scoreOf f e).map (fun g => (e, g)))

/-- The rows at the minimum score, in sealed-menu order. -/
def minima : List (MenuEntry × ℚ) → List (MenuEntry × ℚ)
  | [] => []
  | x :: rest =>
    let m := (rest.map Prod.snd).foldl min x.2
    (x :: rest).filter (fun y => decide (y.2 = m))

/-- The canonical choice: least scored canonical G over the sealed menu
minus the Q6 exclusions, ties broken by the sealed draw. -/
def choose (i : ChoiceInputs) : Choice :=
  if ¬ i.frontier.produced then .noChoice .canonicalFrontierUnavailable
  else if i.frontier.menuPin ≠ i.menu.menuPin then .noChoice .canonicalFrontierMenuMismatch
  else
    let allScored := scored i.frontier i.menu.entries
    let admitted := i.menu.entries.filter (fun e => !(i.excluded.any (· == e.policyKey)))
    match minima (scored i.frontier admitted) with
    | [] =>
      .noChoice (if !i.excluded.isEmpty && !allScored.isEmpty then .repeatChoiceAfterRefusal
                 else .noScoredCanonicalPolicy)
    | [x] => .selected x.1 none
    | x :: y :: rest =>
      match i.draw with
      | none => .noChoice .invalidCanonicalTieDraw
      | some d =>
        if d.Valid then
          .selected ((x :: y :: rest).getD ⌊d.u * (rest.length + 2)⌋₊ x).1 (some d)
        else .noChoice .invalidCanonicalTieDraw

/-- The quality of the evidence record: every menu policy joined, or the
dropped digests named. -/
inductive EvidenceQuality where
  | computed
  | «partial» (dropped : List Digest)
  deriving DecidableEq, Repr

/-- `policy-evidence/join` on the declaration: the menu digests the
declaration's `:policies` lacks are the `:term-absent` rows; `:partial` when
there are any, `:computed` otherwise. -/
def missingDigests (menu : Menu) (declared : List Digest) : List Digest :=
  (menu.entries.map (·.digest)).filter (fun d => decide (d ∉ declared))

def joinQuality (menu : Menu) (declared : List Digest) : EvidenceQuality :=
  if missingDigests menu declared = [] then .computed
  else .«partial» (missingDigests menu declared)

/-- `select-live`'s evidence gate, `#{:computed :partial}`: a join that produced
a quality is admitted; a join that refused (`none`) stops the receipt before
any choice is recorded. -/
def admitted : Option EvidenceQuality → Bool
  | some _ => true
  | none => false

/-- What the receipt records: the choice's inputs, the evidence beside it,
and the choice. -/
structure SelectionRecord where
  inputs : ChoiceInputs
  evidence : EvidenceQuality
  choice : Choice
  deriving Repr

/-- The record is formed from the inputs and the evidence; the choice is
`choose inputs`, whatever the evidence. -/
def record (i : ChoiceInputs) (q : EvidenceQuality) : SelectionRecord :=
  ⟨i, q, choose i⟩

/-! ## Law 1: the choice does not read the evidence -/

theorem choice_same_under_any_quality (i : ChoiceInputs) (ds : List Digest) :
    (record i (.«partial» ds)).choice = (record i .computed).choice := rfl

theorem choice_same_under_all_qualities (i : ChoiceInputs) (q q' : EvidenceQuality) :
    (record i q).choice = (record i q').choice := rfl

theorem choice_is_function_of_inputs (i : ChoiceInputs) (q : EvidenceQuality) :
    (record i q).choice = choose (record i q).inputs := rfl

/-- Two records with the same inputs agree on the choice, whatever each
records as evidence. -/
theorem records_agree_on_choice (r s : SelectionRecord) (i : ChoiceInputs)
    (q q' : EvidenceQuality) (hr : r = record i q) (hs : s = record i q') :
    r.choice = s.choice := by subst hr; subst hs; rfl

/-! ## Law 2: a partial record names every dropped digest -/

theorem mem_missingDigests (menu : Menu) (declared : List Digest) (d : Digest) :
    d ∈ missingDigests menu declared ↔ d ∈ menu.entries.map (·.digest) ∧ d ∉ declared := by
  unfold missingDigests
  rw [List.mem_filter]
  simp

theorem partial_names_every_dropped (menu : Menu) (declared : List Digest) (d : Digest)
    (hd : d ∈ menu.entries.map (·.digest)) (hn : d ∉ declared) :
    ∃ ds, joinQuality menu declared = .«partial» ds ∧ d ∈ ds := by
  have hmem : d ∈ missingDigests menu declared := (mem_missingDigests _ _ _).mpr ⟨hd, hn⟩
  have hne : missingDigests menu declared ≠ [] := List.ne_nil_of_mem hmem
  refine ⟨missingDigests menu declared, ?_, hmem⟩
  unfold joinQuality
  rw [if_neg hne]

theorem computed_iff_nothing_dropped (menu : Menu) (declared : List Digest) :
    joinQuality menu declared = .computed ↔
      ∀ d ∈ menu.entries.map (·.digest), d ∈ declared := by
  constructor
  · intro h d hd
    by_contra hn
    have hmem : d ∈ missingDigests menu declared := (mem_missingDigests _ _ _).mpr ⟨hd, hn⟩
    have hne : missingDigests menu declared ≠ [] := List.ne_nil_of_mem hmem
    unfold joinQuality at h
    rw [if_neg hne] at h
    cases h
  · intro h
    have hnil : missingDigests menu declared = [] := by
      apply List.eq_nil_iff_forall_not_mem.mpr
      intro d hd
      have := (mem_missingDigests _ _ _).mp hd
      exact this.2 (h d this.1)
    unfold joinQuality
    rw [if_pos hnil]

/-- The dropped list is exactly the menu digests the declaration lacks, in
menu order: nothing extra, nothing missing. -/
theorem join_partial_dropped_exact (menu : Menu) (declared : List Digest) (ds : List Digest)
    (h : joinQuality menu declared = .«partial» ds) :
    ds = missingDigests menu declared := by
  unfold joinQuality at h
  by_cases hnil : missingDigests menu declared = []
  · rw [if_pos hnil] at h; cases h
  · rw [if_neg hnil] at h; cases h; rfl

/-- A partial record is never silently `computed`: the two qualities are
distinct constructors. -/
theorem partial_ne_computed (ds : List Digest) :
    (EvidenceQuality.«partial» ds) ≠ .computed := by simp

/-! ## Law 3: no refusal of the choice arises from `partial` -/

theorem refusal_same_under_any_quality (i : ChoiceInputs) (q q' : EvidenceQuality)
    (r : Refusal) :
    (record i q).choice = .noChoice r ↔ (record i q').choice = .noChoice r := Iff.rfl

/-- The refusal set, exhaustively: the five reasons of `evaluate`. -/
theorem refusal_reasons (r : Refusal) :
    r = .canonicalFrontierUnavailable ∨ r = .canonicalFrontierMenuMismatch ∨
    r = .noScoredCanonicalPolicy ∨ r = .repeatChoiceAfterRefusal ∨
    r = .invalidCanonicalTieDraw := by
  cases r <;> simp

/-- The evidence gate admits a partial join. -/
theorem partial_admitted (ds : List Digest) : admitted (some (.«partial» ds)) = true := rfl

theorem computed_admitted : admitted (some .computed) = true := rfl

/-- Only a join that produced no quality at all stops the receipt. -/
theorem not_admitted_iff_no_join (e : Option EvidenceQuality) :
    admitted e = false ↔ e = none := by
  cases e <;> simp [admitted]

/-! ## Controls from the pinned Clojure test -/

/-- The fixture's two policies tie on canonical G to 16 digits (the m150
value, as the receipt prints it). -/
def tiedG : ℚ := -39560226735640867 / 10 ^ 16

def p1 : MenuEntry := ⟨"P1", "k1", "d1"⟩
def p2 : MenuEntry := ⟨"P2", "k2", "d2"⟩

def controlMenu : Menu := ⟨"menu-pin", [p1, p2]⟩

def controlFrontier : Frontier :=
  ⟨true, "menu-pin", [⟨"P1", "d1", .scored tiedG⟩, ⟨"P2", "d2", .scored tiedG⟩]⟩

/-- `java.util.Random(7).nextDouble`, the draw the test's `seed` seals. -/
def seedDraw : Draw := ⟨7306990420600421 / 10 ^ 16⟩

def controlInputs : ChoiceInputs := ⟨controlMenu, controlFrontier, some seedDraw, []⟩

/-- The test's declaration: the second entry's digest dropped. -/
def controlDeclared : List Digest := ["d1"]

theorem control_quality_partial :
    joinQuality controlMenu controlDeclared = .«partial» ["d2"] := by decide

/-- The seeded draw breaks the tie toward the second entry, the one whose
evidence was dropped; the choice is the same beside either quality. -/
theorem control_choice : choose controlInputs = .selected p2 (some seedDraw) := by
  decide +kernel

theorem control_choice_beside_partial :
    (record controlInputs (.«partial» ["d2"])).choice = .selected p2 (some seedDraw) :=
  control_choice

theorem control_choice_beside_computed :
    (record controlInputs .computed).choice = .selected p2 (some seedDraw) :=
  control_choice

/-- The chosen digest is a menu digest, as the test pins. -/
theorem control_chosen_is_menu_entry :
    p2 ∈ controlMenu.entries := by decide

/-- The complete declaration is `computed`; the choice is unchanged. -/
theorem control_complete_computed :
    joinQuality controlMenu ["d1", "d2"] = .computed := by decide

/-- What decides between the tied entries is the draw, not the evidence: a
draw below one half picks the first entry under the same partial record. -/
def lowDraw : Draw := ⟨1 / 4⟩

theorem control_low_draw_picks_first :
    choose { controlInputs with draw := some lowDraw } = .selected p1 (some lowDraw) := by
  decide +kernel

/-- Dropping the first entry's evidence instead does not move the choice. -/
theorem control_other_drop_same_choice :
    (record controlInputs (joinQuality controlMenu ["d2"])).choice =
      (record controlInputs (.«partial» ["d2"])).choice := rfl

/-- The one refusal reachable from these inputs is the draw's absence, and it
is the same beside either quality. -/
theorem control_no_draw_refuses :
    choose { controlInputs with draw := none } = .noChoice .invalidCanonicalTieDraw := by
  decide +kernel

theorem control_no_draw_refuses_beside_partial :
    (record { controlInputs with draw := none } (EvidenceQuality.«partial» ["d2"])).choice =
      Choice.noChoice .invalidCanonicalTieDraw :=
  control_no_draw_refuses

/-- A Q6 exclusion of the chosen key moves the choice; the evidence does
not. -/
theorem control_excluded_picks_other :
    choose { controlInputs with excluded := ["k2"] } = .selected p1 none := by
  decide +kernel

end DarkTower.WarMachine.EvidenceQualityBesideChoice
