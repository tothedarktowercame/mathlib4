import DarkTower.WarMachine.R20Graph

/-!
# Clojure field-flow witnesses for the R20 graph

R20Graph declares eight producer→consumer edges. This module says what a
Clojure field-flow path must show to stand for one of them, and decides it.

A witness lists, per edge, a chain of hops. A hop is one field written by
one Clojure var and read by another, at a pinned futon2 commit. The witness
is generated from futon3c's field-flow checker
(`holes/labs/M-wm-wiring/r20-field-flow.edn`); this module does not trust
the generator. It checks, for every edge:

* exactly one hop chain is offered;
* the first writer is a site of the edge's source endpoint and the last
  reader a site of its target endpoint (`endpointSites`);
* the hops chain (each reader is the next writer);
* the first hop's field type is the edge's quantity (`quantityTag`) and later
  hops carry it (`carries`), so F and G cannot share a port;
* every hop was confirmed at its source site by the checker;
* all hops are pinned to the witness's commit.

Across edges the first hops are distinct: two Lean edges may not be
witnessed by one Clojure field.

The site table is the Lean↔Clojure identification. Its rows follow
S2-authority-ledger.md, "Settlement from the publications" (2026-10-21):
selection (policy evaluation) produces E and G; inference after the
observation under each frozen policy produces F, which in futon2 is
`retrospective-f`; precision's β update is `advance`. Edges whose Clojure
flow is not yet confirmed fail here; that failure is the intended reading.

Nothing here is about values or run identity. That is `Wired` in R20Graph,
and it needs run ids the Clojure fields do not carry yet.
-/

namespace DarkTower.WarMachine.R20Witness
open DarkTower.WarMachine.R20Graph

/-- A Clojure site, `"<repo-relative file>#<var>"`. -/
abbrev Site := String

def policyClj : String := "futon2/src/futon2/aif/policy.clj"
def carryClj : String := "futon2/src/futon2/aif/policy_precision_carry.clj"
def certClj : String := "futon2/src/futon2/aif/wm/apparatus_certificates.clj"
def shapeGClj : String := "futon2/src/futon2/aif/cascade_shape_g.clj"
def observationClj : String := "futon2/src/futon2/aif/observation_model.clj"
def focusClj : String := "futon2/src/futon2/aif/focus_receipt.clj"
def habitClj : String := "futon2/src/futon2/aif/enactment_habit.clj"

def site (file var : String) : Site := file ++ "#" ++ var

/-- The Lean↔Clojure identification of endpoints. Rows without a settled
Clojure site are empty, so any edge touching them cannot be witnessed.

Selection includes `evaluate`, the per-tick observation-model step that
forms the predicted class distribution and H3's risk against C (Friston
eq.2.6, friston2017.txt:600-620). Class preference has two sites: C is set
in the generative model by `class-emission-model` (prior preferences are a
model parameter), and `class-preference-row` audits C against predictions
after G is computed. The row writes only a verdict, so it cannot be the
source of C (S5a, 2026-10-21). For the same reason the strategic focus is
sourced where focus is produced, `discover`, and where it is retained at
decision time, `decision-focus`; `strategic-focus-row` only compares the
focus receipt with the scored class after the fact (S8a, 2026-10-21). At the
pin, `class-emission-model` assigns `:target-class {target :focused}` without
reading focus, so no chain exists and the edge fails. The habit row is the
per-policy enactment count, `fold`, and its normalisation, `masses`
(NOTE-r20-habit-counts-2026-10-22: counts keyed by structural policy
identity). The interoception row has no Clojure site: no code in futon2
treats machine-internal state as an observation modality (`R20Interoception`),
so `interoceptionToSelectionG` cannot be witnessed and every real witness
fails on it. -/
def endpointSites : Endpoint → List Site
  | .selection =>
    [site policyClj "selection-candidate", site policyClj "selection-certificate",
     site observationClj "evaluate"]
  | .postObservationInference => [site carryClj "retrospective-f"]
  | .row .precision => [site carryClj "advance"]
  | .row .classPreference =>
    [site shapeGClj "class-emission-model", site certClj "class-preference-row"]
  | .row .strategicFocus => [site focusClj "discover", site focusClj "decision-focus"]
  | .row .habit => [site habitClj "fold", site habitClj "masses"]
  | .row _ => []

/-- Field types, as `:r20/field-types` writes them without the colon. -/
def quantityTag : QuantityKind → String
  | .habitPrior => "quantity/policy-prior"
  | .preference => "quantity/preference"
  | .preferenceSchedule => "quantity/preference-schedule"
  | .predictedClassDistribution => "quantity/predicted-class-distribution"
  | .policyExpectedFreeEnergy => "quantity/expected-free-energy"
  | .policyFreeEnergy => "quantity/free-energy"
  | .interoceptiveRisk => "quantity/interoceptive-risk"

/-- Container types a quantity may pass through after its first hop. The
frozen family is `family`'s `(select-keys % [:id :g :habit])`. -/
def carrierTags : QuantityKind → List String
  | .habitPrior | .policyExpectedFreeEnergy => ["receipt/frozen-policy-family"]
  | _ => []

def carries (tag : String) (q : QuantityKind) : Bool :=
  tag == quantityTag q || (carrierTags q).contains tag

structure Hop where
  writer : Site
  field : String
  record : String
  fieldType : String
  reader : Site
  /-- Both the write and the read were found at their sites by the checker. -/
  confirmed : Bool
  sha : String
  deriving DecidableEq, Repr

structure EdgeWitness where
  edge : Edge
  hops : List Hop
  deriving Repr

structure Witness where
  sha : String
  edges : List EdgeWitness
  deriving Repr

def allEdges : List Edge :=
  [.habitToSelectionHabit, .selectionToPrecisionHabit, .selectionToPrecisionG, .inferenceToPrecisionF,
   .strategicFocusToClassPreference, .selectionToClassPreference, .classPreferenceToSelectionG,
   .interoceptionToSelectionG]

theorem mem_allEdges (e : Edge) : e ∈ allEdges := by
  cases e <;> simp [allEdges]

def chained : List Hop → Bool
  | a :: b :: rest => a.reader == b.writer && chained (b :: rest)
  | _ => true

def hopsOK (sha : String) (e : Edge) : List Hop → Bool
  | [] => false
  | h :: t =>
    let hops := h :: t
    (endpointSites e.source).contains h.writer &&
    (endpointSites e.target).contains (hops.getLast (List.cons_ne_nil h t)).reader &&
    h.fieldType == quantityTag e.quantity &&
    t.all (fun x => carries x.fieldType e.quantity) &&
    chained hops &&
    hops.all (·.confirmed) &&
    hops.all (·.sha == sha)

/-- The single chain offered for `e`, if exactly one is offered. -/
def chainFor (w : Witness) (e : Edge) : Option (List Hop) :=
  match w.edges.filter (·.edge == e) with
  | [ew] => some ew.hops
  | _ => none

def edgeOK (w : Witness) (e : Edge) : Bool :=
  match chainFor w e with
  | some hops => hopsOK w.sha e hops
  | none => false

def firstKey (ew : EdgeWitness) : Option (String × String × Site) :=
  ew.hops.head?.map fun h => (h.field, h.record, h.writer)

def distinctPorts (w : Witness) : Bool :=
  (w.edges.map firstKey).Nodup

def WitnessOK (w : Witness) : Bool :=
  allEdges.all (edgeOK w) && distinctPorts w

/-- Per-edge verdicts, for the receipt. -/
def verdicts (w : Witness) : List (Edge × Bool) :=
  allEdges.map fun e => (e, edgeOK w e)

theorem edgeOK_sound {w : Witness} {e : Edge} (h : edgeOK w e = true) :
    ∃ hd tl, chainFor w e = some (hd :: tl) ∧
      hd.writer ∈ endpointSites e.source ∧
      ((hd :: tl).getLast (List.cons_ne_nil hd tl)).reader ∈ endpointSites e.target ∧
      hd.fieldType = quantityTag e.quantity ∧
      (∀ x ∈ hd :: tl, x.confirmed = true ∧ x.sha = w.sha) := by
  unfold edgeOK at h
  split at h
  · rename_i hops hc
    cases hops with
    | nil => simp [hopsOK] at h
    | cons hd tl =>
      simp only [hopsOK, Bool.and_eq_true, List.contains_iff_mem, beq_iff_eq,
        List.all_eq_true] at h
      obtain ⟨⟨⟨⟨⟨⟨hs, ht⟩, hq⟩, -⟩, -⟩, hc'⟩, hsha⟩ := h
      exact ⟨hd, tl, hc, hs, ht, hq, fun x hx => ⟨hc' x hx, by simpa using hsha x hx⟩⟩
  · simp at h

/-- A checked witness covers every R20Graph edge. -/
theorem witnessOK_covers {w : Witness} (h : WitnessOK w = true) (e : Edge) :
    edgeOK w e = true := by
  simp only [WitnessOK, Bool.and_eq_true, List.all_eq_true] at h
  exact h.1 e (mem_allEdges e)

/-! ## Controls -/

def pin : String := "270bebc27965b31f1d33012e68b4d1f512eca3f9"

def hop (w f r ty rd : String) (ok : Bool := true) : Hop :=
  ⟨w, f, r, ty, rd, ok, pin⟩

def fHop : Hop :=
  hop (site carryClj "retrospective-f") ":f" ":precision-retrospective" "quantity/free-energy"
    (site carryClj "advance")

def gHop1 (familyConfirmed : Bool := true) : Hop :=
  hop (site policyClj "selection-candidate") ":g" ":selection-candidate"
    "quantity/expected-free-energy" (site carryClj "family") familyConfirmed

def gHop2 (familyConfirmed : Bool := true) : Hop :=
  hop (site carryClj "family") ":candidates" ":precision-family"
    "receipt/frozen-policy-family" (site carryClj "advance") familyConfirmed

def gHops (familyConfirmed : Bool) : List Hop := [gHop1 familyConfirmed, gHop2 familyConfirmed]

def eHops : List Hop :=
  [hop (site policyClj "selection-candidate") ":habit" ":selection-candidate"
      "quantity/policy-prior" (site carryClj "family"),
   hop (site carryClj "family") ":candidates" ":precision-family"
      "receipt/frozen-policy-family" (site carryClj "advance")]

/-- A complete synthetic witness; the class-side sites are invented for the
control and say nothing about futon2. -/
def synthetic : Witness :=
  { sha := pin
    edges :=
      [⟨.inferenceToPrecisionF, [fHop]⟩,
       ⟨.selectionToPrecisionG, gHops true⟩,
       ⟨.selectionToPrecisionHabit, eHops⟩,
       ⟨.habitToSelectionHabit,
        [hop (site habitClj "masses") ":habit-masses" ":enactment-habit"
          "quantity/policy-prior" (site policyClj "selection-candidate")]⟩,
       ⟨.strategicFocusToClassPreference,
        [hop (site focusClj "decision-focus") ":tactical-preference" ":focus"
          "quantity/preference" (site certClj "class-preference-row")]⟩,
       ⟨.selectionToClassPreference,
        [hop (site policyClj "selection-certificate") ":predicted" ":selection-certificate"
          "quantity/predicted-class-distribution" (site certClj "class-preference-row")]⟩,
       ⟨.classPreferenceToSelectionG,
        [hop (site certClj "class-preference-row") ":c-schedule" ":class-preference"
          "quantity/preference-schedule" (site policyClj "selection-candidate")]⟩] }

/-- W0: the checker says yes to every edge whose endpoints have Clojure
sites, so the synthetic witness passes all of them. -/
theorem w0_synthetic_ok :
    (allEdges.filter (· != .interoceptionToSelectionG)).all (edgeOK synthetic) = true ∧
      distinctPorts synthetic = true := by decide

/-- W0b: no witness passes while the interoception row has no Clojure site:
no hop can start at one of its sites. -/
theorem w0b_interoception_unwitnessable (w : Witness) :
    edgeOK w .interoceptionToSelectionG = false := by
  unfold edgeOK
  split
  · rename_i hops _
    cases hops with
    | nil => rfl
    | cons h t => simp [hopsOK, endpointSites, Edge.source]
  · rfl

theorem no_witnessOK_without_interoception_site (w : Witness) : WitnessOK w = false := by
  have := w0b_interoception_unwitnessable w
  simp [WitnessOK, allEdges, this]

def replaceEdge (w : Witness) (e : Edge) (hops : List Hop) : Witness :=
  { w with edges := w.edges.map fun ew => if ew.edge = e then ⟨e, hops⟩ else ew }

/-- W1: a missing edge names itself. -/
theorem w1_missing_edge :
    edgeOK { synthetic with edges := synthetic.edges.filter (·.edge != .selectionToPrecisionG) }
      .selectionToPrecisionG = false := by decide

/-- W2: wrong producer, right type — G written by the class-emission model. -/
theorem w2_wrong_producer :
    edgeOK (replaceEdge synthetic .selectionToPrecisionG
      [hop (site "futon2/src/futon2/aif/cascade_shape_g.clj" "class-emission-model") ":g"
        ":class-model" "quantity/expected-free-energy" (site carryClj "advance")])
      .selectionToPrecisionG = false := by decide

/-- W3: collapsed F/G — G witnessed by the F field fails on type and on
distinct ports. -/
theorem w3_collapsed_ports :
    edgeOK (replaceEdge synthetic .selectionToPrecisionG [fHop]) .selectionToPrecisionG = false ∧
    distinctPorts (replaceEdge synthetic .selectionToPrecisionG [fHop]) = false := by decide

/-- W4: a hop declared but not found at its site does not count. This is
today's state of `family` (S4d review). -/
theorem w4_unconfirmed_hop :
    edgeOK (replaceEdge synthetic .selectionToPrecisionG (gHops false))
      .selectionToPrecisionG = false := by decide

/-- W5: a broken chain fails. -/
theorem w5_broken_chain :
    edgeOK (replaceEdge synthetic .selectionToPrecisionG
      [gHop1, { gHop2 with writer := site policyClj "select" }])
      .selectionToPrecisionG = false := by decide

/-- W6: a hop pinned to another commit fails. -/
theorem w6_stale_hop :
    edgeOK (replaceEdge synthetic .inferenceToPrecisionF [{ fHop with sha := "0000" }])
      .inferenceToPrecisionF = false := by decide

/-- W7: two chains for one edge fail; the witness must choose. -/
theorem w7_ambiguous :
    edgeOK { synthetic with edges := ⟨.inferenceToPrecisionF, [fHop]⟩ :: synthetic.edges }
      .inferenceToPrecisionF = false := by decide

/-- W8: extra Clojure plumbing is allowed — a longer carrier chain passes. -/
theorem w8_extra_carrier_ok :
    edgeOK (replaceEdge synthetic .selectionToPrecisionG
      [gHop1,
       hop (site carryClj "family") ":candidates" ":precision-family"
         "receipt/frozen-policy-family" (site carryClj "seal"),
       hop (site carryClj "seal") ":candidates" ":precision-family"
         "receipt/frozen-policy-family" (site carryClj "advance")])
      .selectionToPrecisionG = true := by decide

/-- W9: a carrier cannot launder a quantity — the frozen family does not
carry F. -/
theorem w9_carrier_does_not_carry_F :
    edgeOK (replaceEdge synthetic .inferenceToPrecisionF
      [{ fHop with reader := site carryClj "family" },
       hop (site carryClj "family") ":candidates" ":precision-family"
         "receipt/frozen-policy-family" (site carryClj "advance")])
      .inferenceToPrecisionF = false := by decide

/-- W10: C written by the generative model and read by selection's risk
step witnesses the C edge in one hop. -/
theorem w10_model_c_to_selection_ok :
    edgeOK (replaceEdge synthetic .classPreferenceToSelectionG
      [hop (site shapeGClj "class-emission-model") ":class-preference" ":class-model"
        "quantity/preference-schedule" (site observationClj "evaluate")])
      .classPreferenceToSelectionG = true := by decide

/-- W11: C cannot reach selection laundered as G; the risk and score fields
do not carry the preference schedule. -/
theorem w11_c_not_carried_by_g :
    edgeOK (replaceEdge synthetic .classPreferenceToSelectionG
      [hop (site shapeGClj "class-emission-model") ":class-preference" ":class-model"
        "quantity/preference-schedule" (site certClj "class-preference-row"),
       hop (site certClj "class-preference-row") ":controller-score" ":ranked-candidate"
        "quantity/expected-free-energy" (site policyClj "selection-candidate")])
      .classPreferenceToSelectionG = false := by decide

/-- W12: focus retained at decision time and read by the generative model's
class assignment witnesses the strategic edge in one hop. This is the hop
futon2 does not have at the pin. -/
theorem w12_decision_focus_to_model_ok :
    edgeOK (replaceEdge synthetic .strategicFocusToClassPreference
      [hop (site focusClj "decision-focus") ":tactical-preference" ":focus"
        "quantity/preference" (site shapeGClj "class-emission-model")])
      .strategicFocusToClassPreference = true := by decide

/-- W13: the strategic-focus certificate row cannot source the edge; it reads
the focus receipt and writes only a verdict. -/
theorem w13_audit_row_is_not_focus :
    edgeOK (replaceEdge synthetic .strategicFocusToClassPreference
      [hop (site certClj "strategic-focus-row") ":tactical-preference" ":focus"
        "quantity/preference" (site shapeGClj "class-emission-model")])
      .strategicFocusToClassPreference = false := by decide

#print axioms edgeOK_sound
#print axioms witnessOK_covers
#print axioms w0_synthetic_ok
#print axioms w1_missing_edge
#print axioms w2_wrong_producer
#print axioms w3_collapsed_ports
#print axioms w4_unconfirmed_hop
#print axioms w5_broken_chain
#print axioms w6_stale_hop
#print axioms w7_ambiguous
#print axioms w8_extra_carrier_ok
#print axioms w9_carrier_does_not_carry_F
#print axioms w10_model_c_to_selection_ok
#print axioms w11_c_not_carried_by_g
#print axioms w12_decision_focus_to_model_ok
#print axioms w13_audit_row_is_not_focus

end DarkTower.WarMachine.R20Witness
