import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.List.Basic

/-! # A finite 3/2-blend carrier

Packet 1 of the carrier fixed by
`NOTE-three-halves-blend-carrier-2026-10-06.md`: ordered hom-sets,
composition, maximal identities, and consistency. The 3/2-pushout property
is deliberately left to packet 2. -/

namespace DarkTower.WarMachine.ThreeHalvesBlend

structure Theory where
  elems : Finset Nat
  axioms : Finset (Nat × Nat × Nat)
  deriving DecidableEq

def Theory.wellFormed (A : Theory) : Bool :=
  decide (∀ a ∈ A.axioms, a.1 ∈ A.elems ∧ a.2.1 ∈ A.elems ∧ a.2.2 ∈ A.elems)

structure PMap where
  rel : Finset (Nat × Nat)
  deriving DecidableEq

namespace PMap

@[ext] theorem ext {f g : PMap} (hrel : f.rel = g.rel) : f = g := by
  cases f
  cases g
  simp_all

/-- A functional partial map whose endpoints belong to its source and target
theories. Functionality is the computable statement
that projection to the first coordinate is injective on the finite relation. -/
def wellFormed (f : PMap) (A B : Theory) : Bool :=
  decide (f.rel ⊆ A.elems ×ˢ B.elems) &&
    decide ((f.rel.image Prod.fst).card = f.rel.card)

/-- Source axioms whose three names are all mapped and whose image is a target
axiom. Preservation is derived from the graph, never declared on the map. -/
def carries (f : PMap) (A B : Theory) : Finset (Nat × Nat × Nat) :=
  A.axioms.filter fun a =>
    decide (∃ images ∈ f.rel ×ˢ (f.rel ×ˢ f.rel),
      images.1.1 = a.1 ∧ images.2.1.1 = a.2.1 ∧ images.2.2.1 = a.2.2 ∧
        (images.1.2, images.2.1.2, images.2.2.2) ∈ B.axioms)

def le (f g : PMap) : Bool :=
  decide (f.rel ⊆ g.rel)

def comp (f g : PMap) : PMap :=
  { rel := (f.rel ×ˢ g.rel).filter (fun pair => pair.1.2 = pair.2.1) |>.image
      (fun pair => (pair.1.1, pair.2.2)) }

def id (A : Theory) : PMap :=
  { rel := A.elems.image (fun x => (x, x)) }

def join (f g : PMap) : PMap :=
  { rel := f.rel ∪ g.rel }

def empty : PMap := ⟨∅⟩

theorem wellFormed_parts {f : PMap} {A B : Theory} (hf : f.wellFormed A B = true) :
    (∀ p ∈ f.rel, p.1 ∈ A.elems ∧ p.2 ∈ B.elems) ∧
    (∀ p ∈ f.rel, ∀ q ∈ f.rel, p.1 = q.1 → p.2 = q.2) := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq] at hf
  have hinj : Set.InjOn Prod.fst (↑f.rel : Set (Nat × Nat)) :=
    Finset.card_image_iff.mp hf.2
  refine ⟨?_, ?_⟩
  · intro p hp
    exact Finset.mem_product.mp (hf.1 hp)
  · intro p hp q hq heq
    exact congrArg Prod.snd (hinj hp hq heq)

theorem le_refl (f : PMap) : f.le f = true := by
  simp [le]

theorem le_trans {f g h : PMap} (hfg : f.le g = true) (hgh : g.le h = true) :
    f.le h = true := by
  simp only [le, decide_eq_true_eq] at hfg hgh ⊢
  exact fun _ hx => hgh (hfg hx)

theorem comp_monotone {f f' g g' : PMap} (hf : f.le f' = true)
    (hg : g.le g' = true) : (comp f g).le (comp f' g') = true := by
  simp only [le, decide_eq_true_eq] at hf hg ⊢
  intro p hp
  simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp ⊢
  obtain ⟨q, ⟨⟨hqf, hqg⟩, hmatch⟩, rfl⟩ := hp
  exact ⟨q, ⟨⟨hf hqf, hg hqg⟩, hmatch⟩, rfl⟩

theorem comp_right_id {A B : Theory} {f : PMap} (hf : f.wellFormed A B = true) :
    comp f (id B) = f := by
  obtain ⟨hdom, _⟩ := wellFormed_parts hf
  apply PMap.ext
  · ext p
    constructor
    · intro hp
      simp only [comp, id, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨q, ⟨⟨hqf, ⟨x, hx, hqx⟩⟩, hmatch⟩, hpq⟩ := hp
      rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only [Prod.mk.injEq] at hqx
      rw [← hpq]
      have hbd : b = d := hmatch.trans (hqx.1.symm.trans hqx.2)
      simpa [hbd] using hqf
    · intro hp
      have hb := (hdom p hp).2
      exact Finset.mem_image.mpr ⟨(p, (p.2, p.2)),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨hp, Finset.mem_image.mpr ⟨p.2, hb, rfl⟩⟩, rfl⟩, rfl⟩

theorem comp_left_id {A B : Theory} {f : PMap} (hf : f.wellFormed A B = true) :
    comp (id A) f = f := by
  obtain ⟨hdom, _⟩ := wellFormed_parts hf
  apply PMap.ext
  · ext p
    constructor
    · intro hp
      simp only [comp, id, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp
      obtain ⟨q, ⟨⟨⟨x, hx, hqx⟩, hqf⟩, hmatch⟩, hpq⟩ := hp
      rcases q with ⟨⟨a, b⟩, ⟨c, d⟩⟩
      simp only [Prod.mk.injEq] at hqx
      rw [← hpq]
      have hac : a = c := (hqx.1.symm.trans hqx.2).trans hmatch
      simpa [hac] using hqf
    · intro hp
      have ha := (hdom p hp).1
      exact Finset.mem_image.mpr ⟨((p.1, p.1), p),
        Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
          ⟨Finset.mem_image.mpr ⟨p.1, ha, rfl⟩, hp⟩, rfl⟩, rfl⟩

theorem id_maximal (A : Theory) (f : PMap) (hf : f.wellFormed A A = true)
    (h : (PMap.id A).le f = true) : f = PMap.id A := by
  obtain ⟨hdom, hfun⟩ := wellFormed_parts hf
  simp only [le, decide_eq_true_eq] at h
  apply PMap.ext
  · ext p
    constructor
    · intro hp
      have hdiag : (p.1, p.1) ∈ f.rel := h
        (Finset.mem_image.mpr ⟨p.1, (hdom p hp).1, rfl⟩)
      have heq : p.2 = p.1 := hfun p hp (p.1, p.1) hdiag rfl
      exact Finset.mem_image.mpr ⟨p.1, (hdom p hp).1, by ext <;> simp [heq]⟩
    · intro hp
      exact h hp

theorem id_not_greatest :
    ∃ (A : Theory) (f : PMap), f.wellFormed A A = true ∧
      f.le (PMap.id A) = false := by
  refine ⟨⟨{0, 1}, ∅⟩, ⟨{(0, 1)}⟩, ?_⟩
  native_decide

/-- Graph inclusion also gives domain inclusion by `Finset.image_subset_image`.
It preserves derived axiom carriage as well. The well-formedness hypotheses
state the intended hom-set, although graph inclusion alone proves this fact. -/
theorem carries_monotone {A B : Theory} {f g : PMap}
    (_hf : f.wellFormed A B = true) (_hg : g.wellFormed A B = true)
    (hfg : f.le g = true) : f.carries A B ⊆ g.carries A B := by
  simp only [le, decide_eq_true_eq] at hfg
  intro a ha
  simp only [carries, Finset.mem_filter, decide_eq_true_eq] at ha ⊢
  refine ⟨ha.1, ?_⟩
  obtain ⟨images, himages, htest⟩ := ha.2
  exact ⟨images, Finset.mem_product.mpr
    ⟨hfg (Finset.mem_product.mp himages).1,
      Finset.mem_product.mpr
        ⟨hfg (Finset.mem_product.mp (Finset.mem_product.mp himages).2).1,
          hfg (Finset.mem_product.mp (Finset.mem_product.mp himages).2).2⟩⟩, htest⟩

end PMap

structure Span where
  G : Theory
  I₁ : Theory
  I₂ : Theory
  a₁ : PMap
  a₂ : PMap
  deriving DecidableEq

structure Cone (s : Span) where
  B : Theory
  b₁ : PMap
  b₂ : PMap
  aux₁ : Bool
  aux₂ : Bool
  deriving DecidableEq

/-- The join of the non-auxiliary composites is their least upper bound, so
its well-formedness is equivalent to existence of a well-formed upper bound.
An auxiliary triangle contributes the empty map to this join. -/
def Cone.consistent (s : Span) (c : Cone s) : Bool :=
  (PMap.join (if c.aux₁ then PMap.empty else PMap.comp s.a₁ c.b₁)
    (if c.aux₂ then PMap.empty else PMap.comp s.a₂ c.b₂)).wellFormed s.G c.B

theorem both_auxiliary_vacuous (s : Span) (B : Theory) (b₁ b₂ : PMap) :
    (Cone.mk B b₁ b₂ true true : Cone s).consistent = true := by
  simp [Cone.consistent, PMap.empty, PMap.join, PMap.wellFormed]

/-! ## House, boat, houseboat, and boathouse

Element codes:

* generic: 0 person, 1 object, 2 medium, 3 use, 4 on;
* house: 10 resident, 11 house, 12 land, 13 livein, 4 on;
* boat: 20 passenger, 21 boat, 22 water, 23 ride, 4 on;
* houseboat: 30 resident/passenger, 31 house/boat, 22 water,
  33 live in/ride, 4 on;
* boathouse: 20 passenger, 32 resident/boat, 11 house, 12 land, 22 water,
  23 ride, 13 livein, 4 on.

Axioms below are triples `(relation, subject, object)`. Thus Houseboat's are
`live in/ride(resident/passenger,house/boat)` and `on(house/boat,water)`;
Boathouse retains all four concrete statements from Figure 5.
-/

def genericTheory : Theory := ⟨{0, 1, 2, 3, 4}, {(3, 0, 1), (4, 1, 2)}⟩
def houseTheory : Theory := ⟨{10, 11, 12, 13, 4}, {(13, 10, 11), (4, 11, 12)}⟩
def boatTheory : Theory := ⟨{20, 21, 22, 23, 4}, {(23, 20, 21), (4, 21, 22)}⟩
def houseboatTheory : Theory := ⟨{30, 31, 22, 33, 4}, {(33, 30, 31), (4, 31, 22)}⟩
def boathouseTheory : Theory :=
  ⟨{20, 32, 11, 12, 22, 23, 13, 4},
    {(23, 20, 32), (13, 32, 11), (4, 11, 12), (4, 32, 22)}⟩

def genericToHouse : PMap :=
  ⟨{(0, 10), (1, 11), (2, 12), (3, 13), (4, 4)}⟩
def genericToBoat : PMap :=
  ⟨{(0, 20), (1, 21), (2, 22), (3, 23), (4, 4)}⟩
def houseBoatSpan : Span :=
  ⟨genericTheory, houseTheory, boatTheory, genericToHouse, genericToBoat⟩

def houseToHouseboat : PMap :=
  ⟨{(10, 30), (11, 31), (13, 33), (4, 4)}⟩
def boatToHouseboat : PMap :=
  ⟨{(20, 30), (21, 31), (22, 22), (23, 33), (4, 4)}⟩
def houseboatCone : Cone houseBoatSpan :=
  ⟨houseboatTheory, houseToHouseboat, boatToHouseboat, false, false⟩

def houseToBoathouse : PMap :=
  ⟨{(10, 32), (11, 11), (12, 12), (13, 13), (4, 4)}⟩
def boatToBoathouse : PMap :=
  ⟨{(20, 20), (21, 32), (22, 22), (23, 23), (4, 4)}⟩

/-- Figure 5: the House-side triangle is auxiliary. -/
def boathouseCone : Cone houseBoatSpan :=
  ⟨boathouseTheory, houseToBoathouse, boatToBoathouse, true, false⟩
def boathouseConeOtherSideAuxiliary : Cone houseBoatSpan :=
  ⟨boathouseTheory, houseToBoathouse, boatToBoathouse, false, true⟩
def boathouseConeNoAuxiliary : Cone houseBoatSpan :=
  ⟨boathouseTheory, houseToBoathouse, boatToBoathouse, false, false⟩

/- The pre-correction Houseboat kept livein and ride distinct. -/
def splitHouseboatTheory : Theory :=
  ⟨{30, 31, 22, 13, 23, 4}, {(13, 30, 31), (23, 30, 31), (4, 31, 22)}⟩
def houseToSplitHouseboat : PMap :=
  ⟨{(10, 30), (11, 31), (13, 13), (4, 4)}⟩
def boatToSplitHouseboat : PMap :=
  ⟨{(20, 30), (21, 31), (22, 22), (23, 23), (4, 4)}⟩
def splitHouseboatCone : Cone houseBoatSpan :=
  ⟨splitHouseboatTheory, houseToSplitHouseboat, boatToSplitHouseboat, false, false⟩

theorem witnessTheories_wellFormed :
    genericTheory.wellFormed = true ∧ houseTheory.wellFormed = true ∧
    boatTheory.wellFormed = true ∧ houseboatTheory.wellFormed = true ∧
    boathouseTheory.wellFormed = true ∧ splitHouseboatTheory.wellFormed = true := by
  native_decide

theorem witnessMaps_wellFormed :
    genericToHouse.wellFormed genericTheory houseTheory = true ∧
    genericToBoat.wellFormed genericTheory boatTheory = true ∧
    houseToHouseboat.wellFormed houseTheory houseboatTheory = true ∧
    boatToHouseboat.wellFormed boatTheory houseboatTheory = true ∧
    houseToBoathouse.wellFormed houseTheory boathouseTheory = true ∧
    boatToBoathouse.wellFormed boatTheory boathouseTheory = true := by
  native_decide

theorem genericToHouse_carries :
    genericToHouse.carries genericTheory houseTheory = {(3, 0, 1), (4, 1, 2)} := by
  native_decide

theorem genericToBoat_carries :
    genericToBoat.carries genericTheory boatTheory = {(3, 0, 1), (4, 1, 2)} := by
  native_decide

theorem houseToHouseboat_carries :
    houseToHouseboat.carries houseTheory houseboatTheory = {(13, 10, 11)} := by
  native_decide

theorem boatToHouseboat_carries :
    boatToHouseboat.carries boatTheory houseboatTheory = {(23, 20, 21), (4, 21, 22)} := by
  native_decide

theorem houseToBoathouse_carries :
    houseToBoathouse.carries houseTheory boathouseTheory = {(13, 10, 11), (4, 11, 12)} := by
  native_decide

theorem boatToBoathouse_carries :
    boatToBoathouse.carries boatTheory boathouseTheory = {(23, 20, 21), (4, 21, 22)} := by
  native_decide

theorem houseboatCone_consistent : houseboatCone.consistent = true := by
  native_decide

theorem boathouseCone_consistent : boathouseCone.consistent = true := by
  native_decide

theorem boathouse_other_side_auxiliary_consistent :
    boathouseConeOtherSideAuxiliary.consistent = true := by
  native_decide

theorem boathouse_no_auxiliary_inconsistent :
    boathouseConeNoAuxiliary.consistent = false := by
  native_decide

theorem split_houseboat_inconsistent : splitHouseboatCone.consistent = false := by
  native_decide

end DarkTower.WarMachine.ThreeHalvesBlend
