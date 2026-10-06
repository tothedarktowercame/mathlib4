import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
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

/-- Number of unordered pairs of distinct sources sent to one target. -/
def identifications (f : PMap) : Nat :=
  (f.rel ×ˢ f.rel).filter (fun pq => pq.1.1 < pq.2.1 && pq.1.2 = pq.2.2) |>.card

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

theorem wellFormed_of_parts {f : PMap} {A B : Theory}
    (hdom : ∀ p ∈ f.rel, p.1 ∈ A.elems ∧ p.2 ∈ B.elems)
    (hfun : ∀ p ∈ f.rel, ∀ q ∈ f.rel, p.1 = q.1 → p.2 = q.2) :
    f.wellFormed A B = true := by
  simp only [wellFormed, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro p hp
    exact Finset.mem_product.mpr (hdom p hp)
  · apply Finset.card_image_iff.mpr
    intro p hp q hq heq
    exact Prod.ext heq (hfun p hp q hq heq)

theorem comp_wellFormed {A B C : Theory} {f g : PMap}
    (hf : f.wellFormed A B = true) (hg : g.wellFormed B C = true) :
    (PMap.comp f g).wellFormed A C = true := by
  obtain ⟨hfdom, hffun⟩ := wellFormed_parts hf
  obtain ⟨hgdom, hgfun⟩ := wellFormed_parts hg
  apply wellFormed_of_parts
  · intro p hp
    simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp
    obtain ⟨q, ⟨⟨hqf, hqg⟩, _⟩, rfl⟩ := hp
    exact ⟨(hfdom q.1 hqf).1, (hgdom q.2 hqg).2⟩
  · intro p hp q hq heq
    simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hp hq
    obtain ⟨wp, ⟨⟨hpf, hpg⟩, hpm⟩, hpv⟩ := hp
    obtain ⟨wq, ⟨⟨hqf, hqg⟩, hqm⟩, hqv⟩ := hq
    have hs : wp.1.1 = wq.1.1 := by simpa [← hpv, ← hqv] using heq
    have hm : wp.1.2 = wq.1.2 := hffun wp.1 hpf wq.1 hqf hs
    have hgs : wp.2.1 = wq.2.1 := hpm ▸ hqm ▸ hm
    have ht : wp.2.2 = wq.2.2 := hgfun wp.2 hpg wq.2 hqg hgs
    simpa [← hpv, ← hqv] using ht

theorem wellFormed_of_le {A B : Theory} {f g : PMap}
    (hfg : f.le g = true) (hg : g.wellFormed A B = true) :
    f.wellFormed A B = true := by
  simp only [le, decide_eq_true_eq] at hfg
  obtain ⟨hgdom, hgfun⟩ := wellFormed_parts hg
  apply wellFormed_of_parts
  · intro p hp
    exact hgdom p (hfg hp)
  · intro p hp q hq heq
    exact hgfun p (hfg hp) q (hfg hq) heq

theorem comp_assoc (f g h : PMap) :
    PMap.comp (PMap.comp f g) h = PMap.comp f (PMap.comp g h) := by
  apply PMap.ext
  ext p
  simp only [comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
  aesop

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

def Cone.route₁ (s : Span) (c : Cone s) : PMap :=
  if c.aux₁ then PMap.empty else PMap.comp s.a₁ c.b₁

def Cone.route₂ (s : Span) (c : Cone s) : PMap :=
  if c.aux₂ then PMap.empty else PMap.comp s.a₂ c.b₂

/-- The join of the non-auxiliary composites is their least upper bound, so
its well-formedness is equivalent to existence of a well-formed upper bound.
An auxiliary triangle contributes the empty map to this join. -/
def Cone.consistent (s : Span) (c : Cone s) : Bool :=
  (PMap.join (c.route₁) (c.route₂)).wellFormed s.G c.B

theorem both_auxiliary_vacuous (s : Span) (B : Theory) (b₁ b₂ : PMap) :
    (Cone.mk B b₁ b₂ true true : Cone s).consistent = true := by
  simp [Cone.consistent, Cone.route₁, Cone.route₂, PMap.empty,
    PMap.join, PMap.wellFormed]

private def firstTarget (rel : Finset (Nat × Nat)) (g : Nat) : Option Nat :=
  ((rel.filter fun (p : Nat × Nat) => p.1 = g).image Prod.snd).sort (· ≤ ·) |>.head?

private def firstConflict (route₁ route₂ : Finset (Nat × Nat)) :
    List Nat → Option (Nat × Nat × Nat)
  | [] => none
  | g :: gs =>
    match firstTarget route₁ g, firstTarget route₂ g with
    | some x, some y => if x = y then firstConflict route₁ route₂ gs else some (g, x, y)
    | _, _ => firstConflict route₁ route₂ gs

private theorem firstTarget_eq_of_mem {rel : Finset (Nat × Nat)} {g x : Nat}
    (hmem : (g, x) ∈ rel)
    (hfun : ∀ p ∈ rel, ∀ q ∈ rel, p.1 = q.1 → p.2 = q.2) :
    firstTarget rel g = some x := by
  have himage : (rel.filter fun p => p.1 = g).image Prod.snd = {x} := by
    ext y
    constructor
    · intro hy
      simp only [Finset.mem_image, Finset.mem_filter] at hy
      obtain ⟨p, ⟨hp, hpg⟩, hpy⟩ := hy
      have : p.2 = x := hfun p hp (g, x) hmem hpg
      simp [← hpy, this]
    · intro hy
      simp only [Finset.mem_singleton] at hy
      subst y
      exact Finset.mem_image.mpr ⟨(g, x), Finset.mem_filter.mpr ⟨hmem, rfl⟩, rfl⟩
  simp [firstTarget, himage]

private theorem mem_of_head?_eq_some {α : Type} {l : List α} {x : α}
    (h : l.head? = some x) : x ∈ l := by
  cases l with
  | nil => simp at h
  | cons a as => simp at h ⊢; exact Or.inl h.symm

private theorem firstTarget_mem {rel : Finset (Nat × Nat)} {g x : Nat}
    (h : firstTarget rel g = some x) : (g, x) ∈ rel := by
  unfold firstTarget at h
  have hx : x ∈ ((rel.filter fun p => p.1 = g).image Prod.snd).sort (· ≤ ·) :=
    mem_of_head?_eq_some h
  simp only [Finset.mem_sort, Finset.mem_image, Finset.mem_filter] at hx
  obtain ⟨p, ⟨hp, hpg⟩, hpx⟩ := hx
  simpa [← hpg, ← hpx] using hp

private theorem firstConflict_none_of_cross_equal {route₁ route₂ : Finset (Nat × Nat)}
    (gs : List Nat)
    (heq : ∀ g x y, g ∈ gs → (g, x) ∈ route₁ → (g, y) ∈ route₂ → x = y) :
    firstConflict route₁ route₂ gs = none := by
  induction gs with
  | nil => rfl
  | cons g gs ih =>
    simp only [firstConflict]
    cases h₁ : firstTarget route₁ g <;> cases h₂ : firstTarget route₂ g
    · exact ih (fun a x y ha hx hy => heq a x y (by simp [ha]) hx hy)
    · exact ih (fun a x y ha hx hy => heq a x y (by simp [ha]) hx hy)
    · exact ih (fun a x y ha hx hy => heq a x y (by simp [ha]) hx hy)
    · rename_i x y
      have hxy : x = y := heq g x y (by simp)
        (firstTarget_mem h₁) (firstTarget_mem h₂)
      simp [hxy]
      exact ih (fun a x y ha hx hy => heq a x y (by simp [ha]) hx hy)

private theorem firstConflict_none_imp {route₁ route₂ : Finset (Nat × Nat)}
    {gs : List Nat} (hnone : firstConflict route₁ route₂ gs = none)
    {g x y : Nat} (hg : g ∈ gs)
    (hx : firstTarget route₁ g = some x) (hy : firstTarget route₂ g = some y) : x = y := by
  induction gs with
  | nil => simp at hg
  | cons a as ih =>
    simp only [List.mem_cons] at hg
    rcases hg with rfl | hg
    · by_cases hxy : x = y
      · exact hxy
      · simp [firstConflict, hx, hy, hxy] at hnone
    · apply ih ?_ hg
      cases h₁ : firstTarget route₁ a <;> cases h₂ : firstTarget route₂ a
      · simpa [firstConflict, h₁, h₂] using hnone
      · simpa [firstConflict, h₁, h₂] using hnone
      · simpa [firstConflict, h₁, h₂] using hnone
      · rename_i u v
        by_cases huv : u = v
        · simpa [firstConflict, h₁, h₂, huv] using hnone
        · simp [firstConflict, h₁, h₂, huv] at hnone

/-- First source, in Nat order, on which the two non-auxiliary routes disagree.
The targets are ordered by route, not by their Nat values. Endpoint failures
are deliberately not encoded by this witness type. -/
def Cone.inconsistencyWitness (s : Span) (c : Cone s) : Option (Nat × Nat × Nat) :=
  firstConflict c.route₁.rel c.route₂.rel (s.G.elems.sort (· ≤ ·))

theorem inconsistencyWitness_none_iff (s : Span) (c : Cone s)
    (ha₁ : s.a₁.wellFormed s.G s.I₁ = true)
    (ha₂ : s.a₂.wellFormed s.G s.I₂ = true)
    (hb₁ : c.b₁.wellFormed s.I₁ c.B = true)
    (hb₂ : c.b₂.wellFormed s.I₂ c.B = true) :
    c.inconsistencyWitness = none ↔ c.consistent = true := by
  have hr₁ : c.route₁.wellFormed s.G c.B = true := by
    unfold Cone.route₁
    split
    · simp [PMap.empty, PMap.wellFormed]
    · exact PMap.comp_wellFormed ha₁ hb₁
  have hr₂ : c.route₂.wellFormed s.G c.B = true := by
    unfold Cone.route₂
    split
    · simp [PMap.empty, PMap.wellFormed]
    · exact PMap.comp_wellFormed ha₂ hb₂
  obtain ⟨hd₁, hf₁⟩ := PMap.wellFormed_parts hr₁
  obtain ⟨hd₂, hf₂⟩ := PMap.wellFormed_parts hr₂
  constructor
  · intro hn
    apply PMap.wellFormed_of_parts
    · intro p hp
      simp only [PMap.join, Finset.mem_union] at hp
      rcases hp with hp | hp
      · exact hd₁ p hp
      · exact hd₂ p hp
    · intro p hp q hq heq
      simp only [PMap.join, Finset.mem_union] at hp hq
      rcases hp with hp | hp <;> rcases hq with hq | hq
      · exact hf₁ p hp q hq heq
      · have hg : p.1 ∈ s.G.elems := (hd₁ p hp).1
        have hgl : p.1 ∈ s.G.elems.sort (· ≤ ·) := by simpa
        have hq' : (p.1, q.2) ∈ c.route₂.rel := by simpa [heq] using hq
        have ht := firstConflict_none_imp (by simpa [Cone.inconsistencyWitness] using hn)
          hgl (firstTarget_eq_of_mem hp hf₁) (firstTarget_eq_of_mem hq' hf₂)
        exact ht
      · have hg : q.1 ∈ s.G.elems := (hd₁ q hq).1
        have hgl : q.1 ∈ s.G.elems.sort (· ≤ ·) := by simpa
        have hp' : (q.1, p.2) ∈ c.route₂.rel := by rw [← heq]; exact hp
        have ht := firstConflict_none_imp (by simpa [Cone.inconsistencyWitness] using hn)
          hgl (firstTarget_eq_of_mem hq hf₁) (firstTarget_eq_of_mem hp' hf₂)
        exact ht.symm
      · exact hf₂ p hp q hq heq
  · intro hc
    obtain ⟨_, hjfun⟩ := PMap.wellFormed_parts hc
    apply firstConflict_none_of_cross_equal
    intro g x y _ hx hy
    exact hjfun (g, x) (by simp [PMap.join, hx]) (g, y)
      (by simp [PMap.join, hy]) rfl

/-- K1' coverage: the literal Definition 7 on this carrier (discovery note
§2), not Goguen's optimality distinction (`Cone.quality`). Auxiliary flags
remove span triangles from consistency; both surviving cone legs cover B. -/
def Cone.isPushout {s : Span} (c : Cone s) : Bool :=
  c.consistent && decide (c.B.elems ⊆
    c.b₁.rel.image Prod.snd ∪ c.b₂.rel.image Prod.snd)

def Mediator {s : Span} (c : Cone s) (C : Theory) (c₁ c₂ h : PMap) : Prop :=
  h.wellFormed c.B C = true ∧
    (PMap.comp c.b₁ h).le c₁ = true ∧ (PMap.comp c.b₂ h).le c₂ = true

def IsThreeHalvesPushout (s : Span) (c : Cone s) : Prop :=
  c.consistent = true ∧
    ∀ (C : Theory) (c₁ c₂ : PMap),
      c₁.wellFormed s.I₁ C = true → c₂.wellFormed s.I₂ C = true →
      (Cone.mk C c₁ c₂ c.aux₁ c.aux₂ : Cone s).consistent = true →
      ∃ h, Mediator c C c₁ c₂ h ∧
        ∀ h', Mediator c C c₁ c₂ h' → h'.le h = true

private def maximumMediator {s : Span} (c : Cone s) (C : Theory)
    (c₁ c₂ : PMap) : PMap :=
  ⟨(c.B.elems ×ˢ C.elems).filter fun uv => decide
    ((∀ iu ∈ c.b₁.rel, iu.2 = uv.1 → (iu.1, uv.2) ∈ c₁.rel) ∧
      (∀ ju ∈ c.b₂.rel, ju.2 = uv.1 → (ju.1, uv.2) ∈ c₂.rel))⟩

theorem pushout_iff_coverage (s : Span) (c : Cone s)
    (_ha₁ : s.a₁.wellFormed s.G s.I₁ = true)
    (_ha₂ : s.a₂.wellFormed s.G s.I₂ = true)
    (_hb₁ : c.b₁.wellFormed s.I₁ c.B = true)
    (_hb₂ : c.b₂.wellFormed s.I₂ c.B = true) :
    IsThreeHalvesPushout s c ↔ c.isPushout = true := by
  constructor
  · rintro ⟨hconsistent, hmax⟩
    simp only [Cone.isPushout, Bool.and_eq_true, decide_eq_true_eq]
    refine ⟨hconsistent, ?_⟩
    intro u huB
    by_contra hu
    simp only [Finset.mem_union, Finset.mem_image, not_or, not_exists,
      not_and] at hu
    let C : Theory := ⟨{0, 1}, ∅⟩
    let emptyMap : PMap := PMap.empty
    have hempty₁ : emptyMap.wellFormed s.I₁ C = true := by
      simp [emptyMap, PMap.empty, PMap.wellFormed]
    have hempty₂ : emptyMap.wellFormed s.I₂ C = true := by
      simp [emptyMap, PMap.empty, PMap.wellFormed]
    have hcomparison :
        (Cone.mk C emptyMap emptyMap c.aux₁ c.aux₂ : Cone s).consistent = true := by
      simp [Cone.consistent, Cone.route₁, Cone.route₂, emptyMap,
        PMap.empty, PMap.comp, PMap.join, PMap.wellFormed]
    obtain ⟨h, hh, hgreatest⟩ := hmax C emptyMap emptyMap hempty₁ hempty₂ hcomparison
    let h₀ : PMap := ⟨{(u, 0)}⟩
    let h₁ : PMap := ⟨{(u, 1)}⟩
    have hcomp₀ (b : PMap) (hno : ∀ x ∈ b.rel, x.2 ≠ u) :
        PMap.comp b h₀ = PMap.empty := by
      apply PMap.ext
      ext p
      constructor
      · intro hp
        simp only [PMap.comp, h₀, Finset.mem_image, Finset.mem_filter,
          Finset.mem_product] at hp
        obtain ⟨q, ⟨⟨hqb, hqh⟩, hmatch⟩, _⟩ := hp
        simp only [Finset.mem_singleton] at hqh
        exact (hno q.1 hqb (by rw [hmatch, hqh])).elim
      · simp [PMap.empty]
    have hcomp₁ (b : PMap) (hno : ∀ x ∈ b.rel, x.2 ≠ u) :
        PMap.comp b h₁ = PMap.empty := by
      apply PMap.ext
      ext p
      constructor
      · intro hp
        simp only [PMap.comp, h₁, Finset.mem_image, Finset.mem_filter,
          Finset.mem_product] at hp
        obtain ⟨q, ⟨⟨hqb, hqh⟩, hmatch⟩, _⟩ := hp
        simp only [Finset.mem_singleton] at hqh
        exact (hno q.1 hqb (by rw [hmatch, hqh])).elim
      · simp [PMap.empty]
    have hno₁ : ∀ x ∈ c.b₁.rel, x.2 ≠ u := by
      intro x hx heq
      exact hu.1 x hx heq
    have hno₂ : ∀ x ∈ c.b₂.rel, x.2 ≠ u := by
      intro x hx heq
      exact hu.2 x hx heq
    have hm₀ : Mediator c C emptyMap emptyMap h₀ := by
      refine ⟨?_, ?_, ?_⟩
      · apply PMap.wellFormed_of_parts
        · intro p hp
          simp only [h₀, Finset.mem_singleton] at hp
          rcases hp with ⟨rfl, rfl⟩
          exact ⟨huB, by simp [C]⟩
        · intro p hp q hq _
          simp only [h₀, Finset.mem_singleton] at hp hq
          simp [hp, hq]
      · simp [hcomp₀ c.b₁ hno₁, PMap.le, PMap.empty]
      · simp [hcomp₀ c.b₂ hno₂, PMap.le, PMap.empty]
    have hm₁ : Mediator c C emptyMap emptyMap h₁ := by
      refine ⟨?_, ?_, ?_⟩
      · apply PMap.wellFormed_of_parts
        · intro p hp
          simp only [h₁, Finset.mem_singleton] at hp
          rcases hp with ⟨rfl, rfl⟩
          exact ⟨huB, by simp [C]⟩
        · intro p hp q hq _
          simp only [h₁, Finset.mem_singleton] at hp hq
          simp [hp, hq]
      · simp [hcomp₁ c.b₁ hno₁, PMap.le, PMap.empty]
      · simp [hcomp₁ c.b₂ hno₂, PMap.le, PMap.empty]
    have hle₀ := hgreatest h₀ hm₀
    have hle₁ := hgreatest h₁ hm₁
    obtain ⟨_, hhfun⟩ := PMap.wellFormed_parts hh.1
    simp only [PMap.le, decide_eq_true_eq] at hle₀ hle₁
    have hp₀ : (u, 0) ∈ h.rel := hle₀ (by simp [h₀])
    have hp₁ : (u, 1) ∈ h.rel := hle₁ (by simp [h₁])
    have : (0 : Nat) = 1 := hhfun (u, 0) hp₀ (u, 1) hp₁ rfl
    omega
  · intro hp
    simp only [Cone.isPushout, Bool.and_eq_true, decide_eq_true_eq] at hp
    refine ⟨hp.1, ?_⟩
    intro C c₁ c₂ hc₁ hc₂ _hcomparison
    let H := maximumMediator c C c₁ c₂
    obtain ⟨hc₁dom, hc₁fun⟩ := PMap.wellFormed_parts hc₁
    obtain ⟨hc₂dom, hc₂fun⟩ := PMap.wellFormed_parts hc₂
    have hHwf : H.wellFormed c.B C = true := by
      apply PMap.wellFormed_of_parts
      · intro p hpH
        have hpH' : p ∈ (maximumMediator c C c₁ c₂).rel := by simpa [H] using hpH
        simpa [maximumMediator] using (Finset.mem_filter.mp hpH').1
      · intro p hpH q hqH heq
        have hpH' : p ∈ (maximumMediator c C c₁ c₂).rel := by simpa [H] using hpH
        have hqH' : q ∈ (maximumMediator c C c₁ c₂).rel := by simpa [H] using hqH
        have pp := (Finset.mem_filter.mp hpH').2
        have qq := (Finset.mem_filter.mp hqH').2
        simp only [decide_eq_true_eq] at pp qq
        have hcov := hp.2 (Finset.mem_product.mp (Finset.mem_filter.mp hpH').1).1
        simp only [Finset.mem_union, Finset.mem_image] at hcov
        rcases hcov with ⟨i, hi, hiu⟩ | ⟨j, hj, hju⟩
        · have hip : (i.1, p.2) ∈ c₁.rel := pp.1 i hi hiu
          have hiq : (i.1, q.2) ∈ c₁.rel := qq.1 i hi (hiu.trans heq)
          exact hc₁fun (i.1, p.2) hip (i.1, q.2) hiq rfl
        · have hjp : (j.1, p.2) ∈ c₂.rel := pp.2 j hj hju
          have hjq : (j.1, q.2) ∈ c₂.rel := qq.2 j hj (hju.trans heq)
          exact hc₂fun (j.1, p.2) hjp (j.1, q.2) hjq rfl
    refine ⟨H, ⟨hHwf, ?_, ?_⟩, ?_⟩
    · simp only [PMap.le, decide_eq_true_eq]
      intro p hpcomp
      simp only [PMap.comp, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product] at hpcomp
      obtain ⟨q, ⟨⟨hqb, hqH⟩, hmatch⟩, rfl⟩ := hpcomp
      have hqH' : q.2 ∈ (maximumMediator c C c₁ c₂).rel := by simpa [H] using hqH
      have hpred := (Finset.mem_filter.mp hqH').2
      simp only [decide_eq_true_eq] at hpred
      exact hpred.1 q.1 hqb hmatch
    · simp only [PMap.le, decide_eq_true_eq]
      intro p hpcomp
      simp only [PMap.comp, Finset.mem_image, Finset.mem_filter,
        Finset.mem_product] at hpcomp
      obtain ⟨q, ⟨⟨hqb, hqH⟩, hmatch⟩, rfl⟩ := hpcomp
      have hqH' : q.2 ∈ (maximumMediator c C c₁ c₂).rel := by simpa [H] using hqH
      have hpred := (Finset.mem_filter.mp hqH').2
      simp only [decide_eq_true_eq] at hpred
      exact hpred.2 q.1 hqb hmatch
    · intro h' hh'
      simp only [PMap.le, decide_eq_true_eq]
      intro uv huv
      obtain ⟨h'dom, _⟩ := PMap.wellFormed_parts hh'.1
      have hle₁ := hh'.2.1
      have hle₂ := hh'.2.2
      simp only [PMap.le, decide_eq_true_eq] at hle₁ hle₂
      change uv ∈ (maximumMediator c C c₁ c₂).rel
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_product.mpr (h'dom uv huv), ?_⟩
      simp only [decide_eq_true_eq]
      constructor
      · intro iu hi heq
        apply hle₁
        simp only [PMap.comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
        exact ⟨(iu, uv), ⟨⟨hi, huv⟩, heq⟩, rfl⟩
      · intro ju hj heq
        apply hle₂
        simp only [PMap.comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
        exact ⟨(ju, uv), ⟨⟨hj, huv⟩, heq⟩, rfl⟩

structure ConeQuality where
  carries₁ : Finset (Nat × Nat × Nat)
  carries₂ : Finset (Nat × Nat × Nat)
  dom₁ : Finset Nat
  dom₂ : Finset Nat
  ident₁ : Nat
  ident₂ : Nat
  deriving DecidableEq

def Cone.quality {s : Span} (c : Cone s) : ConeQuality :=
  { carries₁ := c.b₁.carries s.I₁ c.B
    carries₂ := c.b₂.carries s.I₂ c.B
    dom₁ := c.b₁.rel.image Prod.fst
    dom₂ := c.b₂.rel.image Prod.fst
    ident₁ := c.b₁.identifications
    ident₂ := c.b₂.identifications }

/-- K2': fewer identifications first; at equal identification counts, more
carried axioms and larger domains. Both legs are compared conjunctively. -/
def Cone.qualityLE {s : Span} (c d : Cone s) : Bool :=
  let qc := c.quality
  let qd := d.quality
  decide (qd.ident₁ ≤ qc.ident₁ ∧ qd.ident₂ ≤ qc.ident₂ ∧
    ((qd.ident₁ = qc.ident₁ ∧ qd.ident₂ = qc.ident₂) →
      qc.carries₁ ⊆ qd.carries₁ ∧ qc.carries₂ ⊆ qd.carries₂ ∧
      qc.dom₁ ⊆ qd.dom₁ ∧ qc.dom₂ ⊆ qd.dom₂))

theorem Cone.qualityLE_refl {s : Span} (c : Cone s) : c.qualityLE c = true := by
  simp [Cone.qualityLE]

theorem Cone.qualityLE_trans {s : Span} {c d e : Cone s}
    (hcd : c.qualityLE d = true) (hde : d.qualityLE e = true) :
    c.qualityLE e = true := by
  simp only [Cone.qualityLE, decide_eq_true_eq] at hcd hde ⊢
  refine ⟨Nat.le_trans hde.1 hcd.1, Nat.le_trans hde.2.1 hcd.2.1, ?_⟩
  rintro ⟨hec₁, hec₂⟩
  have hdc₁ : (d.quality).ident₁ = (c.quality).ident₁ :=
    Nat.le_antisymm hcd.1 (hec₁ ▸ hde.1)
  have hdc₂ : (d.quality).ident₂ = (c.quality).ident₂ :=
    Nat.le_antisymm hcd.2.1 (hec₂ ▸ hde.2.1)
  have hed₁ : (e.quality).ident₁ = (d.quality).ident₁ := hec₁.trans hdc₁.symm
  have hed₂ : (e.quality).ident₂ = (d.quality).ident₂ := hec₂.trans hdc₂.symm
  obtain ⟨hcdC₁, hcdC₂, hcdD₁, hcdD₂⟩ := hcd.2.2 ⟨hdc₁, hdc₂⟩
  obtain ⟨hdeC₁, hdeC₂, hdeD₁, hdeD₂⟩ := hde.2.2 ⟨hed₁, hed₂⟩
  exact ⟨fun _ h => hdeC₁ (hcdC₁ h), fun _ h => hdeC₂ (hcdC₂ h),
    fun _ h => hdeD₁ (hcdD₁ h), fun _ h => hdeD₂ (hcdD₂ h)⟩

private def PMap.graphsFrom (sources : List Nat) (targets : Finset Nat) :
    List (Finset (Nat × Nat)) :=
  match sources with
  | [] => [∅]
  | x :: xs => (PMap.graphsFrom xs targets).flatMap fun rel =>
      rel :: (targets.sort (· ≤ ·)).map fun y => insert (x, y) rel

/-- The `(n+1)^m` partial functional graphs between two finite element sets. -/
def PMap.allGraphs (A B : Theory) : List (Finset (Nat × Nat)) :=
  PMap.graphsFrom (A.elems.sort (· ≤ ·)) B.elems

/-- Cone isomorphism by enumeration of partial functional graphs. The graph
and transpose are total well-formed maps; legs commute and axioms map both ways. -/
def Cone.isoCones {s : Span} (c d : Cone s) : Bool :=
  decide (∃ rel ∈ PMap.allGraphs c.B d.B,
    let φ : PMap := ⟨rel⟩
    let ψ : PMap := ⟨rel.image Prod.swap⟩
    φ.wellFormed c.B d.B = true ∧ ψ.wellFormed d.B c.B = true ∧
    rel.image Prod.fst = c.B.elems ∧ rel.image Prod.snd = d.B.elems ∧
    PMap.comp c.b₁ φ = d.b₁ ∧ PMap.comp c.b₂ φ = d.b₂ ∧
    φ.carries c.B d.B = c.B.axioms ∧ ψ.carries d.B c.B = d.B.axioms)

/-! ## Policies, gluing, and structural verdicts -/

inductive Role | G | I₁ | I₂ | B
  deriving DecidableEq, Repr

structure Square where
  G : Theory
  I₁ : Theory
  I₂ : Theory
  B : Theory
  a₁ : PMap
  a₂ : PMap
  b₁ : PMap
  b₂ : PMap
  aux₁ : Bool
  aux₂ : Bool
  deriving DecidableEq

def Square.span (q : Square) : Span := ⟨q.G, q.I₁, q.I₂, q.a₁, q.a₂⟩
def Square.cone (q : Square) : Cone q.span := ⟨q.B, q.b₁, q.b₂, q.aux₁, q.aux₂⟩

/-- On-the-nose equality of the two routes. Auxiliary flags are intentionally
ignored: Proposition 8 uses this equality, not merely consistency after a
triangle has been omitted. -/
def Square.commutes (q : Square) : Bool :=
  decide (PMap.comp q.a₁ q.b₁ = PMap.comp q.a₂ q.b₂)

def Square.object (q : Square) : Role → Theory
  | .G => q.G
  | .I₁ => q.I₁
  | .I₂ => q.I₂
  | .B => q.B

/-- Vertical pasting. The second square must have the first square's `I₁` as
ground, its `b₁` as second span leg, and the first square's `B` as that leg's
codomain. The composite has span `(a₁;a₃, a₂)` and cone `(c₁, b₂;c₂)`. -/
def pastedDiamond (d₁ d₂ : Square) : Option Square :=
  if d₂.G = d₁.I₁ ∧ d₂.I₂ = d₁.B ∧ d₂.a₂ = d₁.b₁ then
    some
      { G := d₁.G
        I₁ := d₂.I₁
        I₂ := d₁.I₂
        B := d₂.B
        a₁ := PMap.comp d₁.a₁ d₂.a₁
        a₂ := d₁.a₂
        b₁ := d₂.b₁
        b₂ := PMap.comp d₁.b₂ d₂.b₂
        aux₁ := d₁.aux₁ || d₂.aux₁
        aux₂ := d₁.aux₂ || d₂.aux₂ }
  else none

structure Gluing where
  i : Nat
  rᵢ : Role
  j : Nat
  rⱼ : Role
  iso : PMap
  deriving DecidableEq

structure Policy where
  squares : List Square
  gluings : List Gluing
  applicationOrder : List (Nat × Nat × Nat)
  deriving DecidableEq

private def Gluing.wellFormed (squares : List Square) (g : Gluing) : Bool :=
  match squares[g.i]?, squares[g.j]? with
  | some qi, some qj =>
    let A := qi.object g.rᵢ
    let B := qj.object g.rⱼ
    let inv : PMap := ⟨g.iso.rel.image Prod.swap⟩
    g.iso.wellFormed A B && inv.wellFormed B A &&
      decide (g.iso.rel.image Prod.fst = A.elems) &&
      decide (g.iso.rel.image Prod.snd = B.elems) &&
      decide (g.iso.carries A B = A.axioms) && decide (inv.carries B A = B.axioms)
  | _, _ => false

def Policy.wellFormed (p : Policy) : Bool :=
  p.gluings.all (Gluing.wellFormed p.squares)

private def componentStep (squares : List Square) (gluings : List Gluing)
    (seen : Finset Nat) : Finset Nat :=
  gluings.foldl (fun acc g =>
    if g.i ∈ acc ∧ g.j < squares.length then insert g.j acc
    else if g.j ∈ acc ∧ g.i < squares.length then insert g.i acc
    else acc) seen

private def componentClosure (squares : List Square) (gluings : List Gluing) :
    Nat → Finset Nat → Finset Nat
  | 0, seen => seen
  | n + 1, seen => componentClosure squares gluings n
      (componentStep squares gluings seen)

private def component (squares : List Square) (gluings : List Gluing) (i : Nat) : List Nat :=
  (componentClosure squares gluings squares.length {i}).sort (· ≤ ·)

private def addComponent (squares : List Square) (gluings : List Gluing)
    (cs : List (List Nat)) (i : Nat) :
    List (List Nat) :=
  if cs.any (fun c => i ∈ c) then cs else cs ++ [component squares gluings i]

/-- Connected components in increasing order of their least square index. -/
def Policy.components (p : Policy) : List (List Nat) :=
  (List.range p.squares.length).foldl (addComponent p.squares p.gluings) []

private theorem componentStep_subset (squares : List Square) (gluings : List Gluing)
    (seen : Finset Nat) : seen ⊆ componentStep squares gluings seen := by
  unfold componentStep
  induction gluings generalizing seen with
  | nil => simp
  | cons g gs ih =>
    simp only [List.foldl_cons]
    apply Finset.Subset.trans (s₂ := if g.i ∈ seen ∧ g.j < squares.length then
      insert g.j seen else if g.j ∈ seen ∧ g.i < squares.length then insert g.i seen else seen)
    · by_cases h₁ : g.i ∈ seen ∧ g.j < squares.length
      · simp [h₁]
      · by_cases h₂ : g.j ∈ seen ∧ g.i < squares.length <;> simp [h₁, h₂]
    · apply ih

private theorem componentClosure_subset (squares : List Square) (gluings : List Gluing)
    (n : Nat) (seen : Finset Nat) :
    seen ⊆ componentClosure squares gluings n seen := by
  induction n generalizing seen with
  | zero => exact Finset.Subset.rfl
  | succ n ih =>
    exact Finset.Subset.trans (componentStep_subset squares gluings seen)
      (ih (componentStep squares gluings seen))

private theorem mem_component_self (squares : List Square) (gluings : List Gluing)
    (i : Nat) : i ∈ component squares gluings i := by
  simp only [component, Finset.mem_sort]
  exact componentClosure_subset squares gluings squares.length {i} (by simp)

private theorem mem_flatten_addComponent (squares : List Square) (gluings : List Gluing)
    (cs : List (List Nat)) (i : Nat) :
    i ∈ (addComponent squares gluings cs i).flatten := by
  unfold addComponent
  split
  · rename_i h
    simp only [List.any_eq_true] at h
    obtain ⟨c, hc, hic⟩ := h
    exact List.mem_flatten.mpr ⟨c, hc, of_decide_eq_true hic⟩
  · simp [mem_component_self]

private theorem mem_flatten_addComponent_of_mem (squares : List Square)
    (gluings : List Gluing) (cs : List (List Nat)) (i x : Nat)
    (hx : x ∈ cs.flatten) : x ∈ (addComponent squares gluings cs i).flatten := by
  unfold addComponent
  split
  · exact hx
  · simp only [List.flatten_append, List.mem_append]
    exact Or.inl hx

private theorem fold_addComponent_preserves (squares : List Square)
    (gluings : List Gluing) (xs : List Nat) (cs : List (List Nat)) (x : Nat)
    (hx : x ∈ cs.flatten) :
    x ∈ (xs.foldl (addComponent squares gluings) cs).flatten := by
  induction xs generalizing cs with
  | nil => exact hx
  | cons i is ih =>
    simp only [List.foldl_cons]
    exact ih _ (mem_flatten_addComponent_of_mem squares gluings cs i x hx)

private theorem fold_addComponent_covers (squares : List Square)
    (gluings : List Gluing) (xs : List Nat) (cs : List (List Nat))
    {i : Nat} (hi : i ∈ xs) :
    i ∈ (xs.foldl (addComponent squares gluings) cs).flatten := by
  induction xs generalizing cs with
  | nil => simp at hi
  | cons x xs ih =>
    simp only [List.mem_cons] at hi
    simp only [List.foldl_cons]
    rcases hi with rfl | hi
    · exact fold_addComponent_preserves squares gluings xs _ i
        (mem_flatten_addComponent squares gluings cs i)
    · exact ih _ hi

/-- Every square index occurs in at least one computed component. Exact-once
requires the additional disjointness invariant for closure merging. -/
theorem components_cover (p : Policy) {i : Nat} (hi : i < p.squares.length) :
    i ∈ p.components.flatten := by
  apply fold_addComponent_covers p.squares p.gluings (List.range p.squares.length) []
  exact List.mem_range.mpr hi

inductive Verdict
  | bag (components : List (List Nat))
  | cascade
  deriving DecidableEq, Repr

def Policy.verdict (p : Policy) : Verdict :=
  if p.wellFormed && p.components.length = 1 && 0 < p.squares.length then
    .cascade
  else .bag p.components

private def Gluing.constructionEdge (g : Gluing) : Option (Nat × Nat) :=
  if g.rᵢ = .B ∧ g.rⱼ ≠ .B then some (g.i, g.j)
  else if g.rⱼ = .B ∧ g.rᵢ ≠ .B then some (g.j, g.i)
  else none

/-- Derived construction order. The application order is a separate carrier. -/
def Policy.constructionOrder (p : Policy) : List (Nat × Nat) :=
  (p.gluings.filterMap Gluing.constructionEdge).eraseDups

theorem verdict_cascade_iff (p : Policy) :
    p.verdict = .cascade ↔ p.wellFormed = true ∧ p.components.length = 1 := by
  simp only [Policy.verdict, Bool.and_eq_true]
  by_cases hw : p.wellFormed = true <;> simp [hw]
  by_cases hc : p.components.length = 1 <;> simp [hc]
  have : 0 < p.squares.length := by
    by_contra h
    have hz : p.squares.length = 0 := Nat.eq_zero_of_not_pos h
    simp [Policy.components, hz] at hc
  have hne : p.squares ≠ [] := List.ne_nil_of_length_pos this
  simp [hne]

theorem applicationOrder_independent (p : Policy) (L : List (Nat × Nat × Nat)) :
    ({p with applicationOrder := L}).verdict = p.verdict ∧
      ({p with applicationOrder := L}).constructionOrder = p.constructionOrder := by
  cases p
  simp [Policy.verdict, Policy.wellFormed, Policy.components, Policy.constructionOrder]

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

/- Additional K1'--K3 witnesses. Code 40 is the one-point blend. The renamed
Houseboat shifts its five element codes by 100. -/
def amphibiousRVTheory : Theory :=
  ⟨{30, 31, 12, 22, 33, 4}, {(33, 30, 31), (4, 31, 12), (4, 31, 22)}⟩
def houseToRV : PMap :=
  ⟨{(10, 30), (11, 31), (12, 12), (13, 33), (4, 4)}⟩
def boatToRV : PMap :=
  ⟨{(20, 30), (21, 31), (22, 22), (23, 33), (4, 4)}⟩
def rvCone : Cone houseBoatSpan :=
  ⟨amphibiousRVTheory, houseToRV, boatToRV, true, false⟩
def rvConeOtherSideAuxiliary : Cone houseBoatSpan :=
  ⟨amphibiousRVTheory, houseToRV, boatToRV, false, true⟩
def rvConeNoAuxiliary : Cone houseBoatSpan :=
  ⟨amphibiousRVTheory, houseToRV, boatToRV, false, false⟩

def onePointTheory : Theory := ⟨{40}, {(40, 40, 40)}⟩
def houseToOnePoint : PMap :=
  ⟨{(10, 40), (11, 40), (12, 40), (13, 40), (4, 40)}⟩
def boatToOnePoint : PMap :=
  ⟨{(20, 40), (21, 40), (22, 40), (23, 40), (4, 40)}⟩
def onePointCone : Cone houseBoatSpan :=
  ⟨onePointTheory, houseToOnePoint, boatToOnePoint, false, false⟩

def waterDroppingTheory : Theory := ⟨houseboatTheory.elems, {(33, 30, 31)}⟩
def waterDroppingCone : Cone houseBoatSpan :=
  ⟨waterDroppingTheory, houseToHouseboat, boatToHouseboat, false, false⟩

def landHouseboatTheory : Theory :=
  ⟨{30, 31, 12, 33, 4}, {(33, 30, 31), (4, 31, 12)}⟩
def houseToLandHouseboat : PMap :=
  ⟨{(10, 30), (11, 31), (12, 12), (13, 33), (4, 4)}⟩
def boatToLandHouseboat : PMap :=
  ⟨{(20, 30), (21, 31), (23, 33), (4, 4)}⟩
def landHouseboatCone : Cone houseBoatSpan :=
  ⟨landHouseboatTheory, houseToLandHouseboat, boatToLandHouseboat, false, false⟩

def renamedHouseboatTheory : Theory :=
  ⟨{130, 131, 122, 133, 104}, {(133, 130, 131), (104, 131, 122)}⟩
def houseToRenamedHouseboat : PMap :=
  ⟨{(10, 130), (11, 131), (13, 133), (4, 104)}⟩
def boatToRenamedHouseboat : PMap :=
  ⟨{(20, 130), (21, 131), (22, 122), (23, 133), (4, 104)}⟩
def renamedHouseboatCone : Cone houseBoatSpan :=
  ⟨renamedHouseboatTheory, houseToRenamedHouseboat,
    boatToRenamedHouseboat, false, false⟩

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

theorem addedWitnesses_wellFormed :
    amphibiousRVTheory.wellFormed = true ∧ onePointTheory.wellFormed = true ∧
    waterDroppingTheory.wellFormed = true ∧ landHouseboatTheory.wellFormed = true ∧
    renamedHouseboatTheory.wellFormed = true := by
  native_decide

theorem landHouseboat_consistent : landHouseboatCone.consistent = true := by
  native_decide

theorem rv_no_auxiliary_inconsistent : rvConeNoAuxiliary.consistent = false := by
  native_decide

/-- Under K1' Boathouse with its House triangle auxiliary is a pushout: the
flag removes that triangle from consistency, while both legs cover the blend.
This was false under the superseded K1, which omitted auxiliary legs from
coverage as well. -/
theorem k1PushoutWitnesses :
    houseboatCone.isPushout = true ∧
    boathouseCone.isPushout = true ∧
    boathouseConeNoAuxiliary.isPushout = false ∧
    onePointCone.isPushout = true ∧
    waterDroppingCone.isPushout = true ∧
    rvCone.isPushout = true ∧
    rvConeOtherSideAuxiliary.isPushout = true ∧
    rvConeNoAuxiliary.isPushout = false ∧
    landHouseboatCone.isPushout = true := by
  native_decide

theorem rv_strictly_better_than_houseboat :
    houseboatCone.qualityLE rvCone = true ∧ rvCone.qualityLE houseboatCone = false := by
  native_decide

theorem houseboat_strictly_better_than_waterDropping :
    waterDroppingCone.qualityLE houseboatCone = true ∧
      houseboatCone.qualityLE waterDroppingCone = false := by
  native_decide

theorem onePoint_below_named_witnesses :
    onePointCone.qualityLE houseboatCone = true ∧
    houseboatCone.qualityLE onePointCone = false ∧
    onePointCone.qualityLE rvCone = true ∧ rvCone.qualityLE onePointCone = false ∧
    onePointCone.qualityLE waterDroppingCone = true ∧
      waterDroppingCone.qualityLE onePointCone = false := by
  native_decide

theorem houseboat_landHouseboat_incomparable :
    houseboatCone.qualityLE landHouseboatCone = false ∧
      landHouseboatCone.qualityLE houseboatCone = false := by
  native_decide

theorem houseboat_rv_not_isomorphic : houseboatCone.isoCones rvCone = false := by
  native_decide

theorem houseboat_self_isomorphic : houseboatCone.isoCones houseboatCone = true := by
  native_decide

theorem renamed_houseboat_isomorphic :
    houseboatCone.isoCones renamedHouseboatCone = true := by
  native_decide

theorem land_houseboat_not_isomorphic :
    houseboatCone.isoCones landHouseboatCone = false := by
  native_decide

/-! ## Policy witnesses

The click witness records the four unconnected occurrences in run
`tick-run-record-2026-10-05-c9d25d6a-f2bb-42bf-a162-2c4a000e804f.edn`.
The diamond witness follows `NOTE-outer-cascade-as-pasted-blends` §3 and
`ConstructionReceipt.diamondSemantics`. Singleton objects not named by a
gluing are placeholders: the run did not record their G/I₁/I₂/B readings. -/

private def tokenTheory (xs : Finset Nat) : Theory := ⟨xs, ∅⟩
private def placeholderSquare (code : Nat) : Square :=
  let T := tokenTheory {code}
  ⟨T, T, T, T, PMap.empty, PMap.empty, PMap.empty, PMap.empty, false, false⟩

def clickPolicy : Policy :=
  ⟨[placeholderSquare 1000, placeholderSquare 1001,
    placeholderSquare 1002, placeholderSquare 1003], [], []⟩

private def observeOut : Theory := tokenTheory {0, 1}
private def fillOut : Theory := tokenTheory {2, 3}
private def injuryOut : Theory := tokenTheory {4, 5}

private def observeSquare : Square :=
  ⟨tokenTheory {100}, tokenTheory {101}, tokenTheory {102}, observeOut,
    PMap.empty, PMap.empty, PMap.empty, PMap.empty, false, false⟩
private def fillSquare : Square :=
  ⟨tokenTheory {110}, observeOut, tokenTheory {111}, fillOut,
    PMap.empty, PMap.empty, PMap.empty, PMap.empty, false, false⟩
private def injurySquare : Square :=
  ⟨tokenTheory {120}, observeOut, tokenTheory {121}, injuryOut,
    PMap.empty, PMap.empty, PMap.empty, PMap.empty, false, false⟩
private def minimiseSquare : Square :=
  ⟨tokenTheory {130}, fillOut, injuryOut, tokenTheory {6},
    PMap.empty, PMap.empty, PMap.empty, PMap.empty, false, false⟩

private def identityGluing (i : Nat) (rᵢ : Role) (j : Nat) (rⱼ : Role)
    (T : Theory) : Gluing := ⟨i, rᵢ, j, rⱼ, PMap.id T⟩

private def observeFill : Gluing := identityGluing 0 .B 1 .I₁ observeOut
private def observeInjury : Gluing := identityGluing 0 .B 2 .I₁ observeOut
private def fillMinimise : Gluing := identityGluing 1 .B 3 .I₁ fillOut
private def injuryMinimise : Gluing := identityGluing 2 .B 3 .I₂ injuryOut

def diamondPolicy : Policy :=
  ⟨[observeSquare, fillSquare, injurySquare, minimiseSquare],
    [observeFill, observeInjury, fillMinimise, injuryMinimise], []⟩

def diamondPolicyDisconnectedMinimise : Policy :=
  ⟨diamondPolicy.squares, [observeFill, observeInjury], []⟩

theorem clickPolicy_is_bag : clickPolicy.verdict = .bag [[0], [1], [2], [3]] := by
  native_decide

theorem diamondPolicy_is_cascade : diamondPolicy.verdict = .cascade := by
  native_decide

theorem diamondPolicy_constructionOrder :
    diamondPolicy.constructionOrder = [(0, 1), (0, 2), (1, 3), (2, 3)] := by
  native_decide

theorem disconnectedMinimise_is_bag :
    diamondPolicyDisconnectedMinimise.verdict = .bag [[0, 1, 2], [3]] := by
  native_decide

theorem diamond_application_order_witness :
    ({diamondPolicy with applicationOrder := [(1, 2, 0)]}).verdict =
      diamondPolicy.verdict ∧
    ({diamondPolicy with applicationOrder := [(1, 2, 0)]}).constructionOrder =
      diamondPolicy.constructionOrder := by
  exact applicationOrder_independent diamondPolicy [(1, 2, 0)]

/-! ## Vertical pasting can destroy consistency

This is the partial-map witness for Goguen 1999, p. 33: two consistent
diamonds whose vertical composite is inconsistent. -/

private def pasteG : Theory := tokenTheory {0}
private def pasteI₁ : Theory := tokenTheory {1}
private def pasteI₂ : Theory := tokenTheory {2}
private def pasteB₁ : Theory := tokenTheory {3}
private def pasteJ : Theory := tokenTheory {4}
private def pasteC : Theory := tokenTheory {5, 6}

private def pasteA₁ : PMap := ⟨{(0, 1)}⟩
private def pasteA₂ : PMap := ⟨{(0, 2)}⟩
private def pasteB₁Leg : PMap := PMap.empty
private def pasteB₂ : PMap := ⟨{(2, 3)}⟩
private def pasteA₃ : PMap := ⟨{(1, 4)}⟩
private def pasteC₁ : PMap := ⟨{(4, 5)}⟩
private def pasteC₂ : PMap := ⟨{(3, 6)}⟩

def pasteDiamondOne : Square :=
  ⟨pasteG, pasteI₁, pasteI₂, pasteB₁, pasteA₁, pasteA₂,
    pasteB₁Leg, pasteB₂, false, false⟩
def pasteDiamondTwo : Square :=
  ⟨pasteI₁, pasteJ, pasteB₁, pasteC, pasteA₃, pasteB₁Leg,
    pasteC₁, pasteC₂, false, false⟩
def pasteComposite : Square :=
  ⟨pasteG, pasteJ, pasteI₂, pasteC, PMap.comp pasteA₁ pasteA₃, pasteA₂,
    pasteC₁, PMap.comp pasteB₂ pasteC₂, false, false⟩

theorem pastedDiamond_witness :
    pastedDiamond pasteDiamondOne pasteDiamondTwo = some pasteComposite := by
  native_decide

theorem diamondOne_consistent : pasteDiamondOne.cone.consistent = true := by
  native_decide

theorem diamondTwo_consistent : pasteDiamondTwo.cone.consistent = true := by
  native_decide

theorem composite_inconsistent : pasteComposite.cone.consistent = false := by
  native_decide

theorem composite_witness :
    pasteComposite.cone.inconsistencyWitness = some (0, 5, 6) := by
  native_decide

private def totalPasteB₁ : PMap := ⟨{(1, 3)}⟩
def totalB₁DiamondTwo : Square :=
  ⟨pasteI₁, pasteJ, pasteB₁, pasteC, pasteA₃, totalPasteB₁,
    pasteC₁, pasteC₂, false, false⟩

theorem totalB₁_diamondTwo_inconsistent :
    totalB₁DiamondTwo.cone.consistent = false := by
  native_decide

private def endpointBadSpan : Span :=
  ⟨pasteG, pasteI₁, pasteI₂, ⟨{(9, 1)}⟩, PMap.empty⟩
private def endpointBadCone : Cone endpointBadSpan :=
  ⟨tokenTheory {5}, ⟨{(1, 5)}⟩, PMap.empty, false, false⟩

theorem witness_none_without_wellFormed :
    ∃ (s : Span) (c : Cone s), c.inconsistencyWitness = none ∧ c.consistent = false := by
  exact ⟨endpointBadSpan, endpointBadCone, by native_decide⟩

/-! ## Proposition 8 needs commutation -/

private def prop8G : Theory := tokenTheory {0}
private def prop8I₁ : Theory := tokenTheory {1}
private def prop8I₂ : Theory := tokenTheory {2}
private def prop8B₁ : Theory := tokenTheory {3}
private def prop8J : Theory := tokenTheory {4}
private def prop8C : Theory := tokenTheory {5}

private def prop8A₁ : PMap := ⟨{(0, 1)}⟩
private def prop8B₁Leg : PMap := ⟨{(1, 3)}⟩
private def prop8C₂ : PMap := ⟨{(3, 5)}⟩

def prop8DiamondOne : Square :=
  ⟨prop8G, prop8I₁, prop8I₂, prop8B₁, prop8A₁, PMap.empty,
    prop8B₁Leg, PMap.empty, false, false⟩
def prop8DiamondTwo : Square :=
  ⟨prop8I₁, prop8J, prop8B₁, prop8C, PMap.empty, prop8B₁Leg,
    PMap.empty, prop8C₂, false, false⟩
def prop8Composite : Square :=
  ⟨prop8G, prop8J, prop8I₂, prop8C, PMap.empty, PMap.empty,
    PMap.empty, PMap.empty, false, false⟩

theorem prop8_fails_without_commutation :
    prop8DiamondOne.cone.isPushout = true ∧
    prop8DiamondTwo.cone.isPushout = true ∧
    pastedDiamond prop8DiamondOne prop8DiamondTwo = some prop8Composite ∧
    prop8Composite.cone.isPushout = false := by
  native_decide

end DarkTower.WarMachine.ThreeHalvesBlend
