import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Image
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Finset.Sort
import Mathlib.Data.List.Basic
import DarkTower.WarMachine.FiniteListGraphClosure

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

instance : Fintype Role :=
  Fintype.ofList [.G, .I₁, .I₂, .B] (by intro r; cases r <;> simp)

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

@[simp] def Square.span (q : Square) : Span := ⟨q.G, q.I₁, q.I₂, q.a₁, q.a₂⟩
@[simp] def Square.cone (q : Square) : Cone q.span :=
  ⟨q.B, q.b₁, q.b₂, q.aux₁, q.aux₂⟩

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

/-- Goguen's Proposition 8 on this carrier: vertically pasted pushouts remain
pushouts when the second square commutes on the nose and all seven constituent
maps are hom-set members. Without the last condition the second leg may be
non-functional away from the part tested by the second square. -/
theorem prop8 (d₁ d₂ d : Square)
    (hpaste : pastedDiamond d₁ d₂ = some d)
    (_hwa₁ : d₁.a₁.wellFormed d₁.G d₁.I₁ = true)
    (_hwa₂ : d₁.a₂.wellFormed d₁.G d₁.I₂ = true)
    (_hwb₁ : d₁.b₁.wellFormed d₁.I₁ d₁.B = true)
    (_hwb₂ : d₁.b₂.wellFormed d₁.I₂ d₁.B = true)
    (_hwa₃ : d₂.a₁.wellFormed d₂.G d₂.I₁ = true)
    (_hwc₁ : d₂.b₁.wellFormed d₂.I₁ d₂.B = true)
    (hwc₂ : d₂.b₂.wellFormed d₂.I₂ d₂.B = true)
    (h₁ : d₁.cone.isPushout = true) (h₂ : d₂.cone.isPushout = true)
    (hcomm₂ : d₂.commutes = true) : d.cone.isPushout = true := by
  unfold pastedDiamond at hpaste
  split at hpaste
  · rename_i hmatch
    simp only [Option.some.injEq] at hpaste
    subst d
    rcases hmatch with ⟨hG, hI₂, ha₂⟩
    simp only [Square.commutes, decide_eq_true_eq] at hcomm₂
    simp only [Cone.isPushout, Bool.and_eq_true, decide_eq_true_eq] at h₁ h₂ ⊢
    constructor
    · let base : PMap := PMap.join d₁.cone.route₁ d₁.cone.route₂
      let bound : PMap := PMap.comp base d₂.b₂
      have hbase : base.wellFormed d₁.G d₁.B = true := by
        simpa [base, Cone.consistent] using h₁.1
      have hbound : bound.wellFormed d₁.G d₂.B = true := by
        apply PMap.comp_wellFormed hbase
        simpa [hI₂] using hwc₂
      apply PMap.wellFormed_of_le (g := bound) ?_ hbound
      simp only [PMap.le, decide_eq_true_eq]
      intro p hp
      simp only [PMap.join, Finset.mem_union] at hp
      rcases hp with hp | hp
      · by_cases haux₁ : d₁.aux₁ = true
        · have : False := by
            simp [Cone.route₁, haux₁, PMap.empty] at hp
          contradiction
        · by_cases haux₃ : d₂.aux₁ = true
          · have : False := by
              simp [Cone.route₁, haux₃, PMap.empty] at hp
            contradiction
          · have hd₁a : d₁.aux₁ = false := Bool.eq_false_of_not_eq_true haux₁
            have hd₂a : d₂.aux₁ = false := Bool.eq_false_of_not_eq_true haux₃
            have heq : PMap.comp (PMap.comp d₁.a₁ d₂.a₁) d₂.b₁ =
                PMap.comp (PMap.comp d₁.a₁ d₁.b₁) d₂.b₂ := by
              rw [PMap.comp_assoc, hcomm₂, ← PMap.comp_assoc, ha₂]
            have hinner : (PMap.comp d₁.a₁ d₁.b₁).le base = true := by
              simp only [PMap.le, decide_eq_true_eq]
              intro x hx
              exact Finset.mem_union_left _ (by simpa [base, Cone.route₁, hd₁a] using hx)
            have hout := PMap.comp_monotone hinner (PMap.le_refl d₂.b₂)
            simp only [PMap.le, decide_eq_true_eq] at hout
            apply hout
            rw [← heq]
            simpa [Cone.route₁, hd₁a, hd₂a] using hp
      · by_cases haux₂ : d₁.aux₂ = true
        · have : False := by
            simp [Cone.route₂, haux₂, PMap.empty] at hp
          contradiction
        · by_cases haux₄ : d₂.aux₂ = true
          · have : False := by
              simp [Cone.route₂, haux₄, PMap.empty] at hp
            contradiction
          · have hd₁a : d₁.aux₂ = false := Bool.eq_false_of_not_eq_true haux₂
            have hd₂a : d₂.aux₂ = false := Bool.eq_false_of_not_eq_true haux₄
            have heq : PMap.comp d₁.a₂ (PMap.comp d₁.b₂ d₂.b₂) =
                PMap.comp (PMap.comp d₁.a₂ d₁.b₂) d₂.b₂ := by
              rw [← PMap.comp_assoc]
            have hinner : (PMap.comp d₁.a₂ d₁.b₂).le base = true := by
              simp only [PMap.le, decide_eq_true_eq]
              intro x hx
              exact Finset.mem_union_right _ (by simpa [base, Cone.route₂, hd₁a] using hx)
            have hout := PMap.comp_monotone hinner (PMap.le_refl d₂.b₂)
            simp only [PMap.le, decide_eq_true_eq] at hout
            apply hout
            rw [← heq]
            simpa [Cone.route₂, hd₁a, hd₂a] using hp
    · intro y hy
      have hy₂ := h₂.2 hy
      simp only [Finset.mem_union, Finset.mem_image] at hy₂ ⊢
      rcases hy₂ with ⟨jy, hjy, rfl⟩ | ⟨my, hmy, rfl⟩
      · exact Or.inl ⟨jy, hjy, rfl⟩
      · have hmB : my.1 ∈ d₁.B.elems := by
          have := (PMap.wellFormed_parts (by simpa [hI₂] using hwc₂)).1 my hmy
          exact this.1
        have hm := h₁.2 hmB
        simp only [Finset.mem_union, Finset.mem_image] at hm
        rcases hm with ⟨im, him, himy⟩ | ⟨km, hkm, hkmy⟩
        · have hroute : (im.1, my.2) ∈ (PMap.comp d₂.a₂ d₂.b₂).rel := by
            simp only [PMap.comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product]
            exact ⟨(im, my), ⟨⟨by simpa [ha₂] using him, hmy⟩, himy⟩, rfl⟩
          rw [← hcomm₂] at hroute
          simp only [PMap.comp, Finset.mem_image, Finset.mem_filter, Finset.mem_product] at hroute
          obtain ⟨w, ⟨⟨hwa, hwb⟩, _⟩, hwy⟩ := hroute
          have hwy2 : w.2.2 = my.2 := by injection hwy
          exact Or.inl ⟨w.2, hwb, hwy2⟩
        · right
          refine ⟨(km.1, my.2), ?_, rfl⟩
          apply Finset.mem_image.mpr
          exact ⟨(km, my), Finset.mem_filter.mpr
            ⟨Finset.mem_product.mpr ⟨hkm, hmy⟩, hkmy⟩, rfl⟩
  · simp at hpaste

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

/-- Indices of two composable supplied gluings and the supplied direct gluing
between the same typed endpoints.  This is additive evidence; it does not
change `Policy.wellFormed`. -/
structure GluingTriangleCertificate where
  first : Nat
  second : Nat
  direct : Nat
  deriving DecidableEq

/-- Check one explicitly supplied gluing triangle.  Besides pairwise policy
well-formedness, endpoints and roles must line up and the two-step transport
must equal the direct transport as a partial-map graph. -/
def GluingTriangleCertificate.valid (p : Policy)
    (c : GluingTriangleCertificate) : Bool :=
  match p.gluings[c.first]?, p.gluings[c.second]?, p.gluings[c.direct]? with
  | some f, some g, some d =>
      p.wellFormed &&
      decide (f.j = g.i) && decide (f.rⱼ = g.rᵢ) &&
      decide (f.i = d.i) && decide (f.rᵢ = d.rᵢ) &&
      decide (g.j = d.j) && decide (g.rⱼ = d.rⱼ) &&
      decide (PMap.comp f.iso g.iso = d.iso)
  | _, _, _ => false

/-!
This certificate checks one supplied triangle; it does not assert that the
supplied triangles cover every cycle.  Before using coherent connectivity for
pasting or a colimit claim, one additionally needs a completeness theorem that
the certificates cover a cycle basis of the admitted gluing graph, followed by
path independence derived from coherence on that basis.
-/

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

/-- Raw-input connected components in increasing order of their least square
index.  This intentionally traverses every supplied gluing, including a
malformed one, and is diagnostic data only.  `Policy.verdict` may call the
result a cascade only after `Policy.wellFormed` succeeds. -/
def Policy.components (p : Policy) : List (List Nat) :=
  (List.range p.squares.length).foldl (addComponent p.squares p.gluings) []

/-! ## Deterministic finite cycle obligations

Edges are considered in supplied order.  A well-formed edge enters the forest
iff its two typed endpoints `(square index, Role)` are not already connected
by earlier forest edges;
every other well-formed edge deterministically creates one obligation.  Thus
parallel and reversed duplicate edges are explicit non-tree obligations, not
silently deduplicated. -/

abbrev OrientedGluing := Nat × Bool -- index, reversed?

structure GluingPathInfo where
  source : Nat × Role
  target : Nat × Role
  transport : PMap
  deriving DecidableEq

private def admittedIndexedGluings (p : Policy) : List (Nat × Gluing) :=
  ((List.range p.gluings.length).zip p.gluings).filter fun ig =>
    Gluing.wellFormed p.squares ig.2

private theorem Gluing.wellFormed_endpoint_bounds {squares : List Square} {g : Gluing}
    (h : Gluing.wellFormed squares g = true) :
    g.i < squares.length ∧ g.j < squares.length := by
  unfold Gluing.wellFormed at h
  split at h <;> rename_i hi hj
  · exact ⟨(List.getElem?_eq_some_iff.mp hi).choose,
      (List.getElem?_eq_some_iff.mp hj).choose⟩
  · simp at h

private def typedEdges (p : Policy) (forest : List (Nat × Gluing)) :
    List ((Fin p.squares.length × Role) × (Fin p.squares.length × Role)) :=
  forest.filterMap fun ig =>
    if h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length then
      some ((⟨ig.2.i, h.1⟩, ig.2.rᵢ), (⟨ig.2.j, h.2⟩, ig.2.rⱼ))
    else none

private def typedEdge (p : Policy) (ig : Nat × Gluing)
    (h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    (Fin p.squares.length × Role) × (Fin p.squares.length × Role) :=
  ((⟨ig.2.i, h.1⟩, ig.2.rᵢ), (⟨ig.2.j, h.2⟩, ig.2.rⱼ))

theorem typedEdge_proof_irrel (p : Policy) (ig : Nat × Gluing)
    (h₁ h₂ : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    typedEdge p ig h₁ = typedEdge p ig h₂ := by
  rfl

private def typedEndpointKey? (p : Policy) (ig : Nat × Gluing) :
    Option (Sym2 (Fin p.squares.length × Role)) :=
  if h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length then
    some s((typedEdge p ig h).1, (typedEdge p ig h).2)
  else none

private theorem edgeKeys_typedEdges (p : Policy) (xs : List (Nat × Gluing)) :
    FiniteListGraphClosure.edgeKeys (typedEdges p xs) =
      xs.filterMap (typedEndpointKey? p) := by
  induction xs with
  | nil => simp [FiniteListGraphClosure.edgeKeys, typedEdges]
  | cons ig xs ih =>
      by_cases h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length
      · simp [typedEdges, FiniteListGraphClosure.edgeKeys, typedEndpointKey?, h,
          typedEdge]
        exact ih
      · simp [typedEdges, FiniteListGraphClosure.edgeKeys, typedEndpointKey?, h]
        exact ih

private theorem filterMap_nodup_source_unique {α β : Type*}
    {f : α → Option β} {xs : List α} {a b : α} {y : β}
    (hn : (xs.filterMap f).Nodup) (ha : a ∈ xs) (hb : b ∈ xs)
    (hfa : f a = some y) (hfb : f b = some y) : a = b := by
  induction xs generalizing a b with
  | nil => simp at ha
  | cons x xs ih =>
      simp only [List.mem_cons] at ha hb
      rcases ha with rfl | ha <;> rcases hb with rfl | hb
      · rfl
      · simp only [List.filterMap_cons, hfa] at hn
        exact (((List.pairwise_cons.mp hn).1 _
          (List.mem_filterMap.mpr ⟨b, hb, hfb⟩)) rfl).elim
      · simp only [List.filterMap_cons, hfb] at hn
        exact (((List.pairwise_cons.mp hn).1 _
          (List.mem_filterMap.mpr ⟨a, ha, hfa⟩)) rfl).elim
      · apply ih
        · cases hfx : f x with
          | none => simpa [List.filterMap_cons, hfx] using hn
          | some z =>
              rw [List.filterMap_cons, hfx] at hn
              exact hn.of_cons
        · exact ha
        · exact hb
        · exact hfa
        · exact hfb

private theorem typedEdges_singleton (p : Policy) (ig : Nat × Gluing)
    (h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    typedEdges p [ig] = [typedEdge p ig h] := by
  simp [typedEdges, typedEdge, h]

private theorem typedEdges_cons (p : Policy) (ig : Nat × Gluing)
    (xs : List (Nat × Gluing))
    (h : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    typedEdges p (ig :: xs) = typedEdge p ig h :: typedEdges p xs := by
  simp [typedEdges, typedEdge, h]

private theorem typedEdges_append (p : Policy) (xs ys : List (Nat × Gluing)) :
    typedEdges p (xs ++ ys) = typedEdges p xs ++ typedEdges p ys := by
  exact List.filterMap_append

def Policy.typedComponentFin (p : Policy) (forest : List (Nat × Gluing))
    (v : Fin p.squares.length × Role) : Finset (Fin p.squares.length × Role) :=
  FiniteListGraphClosure.close (typedEdges p forest)
    (Fintype.card (Fin p.squares.length × Role)) {v}

def Policy.typedComponent (p : Policy) (forest : List (Nat × Gluing))
    (v : Nat × Role) : Finset (Nat × Role) :=
  if h : v.1 < p.squares.length then
    (p.typedComponentFin forest (⟨v.1, h⟩, v.2)).image
      (fun x => (x.1.val, x.2))
  else {v}

theorem Policy.mem_typedComponentFin_iff_reachable (p : Policy)
    (forest : List (Nat × Gluing))
    (u v : Fin p.squares.length × Role) :
    v ∈ p.typedComponentFin forest u ↔
      (FiniteListGraphClosure.graph (typedEdges p forest)).Reachable u v := by
  unfold Policy.typedComponentFin
  simpa using FiniteListGraphClosure.mem_close_card_iff_reachable
    (typedEdges p forest) u v

theorem Policy.mem_typedComponent_iff_reachable (p : Policy)
    (forest : List (Nat × Gluing)) (u v : Nat × Role)
    (hu : u.1 < p.squares.length) (hv : v.1 < p.squares.length) :
    v ∈ p.typedComponent forest u ↔
      (FiniteListGraphClosure.graph (typedEdges p forest)).Reachable
        (⟨u.1, hu⟩, u.2) (⟨v.1, hv⟩, v.2) := by
  rw [Policy.typedComponent]
  simp only [dif_pos hu, Finset.mem_image]
  constructor
  · rintro ⟨x, hx, hval⟩
    have heq : x = (⟨v.1, hv⟩, v.2) := by
      apply Prod.ext
      · apply Fin.ext
        exact congrArg (fun z : Nat × Role => z.1) hval
      · exact congrArg (fun z : Nat × Role => z.2) hval
    subst x
    exact (p.mem_typedComponentFin_iff_reachable forest _ _).mp hx
  · intro hr
    refine ⟨(⟨v.1, hv⟩, v.2), ?_, rfl⟩
    exact (p.mem_typedComponentFin_iff_reachable forest _ _).mpr hr

private def forestStep (p : Policy) (forest : List (Nat × Gluing))
    (ig : Nat × Gluing) : List (Nat × Gluing) :=
  if (ig.2.j, ig.2.rⱼ) ∈ p.typedComponent forest (ig.2.i, ig.2.rᵢ) then forest
  else forest ++ [ig]

private theorem typedEdges_forestStep (p : Policy) (forest : List (Nat × Gluing))
    (ig : Nat × Gluing) (hig : Gluing.wellFormed p.squares ig.2 = true) :
    typedEdges p (forestStep p forest ig) =
      FiniteListGraphClosure.forestStep (typedEdges p forest)
        (typedEdge p ig (Gluing.wellFormed_endpoint_bounds hig)) := by
  classical
  have hb := Gluing.wellFormed_endpoint_bounds hig
  have hmem := p.mem_typedComponent_iff_reachable forest
    (ig.2.i, ig.2.rᵢ) (ig.2.j, ig.2.rⱼ) hb.1 hb.2
  unfold forestStep FiniteListGraphClosure.forestStep
  by_cases hr : (FiniteListGraphClosure.graph (typedEdges p forest)).Reachable
      (⟨ig.2.i, hb.1⟩, ig.2.rᵢ) (⟨ig.2.j, hb.2⟩, ig.2.rⱼ)
  · simp only [if_pos (hmem.mpr hr)]
    simp [typedEdge, hr]
  · simp only [if_neg (fun hm => hr (hmem.mp hm)), typedEdges_append]
    rw [typedEdges_singleton p ig hb]
    simp [typedEdge, hr]

private def Policy.indexedGluingForest (p : Policy) : List (Nat × Gluing) :=
  (admittedIndexedGluings p).foldl (forestStep p) []

private theorem foldl_forestStep_sublist (p : Policy) (xs : List (Nat × Gluing)) :
    (xs.foldl (forestStep p) []).Sublist xs := by
  induction xs using List.reverseRecOn with
  | nil => simp
  | append_singleton xs ig ih =>
      rw [List.foldl_append]
      simp only [List.foldl]
      unfold forestStep
      split
      · exact ih.trans (List.sublist_append_left xs [ig])
      · exact ih.append (List.Sublist.refl [ig])

private theorem admittedIndexedGluings_indices_nodup (p : Policy) :
    ((admittedIndexedGluings p).map Prod.fst).Nodup := by
  unfold admittedIndexedGluings
  have hz : ((((List.range p.gluings.length).zip p.gluings).map Prod.fst)).Nodup := by
    rw [List.map_fst_zip (by simp)]
    exact List.nodup_range
  exact ((List.filter_sublist (p := fun ig : Nat × Gluing =>
    Gluing.wellFormed p.squares ig.2)).map Prod.fst).nodup hz

theorem Policy.indexedGluingForest_indices_nodup (p : Policy) :
    (p.indexedGluingForest.map Prod.fst).Nodup := by
  exact ((foldl_forestStep_sublist p (admittedIndexedGluings p)).map Prod.fst).nodup
    (admittedIndexedGluings_indices_nodup p)

theorem Policy.indexedGluingForest_index_unique (p : Policy)
    {a b : Nat × Gluing} (ha : a ∈ p.indexedGluingForest)
    (hb : b ∈ p.indexedGluingForest) (hindex : a.1 = b.1) : a = b := by
  have hn := p.indexedGluingForest_indices_nodup
  have hd : p.indexedGluingForest.Nodup := hn.of_map Prod.fst
  exact (List.nodup_map_iff_inj_on hd).mp hn a ha b hb hindex

private theorem typedEdges_foldl_forestStep (p : Policy)
    (xs acc : List (Nat × Gluing))
    (hxs : ∀ ig ∈ xs, Gluing.wellFormed p.squares ig.2 = true) :
    typedEdges p (xs.foldl (forestStep p) acc) =
      (typedEdges p xs).foldl FiniteListGraphClosure.forestStep (typedEdges p acc) := by
  induction xs generalizing acc with
  | nil => simp [typedEdges]
  | cons ig xs ih =>
      have hig : Gluing.wellFormed p.squares ig.2 = true := hxs ig (by simp)
      have hrest : ∀ x ∈ xs, Gluing.wellFormed p.squares x.2 = true :=
        fun x hx => hxs x (by simp [hx])
      simp only [List.foldl_cons]
      rw [ih (forestStep p acc ig) hrest, typedEdges_forestStep p acc ig hig,
        typedEdges_cons p ig xs (Gluing.wellFormed_endpoint_bounds hig), List.foldl_cons]

private theorem admittedIndexedGluings_wellFormed (p : Policy) :
    ∀ ig ∈ admittedIndexedGluings p,
      Gluing.wellFormed p.squares ig.2 = true := by
  intro ig hig
  exact (List.mem_filter.mp hig).2

theorem Policy.typedEdges_indexedGluingForest (p : Policy) :
    typedEdges p p.indexedGluingForest =
      FiniteListGraphClosure.greedyForest (typedEdges p (admittedIndexedGluings p)) := by
  rw [Policy.indexedGluingForest,
    typedEdges_foldl_forestStep p (admittedIndexedGluings p) []
      (admittedIndexedGluings_wellFormed p)]
  rfl

theorem Policy.indexedGluingForest_typedEndpointKeys_nodup (p : Policy) :
    (FiniteListGraphClosure.edgeKeys
      (typedEdges p p.indexedGluingForest)).Nodup := by
  rw [p.typedEdges_indexedGluingForest]
  exact FiniteListGraphClosure.greedyForest_edgeKeys_nodup _

/-- The graph represented by the executable indexed forest. -/
def Policy.typedGluingForestGraph (p : Policy) :
    SimpleGraph (Fin p.squares.length × Role) :=
  FiniteListGraphClosure.graph (typedEdges p p.indexedGluingForest)

/-- The graph of every supplied, individually well-formed typed gluing. -/
def Policy.admittedTypedGluingGraph (p : Policy) :
    SimpleGraph (Fin p.squares.length × Role) :=
  FiniteListGraphClosure.graph (typedEdges p (admittedIndexedGluings p))

theorem Policy.typedGluingForestGraph_isAcyclic (p : Policy) :
    p.typedGluingForestGraph.IsAcyclic := by
  rw [Policy.typedGluingForestGraph, p.typedEdges_indexedGluingForest]
  exact FiniteListGraphClosure.greedyForest_isAcyclic _

theorem Policy.typedGluingForestGraph_reachable_iff (p : Policy)
    (u v : Fin p.squares.length × Role) :
    p.typedGluingForestGraph.Reachable u v ↔
      p.admittedTypedGluingGraph.Reachable u v := by
  rw [Policy.typedGluingForestGraph, Policy.admittedTypedGluingGraph,
    p.typedEdges_indexedGluingForest]
  exact FiniteListGraphClosure.greedyForest_reachable_iff _ _ _

/-- Admitted typed connectivity is represented by a (possibly nil) simple
path in the deterministic forest.  In particular, the reflexive `u = v`
case does not require a nonempty edge path. -/
theorem Policy.admittedTyped_reachable_iff_nonempty_forestPath (p : Policy)
    (u v : Fin p.squares.length × Role) :
    p.admittedTypedGluingGraph.Reachable u v ↔
      Nonempty (p.typedGluingForestGraph.Path u v) := by
  constructor
  · intro h
    have hf : p.typedGluingForestGraph.Reachable u v :=
      (p.typedGluingForestGraph_reachable_iff u v).mpr h
    obtain ⟨w, hw⟩ := hf.exists_isPath
    exact ⟨⟨w, hw⟩⟩
  · rintro ⟨q⟩
    exact (p.typedGluingForestGraph_reachable_iff u v).mp q.1.reachable

theorem Policy.exists_typedGluingForest_path (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.admittedTypedGluingGraph.Reachable u v) :
    ∃ w : p.typedGluingForestGraph.Walk u v, w.IsPath := by
  obtain ⟨q⟩ := (p.admittedTyped_reachable_iff_nonempty_forestPath u v).mp h
  exact ⟨q.1, q.2⟩

theorem Policy.typedGluingForest_path_unique (p : Policy)
    {u v : Fin p.squares.length × Role}
    (q₁ q₂ : p.typedGluingForestGraph.Path u v) : q₁ = q₂ :=
  p.typedGluingForestGraph_isAcyclic.path_unique q₁ q₂

/-- Choice is used only to package the unique mathematical path; this
definition makes no claim of executable path extraction. -/
noncomputable def Policy.canonicalTypedGluingForestPath (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.admittedTypedGluingGraph.Reachable u v) :
    p.typedGluingForestGraph.Path u v :=
  Classical.choice ((p.admittedTyped_reachable_iff_nonempty_forestPath u v).mp h)

theorem Policy.canonicalTypedGluingForestPath_unique (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.admittedTypedGluingGraph.Reachable u v)
    (q : p.typedGluingForestGraph.Path u v) :
    p.canonicalTypedGluingForestPath h = q :=
  p.typedGluingForest_path_unique _ _

theorem Policy.canonicalTypedGluingForestPath_self (p : Policy)
    (u : Fin p.squares.length × Role) :
    p.canonicalTypedGluingForestPath (SimpleGraph.Reachable.refl u) =
      SimpleGraph.Path.nil := by
  apply p.typedGluingForest_path_unique

def Policy.gluingForest (p : Policy) : List Nat :=
  p.indexedGluingForest.map Prod.fst

private theorem mem_foldl_forestStep (p : Policy) (xs acc : List (Nat × Gluing))
    (x : Nat × Gluing) (h : x ∈ xs.foldl (forestStep p) acc) :
    x ∈ acc ∨ x ∈ xs := by
  induction xs generalizing acc with
  | nil => simpa using h
  | cons a xs ih =>
      have hx := ih (forestStep p acc a) h
      rcases hx with hx | hx
      · unfold forestStep at hx
        split at hx
        · exact Or.inl hx
        · have hmem : x ∈ acc ∨ x = a := by simpa using hx
          rcases hmem with hacc | rfl
          · exact Or.inl hacc
          · exact Or.inr (by simp)
      · exact Or.inr (by simp [hx])

theorem Policy.indexedGluingForest_member_wellFormed (p : Policy)
    {ig : Nat × Gluing} (hig : ig ∈ p.indexedGluingForest) :
    Gluing.wellFormed p.squares ig.2 = true := by
  have hi := mem_foldl_forestStep p (admittedIndexedGluings p) [] ig hig
  simp only [List.not_mem_nil, false_or] at hi
  exact (List.mem_filter.mp hi).2

theorem Policy.indexedGluingForest_member_original (p : Policy)
    {ig : Nat × Gluing} (hig : ig ∈ p.indexedGluingForest) :
    ig ∈ (List.range p.gluings.length).zip p.gluings := by
  have hi := mem_foldl_forestStep p (admittedIndexedGluings p) [] ig hig
  simp only [List.not_mem_nil, false_or] at hi
  exact (List.mem_filter.mp hi).1

private theorem range_zip_member_getElem? {α : Type*} {xs : List α}
    {i : Nat} {x : α} (h : (i, x) ∈ (List.range xs.length).zip xs) :
    xs[i]? = some x := by
  obtain ⟨n, hn, hget⟩ := List.mem_iff_getElem.mp h
  have hnRange : n < (List.range xs.length).length := by
    simpa [List.length_zip] using hn
  have hnXs : n < xs.length := by simpa using hnRange
  rw [List.getElem_zip] at hget
  have hi : n = i := by
    simpa using congrArg Prod.fst hget
  have hx : xs[n] = x := by
    simpa using congrArg Prod.snd hget
  subst i
  exact List.getElem?_eq_some_iff.mpr ⟨hnXs, hx⟩

theorem Policy.indexedGluingForest_member_lookup (p : Policy)
    {ig : Nat × Gluing} (hig : ig ∈ p.indexedGluingForest) :
    p.gluings[ig.1]? = some ig.2 :=
  range_zip_member_getElem? (p.indexedGluingForest_member_original hig)

theorem Policy.indexedGluingForest_member_emits_typedEdge (p : Policy)
    {ig : Nat × Gluing} (hig : ig ∈ p.indexedGluingForest) :
    let hb := Gluing.wellFormed_endpoint_bounds
      (p.indexedGluingForest_member_wellFormed hig)
    typedEdge p ig hb ∈ typedEdges p p.indexedGluingForest := by
  dsimp
  apply List.mem_filterMap.mpr
  refine ⟨ig, hig, ?_⟩
  simp [Gluing.wellFormed_endpoint_bounds,
    p.indexedGluingForest_member_wellFormed hig, typedEdge]

theorem Policy.mem_typedEdges_indexedGluingForest_iff (p : Policy)
    {e : (Fin p.squares.length × Role) × (Fin p.squares.length × Role)} :
    e ∈ typedEdges p p.indexedGluingForest ↔
      ∃ ig ∈ p.indexedGluingForest,
        ∃ hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length,
          e = typedEdge p ig hb := by
  constructor
  · intro he
    obtain ⟨ig, hig, hem⟩ := List.mem_filterMap.mp he
    split at hem <;> rename_i hb
    · exact ⟨ig, hig, hb, Option.some.inj hem.symm⟩
    · simp at hem
  · rintro ⟨ig, hig, hb, rfl⟩
    exact p.indexedGluingForest_member_emits_typedEdge hig

theorem Policy.indexedGluingForest_typedEndpointKey_unique (p : Policy)
    {a b : Nat × Gluing} (ha : a ∈ p.indexedGluingForest)
    (hb : b ∈ p.indexedGluingForest)
    (haBound : a.2.i < p.squares.length ∧ a.2.j < p.squares.length)
    (hbBound : b.2.i < p.squares.length ∧ b.2.j < p.squares.length)
    (hkey : s((typedEdge p a haBound).1, (typedEdge p a haBound).2) =
      s((typedEdge p b hbBound).1, (typedEdge p b hbBound).2)) : a = b := by
  apply filterMap_nodup_source_unique
    (f := typedEndpointKey? p)
    (y := s((typedEdge p a haBound).1, (typedEdge p a haBound).2))
  · rw [← edgeKeys_typedEdges]
    exact p.indexedGluingForest_typedEndpointKeys_nodup
  · exact ha
  · exact hb
  · simp [typedEndpointKey?, haBound, typedEdge]
  · rw [typedEndpointKey?]
    simp only [dif_pos hbBound]
    exact congrArg some hkey.symm

def orientedTypedEndpoints (p : Policy) (ig : Nat × Gluing)
    (hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length)
    (reversed : Bool) :
    (Fin p.squares.length × Role) × (Fin p.squares.length × Role) :=
  if reversed then ((typedEdge p ig hb).2, (typedEdge p ig hb).1)
  else typedEdge p ig hb

theorem orientedTypedEndpoints_forward (p : Policy) (ig : Nat × Gluing)
    (hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    orientedTypedEndpoints p ig hb false = typedEdge p ig hb := by rfl

theorem orientedTypedEndpoints_reverse (p : Policy) (ig : Nat × Gluing)
    (hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length) :
    orientedTypedEndpoints p ig hb true =
      ((typedEdge p ig hb).2, (typedEdge p ig hb).1) := by rfl

structure OrientedForestAdjacencyWitness (p : Policy)
    (u v : Fin p.squares.length × Role) where
  ig : Nat × Gluing
  member : ig ∈ p.indexedGluingForest
  bounds : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length
  reversed : Bool
  endpoints : orientedTypedEndpoints p ig bounds reversed = (u, v)

theorem Policy.exists_orientedForestAdjacencyWitness (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.typedGluingForestGraph.Adj u v) :
    Nonempty (OrientedForestAdjacencyWitness p u v) := by
  change (FiniteListGraphClosure.graph
    (typedEdges p p.indexedGluingForest)).Adj u v at h
  rw [FiniteListGraphClosure.graph, SimpleGraph.fromRel_adj] at h
  rcases h with ⟨_, huv | hvu⟩
  · obtain ⟨ig, hig, hb, he⟩ :=
      p.mem_typedEdges_indexedGluingForest_iff.mp huv
    exact ⟨⟨ig, hig, hb, false, by
      change typedEdge p ig hb = (u, v)
      exact he.symm⟩⟩
  · obtain ⟨ig, hig, hb, he⟩ :=
      p.mem_typedEdges_indexedGluingForest_iff.mp hvu
    exact ⟨⟨ig, hig, hb, true, by
      change ((typedEdge p ig hb).2, (typedEdge p ig hb).1) = (u, v)
      exact congrArg Prod.swap he.symm⟩⟩

theorem Policy.orientedForestAdjacencyWitness_unique (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.typedGluingForestGraph.Adj u v)
    (a b : OrientedForestAdjacencyWitness p u v) :
    a.ig = b.ig ∧ a.reversed = b.reversed := by
  rcases a with ⟨a, ha, haBound, ar, hae⟩
  rcases b with ⟨b, hb, hbBound, br, hbe⟩
  change a = b ∧ ar = br
  have hkey : s((typedEdge p a haBound).1, (typedEdge p a haBound).2) =
      s((typedEdge p b hbBound).1, (typedEdge p b hbBound).2) := by
    have hka' : s((typedEdge p a haBound).1, (typedEdge p a haBound).2) =
        s(u, v) := by
      cases har : ar
      · have ea : typedEdge p a haBound = (u, v) := by
          simpa [orientedTypedEndpoints, har] using hae
        exact congrArg (fun e => s(e.1, e.2)) ea
      · have ea : ((typedEdge p a haBound).2, (typedEdge p a haBound).1) =
            (u, v) := by simpa [orientedTypedEndpoints, har] using hae
        simpa only [Sym2.eq_swap] using congrArg (fun e => s(e.1, e.2)) ea
    have hkb' : s((typedEdge p b hbBound).1, (typedEdge p b hbBound).2) =
        s(u, v) := by
      cases hbr : br
      · have eb : typedEdge p b hbBound = (u, v) := by
          simpa [orientedTypedEndpoints, hbr] using hbe
        exact congrArg (fun e => s(e.1, e.2)) eb
      · have eb : ((typedEdge p b hbBound).2, (typedEdge p b hbBound).1) =
            (u, v) := by simpa [orientedTypedEndpoints, hbr] using hbe
        simpa only [Sym2.eq_swap] using congrArg (fun e => s(e.1, e.2)) eb
    exact hka'.trans hkb'.symm
  have hig := p.indexedGluingForest_typedEndpointKey_unique
    ha hb haBound hbBound hkey
  constructor
  · exact hig
  subst b
  cases har : ar <;> cases hbr : br <;> simp [har, hbr]
  · simp [orientedTypedEndpoints, har, hbr] at hae hbe
    have huv : u = v := by
      calc
        u = (typedEdge p a haBound).1 := by simpa using congrArg Prod.fst hae.symm
        _ = (typedEdge p a hbBound).1 := by rw [typedEdge_proof_irrel p a haBound hbBound]
        _ = v := hbe.2
    exact (h.ne huv).elim
  · simp [orientedTypedEndpoints, har, hbr] at hae hbe
    have huv : u = v := by
      calc
        u = (typedEdge p a hbBound).2 := hae.1.symm
        _ = (typedEdge p a haBound).2 := by rw [typedEdge_proof_irrel p a hbBound haBound]
        _ = v := by simpa using congrArg Prod.snd hbe
    exact (h.ne huv).elim

noncomputable def Policy.orientedForestAdjacencyWitness (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.typedGluingForestGraph.Adj u v) :
    OrientedForestAdjacencyWitness p u v :=
  Classical.choice (p.exists_orientedForestAdjacencyWitness h)

theorem Policy.orientedForestAdjacencyWitness_spec_unique (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.typedGluingForestGraph.Adj u v)
    (w : OrientedForestAdjacencyWitness p u v) :
    (p.orientedForestAdjacencyWitness h).ig = w.ig ∧
      (p.orientedForestAdjacencyWitness h).reversed = w.reversed :=
  p.orientedForestAdjacencyWitness_unique h _ w

/-- Every selected typed-forest edge is an actually supplied, individually
well-formed gluing; forest construction cannot mint an edge. -/
theorem Policy.gluingForest_edge_admitted (p : Policy) {k : Nat}
    (hk : k ∈ p.gluingForest) :
    ∃ g, (k, g) ∈ (List.range p.gluings.length).zip p.gluings ∧
      Gluing.wellFormed p.squares g = true := by
  simp only [Policy.gluingForest, List.mem_map] at hk
  obtain ⟨ig, hig, rfl⟩ := hk
  have hi := mem_foldl_forestStep p (admittedIndexedGluings p) [] ig hig
  simp only [List.not_mem_nil, false_or] at hi
  simp only [admittedIndexedGluings, List.mem_filter] at hi
  exact ⟨ig.2, hi.1, hi.2⟩

def Policy.requiredCycleEdges (p : Policy) : List Nat :=
  (admittedIndexedGluings p).filterMap fun ig =>
    if ig.1 ∈ p.gluingForest then none else some ig.1

private def reversePMap (f : PMap) : PMap :=
  ⟨f.rel.image Prod.swap⟩

def Policy.orientedGluing (p : Policy) (step : OrientedGluing) :
    Option GluingPathInfo :=
  match p.gluings[step.1]? with
  | none => none
  | some g =>
      if step.2 then some ⟨(g.j, g.rⱼ), (g.i, g.rᵢ), reversePMap g.iso⟩
      else some ⟨(g.i, g.rᵢ), (g.j, g.rⱼ), g.iso⟩

theorem Policy.orientedGluing_of_forestAdjacencyWitness (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : OrientedForestAdjacencyWitness p u v) :
    ∃ info,
      p.orientedGluing (w.ig.1, w.reversed) = some info ∧
      info.source = (u.1.val, u.2) ∧ info.target = (v.1.val, v.2) := by
  have hl := p.indexedGluingForest_member_lookup w.member
  cases hr : w.reversed
  · let info : GluingPathInfo :=
      ⟨(w.ig.2.i, w.ig.2.rᵢ), (w.ig.2.j, w.ig.2.rⱼ), w.ig.2.iso⟩
    refine ⟨info, ?_, ?_, ?_⟩
    · simp [Policy.orientedGluing, hl, hr, info]
    · change (w.ig.2.i, w.ig.2.rᵢ) = (u.1.val, u.2)
      simpa [orientedTypedEndpoints, hr, typedEdge] using
        congrArg (fun z => (z.1.1.val, z.1.2)) w.endpoints
    · change (w.ig.2.j, w.ig.2.rⱼ) = (v.1.val, v.2)
      simpa [orientedTypedEndpoints, hr, typedEdge] using
        congrArg (fun z => (z.2.1.val, z.2.2)) w.endpoints
  · let info : GluingPathInfo :=
      ⟨(w.ig.2.j, w.ig.2.rⱼ), (w.ig.2.i, w.ig.2.rᵢ), reversePMap w.ig.2.iso⟩
    refine ⟨info, ?_, ?_, ?_⟩
    · simp [Policy.orientedGluing, hl, hr, info]
    · change (w.ig.2.j, w.ig.2.rⱼ) = (u.1.val, u.2)
      simpa [orientedTypedEndpoints, hr, typedEdge] using
        congrArg (fun z => (z.1.1.val, z.1.2)) w.endpoints
    · change (w.ig.2.i, w.ig.2.rᵢ) = (v.1.val, v.2)
      simpa [orientedTypedEndpoints, hr, typedEdge] using
        congrArg (fun z => (z.2.1.val, z.2.2)) w.endpoints

structure OrientedForestStepWitness (p : Policy) (step : OrientedGluing) where
  ig : Nat × Gluing
  member : ig ∈ p.indexedGluingForest
  index_eq : ig.1 = step.1
  bounds : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length
  endpoints_ne : (orientedTypedEndpoints p ig bounds step.2).1 ≠
    (orientedTypedEndpoints p ig bounds step.2).2

def OrientedForestStepWitness.source {p : Policy} {step : OrientedGluing}
    (w : OrientedForestStepWitness p step) : Fin p.squares.length × Role :=
  (orientedTypedEndpoints p w.ig w.bounds step.2).1

def OrientedForestStepWitness.target {p : Policy} {step : OrientedGluing}
    (w : OrientedForestStepWitness p step) : Fin p.squares.length × Role :=
  (orientedTypedEndpoints p w.ig w.bounds step.2).2

theorem Policy.gluingForest_member_has_unique_entry (p : Policy) {k : Nat}
    (hk : k ∈ p.gluingForest) :
    ∃! ig : Nat × Gluing,
      ig ∈ p.indexedGluingForest ∧ ig.1 = k ∧
      p.gluings[ig.1]? = some ig.2 ∧
      Gluing.wellFormed p.squares ig.2 = true ∧
      ∃ hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length,
        typedEdge p ig hb ∈ typedEdges p p.indexedGluingForest := by
  unfold Policy.gluingForest at hk
  obtain ⟨ig, hig, hik⟩ := List.mem_map.mp hk
  have hwf := p.indexedGluingForest_member_wellFormed hig
  have hb := Gluing.wellFormed_endpoint_bounds hwf
  refine ⟨ig, ⟨hig, hik, p.indexedGluingForest_member_lookup hig, hwf,
    hb, p.indexedGluingForest_member_emits_typedEdge hig⟩, ?_⟩
  intro other ho
  exact p.indexedGluingForest_index_unique ho.1 hig (ho.2.1.trans hik.symm)

noncomputable def Policy.orientedForestStepWitness (p : Policy) (step : OrientedGluing)
    (hk : step.1 ∈ p.gluingForest) : OrientedForestStepWitness p step := by
  let hex := (p.gluingForest_member_has_unique_entry hk).exists
  let ig := Classical.choose hex
  have hdata := Classical.choose_spec hex
  have hig := hdata.1
  have hik := hdata.2.1
  have hwf := hdata.2.2.2.1
  let hb := Gluing.wellFormed_endpoint_bounds hwf
  have hem := p.indexedGluingForest_member_emits_typedEdge hig
  have hne := FiniteListGraphClosure.greedyForest_edge_ne
    (typedEdges p (admittedIndexedGluings p))
    (show typedEdge p ig hb ∈
      FiniteListGraphClosure.greedyForest
        (typedEdges p (admittedIndexedGluings p)) by
      rw [← p.typedEdges_indexedGluingForest]
      exact hem)
  refine ⟨ig, hig, hik, hb, ?_⟩
  cases hr : step.2
  · simpa [orientedTypedEndpoints, hr] using hne
  · simpa [orientedTypedEndpoints, hr] using hne.symm

theorem OrientedForestStepWitness.adj
    {p : Policy} {step : OrientedGluing}
    (w : OrientedForestStepWitness p step) :
    p.typedGluingForestGraph.Adj w.source w.target := by
  change (FiniteListGraphClosure.graph
    (typedEdges p p.indexedGluingForest)).Adj w.source w.target
  rw [FiniteListGraphClosure.graph, SimpleGraph.fromRel_adj]
  refine ⟨w.endpoints_ne, ?_⟩
  have hem := p.indexedGluingForest_member_emits_typedEdge w.member
  cases hr : step.2
  · exact Or.inl (by simpa [OrientedForestStepWitness.source,
      OrientedForestStepWitness.target, orientedTypedEndpoints, hr] using hem)
  · exact Or.inr (by simpa [OrientedForestStepWitness.source,
      OrientedForestStepWitness.target, orientedTypedEndpoints, hr] using hem)

theorem OrientedForestStepWitness.orientedGluing_info
    {p : Policy} {step : OrientedGluing}
    (w : OrientedForestStepWitness p step) :
    ∃ info, p.orientedGluing step = some info ∧
      info.source = (w.source.1.val, w.source.2) ∧
      info.target = (w.target.1.val, w.target.2) := by
  let a : OrientedForestAdjacencyWitness p w.source w.target :=
    ⟨w.ig, w.member, w.bounds, step.2, rfl⟩
  obtain ⟨info, hi, hs, ht⟩ := p.orientedGluing_of_forestAdjacencyWitness a
  have hstep : (w.ig.1, step.2) = step := by
    apply Prod.ext
    · exact w.index_eq
    · rfl
  exact ⟨info, hstep ▸ hi, hs, ht⟩

theorem OrientedForestStepWitness.unique_of_endpoints
    {p : Policy} {step step' : OrientedGluing}
    (w : OrientedForestStepWitness p step)
    (w' : OrientedForestStepWitness p step')
    (hs : w.source = w'.source) (ht : w.target = w'.target) :
    w.ig = w'.ig ∧ step.2 = step'.2 := by
  let a : OrientedForestAdjacencyWitness p w.source w.target :=
    ⟨w.ig, w.member, w.bounds, step.2, rfl⟩
  let b : OrientedForestAdjacencyWitness p w.source w.target :=
    ⟨w'.ig, w'.member, w'.bounds, step'.2, by
      exact Prod.ext hs.symm ht.symm⟩
  exact p.orientedForestAdjacencyWitness_unique w.adj a b

noncomputable def Policy.orientedStepsOfWalk (p : Policy) :
    {u v : Fin p.squares.length × Role} →
      p.typedGluingForestGraph.Walk u v → List OrientedGluing
  | _, _, .nil => []
  | _, _, .cons h rest =>
      let w := p.orientedForestAdjacencyWitness h
      (w.ig.1, w.reversed) :: p.orientedStepsOfWalk rest

noncomputable def Policy.orientedStepsOfPath (p : Policy)
    {u v : Fin p.squares.length × Role}
    (q : p.typedGluingForestGraph.Path u v) : List OrientedGluing :=
  p.orientedStepsOfWalk q.1

theorem Policy.orientedStepsOfWalk_length (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v) :
    (p.orientedStepsOfWalk w).length = w.length := by
  induction w with
  | nil => rfl
  | cons h rest ih => simp [Policy.orientedStepsOfWalk, ih]

theorem Policy.orientedStepsOfPath_length (p : Policy)
    {u v : Fin p.squares.length × Role}
    (q : p.typedGluingForestGraph.Path u v) :
    (p.orientedStepsOfPath q).length = q.1.length :=
  p.orientedStepsOfWalk_length q.1

def Policy.gluingPathInfo (p : Policy) : List OrientedGluing → Option GluingPathInfo
  | [] => none
  | [step] => p.orientedGluing step
  | step :: rest =>
      match p.orientedGluing step, p.gluingPathInfo rest with
      | some first, some tail =>
          if first.target = tail.source then
            some ⟨first.source, tail.target, PMap.comp first.transport tail.transport⟩
          else none
      | _, _ => none

structure OrientedStepsWalkResult (p : Policy)
    (steps : List OrientedGluing) (info : GluingPathInfo) where
  source : Fin p.squares.length × Role
  target : Fin p.squares.length × Role
  walk : p.typedGluingForestGraph.Walk source target
  source_eq : (source.1.val, source.2) = info.source
  target_eq : (target.1.val, target.2) = info.target
  steps_eq : p.orientedStepsOfWalk walk = steps
  length_eq : walk.length = steps.length

theorem Policy.gluingPathInfo_nil (p : Policy) :
    p.gluingPathInfo [] = none := rfl

noncomputable def Policy.walkOfComposableOrientedSteps (p : Policy)
    (steps : List OrientedGluing) (info : GluingPathInfo)
    (hne : steps ≠ [])
    (hall : ∀ step ∈ steps, step.1 ∈ p.gluingForest)
    (hinfo : p.gluingPathInfo steps = some info) :
    OrientedStepsWalkResult p steps info := by
  induction steps generalizing info with
  | nil => exact (hne rfl).elim
  | cons step rest ih =>
      let sw := p.orientedForestStepWitness step (hall step (by simp))
      let hex := sw.orientedGluing_info
      let first := Classical.choose hex
      have hfirstData := Classical.choose_spec hex
      have hfirst := hfirstData.1
      have hfirstSource := hfirstData.2.1
      have hfirstTarget := hfirstData.2.2
      cases rest with
      | nil =>
          have heq : first = info := by
            change p.orientedGluing step = some info at hinfo
            exact Option.some.inj (hfirst.symm.trans hinfo)
          subst info
          let walk : p.typedGluingForestGraph.Walk sw.source sw.target :=
            .cons sw.adj .nil
          have hencoded : p.orientedStepsOfWalk walk = [step] := by
            have hu := p.orientedForestAdjacencyWitness_spec_unique sw.adj
              ⟨sw.ig, sw.member, sw.bounds, step.2, rfl⟩
            simp only [walk, Policy.orientedStepsOfWalk]
            have hp : ((p.orientedForestAdjacencyWitness sw.adj).ig.1,
                (p.orientedForestAdjacencyWitness sw.adj).reversed) = step := by
              apply Prod.ext
              · exact congrArg Prod.fst hu.1 |>.trans sw.index_eq
              · exact hu.2
            rw [hp]
          exact ⟨sw.source, sw.target, walk, hfirstSource.symm,
            hfirstTarget.symm, hencoded, by simp [walk]⟩
      | cons next tail =>
          cases htailInfo : p.gluingPathInfo (next :: tail) with
          | none =>
              change (match p.orientedGluing step,
                  p.gluingPathInfo (next :: tail) with
                | some first, some tail =>
                    if first.target = tail.source then
                      some ⟨first.source, tail.target,
                        PMap.comp first.transport tail.transport⟩
                    else none
                | _, _ => none) = some info at hinfo
              rw [hfirst, htailInfo] at hinfo
              contradiction
          | some tailInfo =>
              have hrestNonempty : next :: tail ≠ [] := by simp
              have hrestAll : ∀ s ∈ next :: tail, s.1 ∈ p.gluingForest := by
                intro s hs
                exact hall s (by simp [hs])
              let tailResult := ih tailInfo hrestNonempty hrestAll htailInfo
              rcases tailResult with
                ⟨tailSource, tailTarget, tailWalk, tailSourceEq, tailTargetEq,
                  tailStepsEq, tailLengthEq⟩
              change (match p.orientedGluing step,
                  p.gluingPathInfo (next :: tail) with
                | some first, some tail =>
                    if first.target = tail.source then
                      some ⟨first.source, tail.target,
                        PMap.comp first.transport tail.transport⟩
                    else none
                | _, _ => none) = some info at hinfo
              rw [hfirst, htailInfo] at hinfo
              simp at hinfo
              have hjoinNat : first.target = tailInfo.source := hinfo.1
              have hrecord :
                  (⟨first.source, tailInfo.target,
                    PMap.comp first.transport tailInfo.transport⟩ :
                    GluingPathInfo) = info := hinfo.2
              have htypedNat :
                  (sw.target.1.val, sw.target.2) =
                    (tailSource.1.val, tailSource.2) :=
                hfirstTarget.symm.trans
                  (hjoinNat.trans tailSourceEq.symm)
              have hjoinTyped : sw.target = tailSource :=
                Prod.ext
                  (Fin.ext (congrArg (fun z : Nat × Role => z.1) htypedNat))
                  (congrArg (fun z : Nat × Role => z.2) htypedNat)
              subst tailSource
              let walk : p.typedGluingForestGraph.Walk sw.source tailTarget :=
                .cons sw.adj tailWalk
              have hencodedHead :
                  ((p.orientedForestAdjacencyWitness sw.adj).ig.1,
                    (p.orientedForestAdjacencyWitness sw.adj).reversed) = step := by
                have hu := p.orientedForestAdjacencyWitness_spec_unique sw.adj
                  ⟨sw.ig, sw.member, sw.bounds, step.2, rfl⟩
                apply Prod.ext
                · exact congrArg Prod.fst hu.1 |>.trans sw.index_eq
                · exact hu.2
              have hinfoEq : info =
                  ⟨first.source, tailInfo.target,
                    PMap.comp first.transport tailInfo.transport⟩ :=
                hrecord.symm
              refine ⟨sw.source, tailTarget, walk, ?_, ?_, ?_, ?_⟩
              · rw [hinfoEq]
                exact hfirstSource.symm
              · rw [hinfoEq]
                exact tailTargetEq
              · simp only [walk, Policy.orientedStepsOfWalk, hencodedHead,
                  tailStepsEq]
              · simp [walk, tailLengthEq]

theorem Policy.orientedForestAdjacencyWitness_endpointKey (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.typedGluingForestGraph.Adj u v) :
    let w := p.orientedForestAdjacencyWitness h
    s((typedEdge p w.ig w.bounds).1, (typedEdge p w.ig w.bounds).2) = s(u, v) := by
  let w := p.orientedForestAdjacencyWitness h
  cases hr : w.reversed
  · have he : typedEdge p w.ig w.bounds = (u, v) := by
      simpa [w, orientedTypedEndpoints, hr] using w.endpoints
    exact congrArg (fun e => s(e.1, e.2)) he
  · have he : ((typedEdge p w.ig w.bounds).2,
        (typedEdge p w.ig w.bounds).1) = (u, v) := by
      simpa [w, orientedTypedEndpoints, hr] using w.endpoints
    simpa only [Sym2.eq_swap] using congrArg (fun e => s(e.1, e.2)) he

theorem Policy.mem_orientedStepsOfWalk_indices_has_edge (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v) {n : Nat}
    (hn : n ∈ (p.orientedStepsOfWalk w).map Prod.fst) :
    ∃ e ∈ w.edges, ∃ ig ∈ p.indexedGluingForest,
      ig.1 = n ∧ ∃ hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length,
        s((typedEdge p ig hb).1, (typedEdge p ig hb).2) = e := by
  induction w with
  | nil => simp [Policy.orientedStepsOfWalk] at hn
  | @cons u x v h rest ih =>
      let a := p.orientedForestAdjacencyWitness h
      simp only [Policy.orientedStepsOfWalk, List.map_cons, List.mem_cons] at hn
      rcases hn with hn | hn
      · refine ⟨s(u, x), by simp, a.ig, a.member, ?_, a.bounds, ?_⟩
        · simpa [a] using hn.symm
        · simpa [a] using p.orientedForestAdjacencyWitness_endpointKey h
      · obtain ⟨e, he, ig, hig, hin, hb, hkey⟩ := ih hn
        exact ⟨e, by simp [he], ig, hig, hin, hb, hkey⟩

theorem Policy.mem_walk_edges_has_orientedStepIndex (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v)
    {e : Sym2 (Fin p.squares.length × Role)} (he : e ∈ w.edges) :
    ∃ ig ∈ p.indexedGluingForest,
      ig.1 ∈ (p.orientedStepsOfWalk w).map Prod.fst ∧
      ∃ hb : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length,
        s((typedEdge p ig hb).1, (typedEdge p ig hb).2) = e := by
  induction w with
  | nil => simp at he
  | @cons u x v h rest ih =>
      simp only [SimpleGraph.Walk.edges_cons, List.mem_cons] at he
      rcases he with rfl | he
      · let a := p.orientedForestAdjacencyWitness h
        refine ⟨a.ig, a.member, ?_, a.bounds, ?_⟩
        · simp [Policy.orientedStepsOfWalk, a]
        · simpa [a] using p.orientedForestAdjacencyWitness_endpointKey h
      · obtain ⟨ig, hig, hin, hb, hkey⟩ := ih he
        exact ⟨ig, hig, by simp [Policy.orientedStepsOfWalk, hin], hb, hkey⟩

theorem Policy.walk_edges_nodup_of_orientedStep_indices_nodup (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v)
    (hn : ((p.orientedStepsOfWalk w).map Prod.fst).Nodup) :
    w.edges.Nodup := by
  induction w with
  | nil => simp
  | @cons u x v h rest ih =>
      let a := p.orientedForestAdjacencyWitness h
      simp only [Policy.orientedStepsOfWalk, List.map_cons,
        List.nodup_cons] at hn
      simp only [SimpleGraph.Walk.edges_cons, List.nodup_cons]
      refine ⟨?_, ih hn.2⟩
      intro he
      obtain ⟨ig, hig, hin, hb, hkey⟩ :=
        p.mem_walk_edges_has_orientedStepIndex rest he
      have haKey : s((typedEdge p a.ig a.bounds).1,
          (typedEdge p a.ig a.bounds).2) = s(u, x) := by
        simpa [a] using p.orientedForestAdjacencyWitness_endpointKey h
      have higEq : ig = a.ig :=
        p.indexedGluingForest_typedEndpointKey_unique hig a.member hb a.bounds
          (hkey.trans haKey.symm)
      subst ig
      exact hn.1 hin

theorem OrientedStepsWalkResult.isTrail
    {p : Policy} {steps : List OrientedGluing} {info : GluingPathInfo}
    (r : OrientedStepsWalkResult p steps info)
    (hn : (steps.map Prod.fst).Nodup) : r.walk.IsTrail := by
  constructor
  apply p.walk_edges_nodup_of_orientedStep_indices_nodup
  rw [r.steps_eq]
  exact hn

theorem OrientedStepsWalkResult.isPath
    {p : Policy} {steps : List OrientedGluing} {info : GluingPathInfo}
    (r : OrientedStepsWalkResult p steps info)
    (hn : (steps.map Prod.fst).Nodup) : r.walk.IsPath :=
  (p.typedGluingForestGraph_isAcyclic.isPath_iff_isTrail r.walk).mpr
    (r.isTrail hn)

structure OrientedStepsPathResult (p : Policy)
    (steps : List OrientedGluing) (info : GluingPathInfo) where
  source : Fin p.squares.length × Role
  target : Fin p.squares.length × Role
  path : p.typedGluingForestGraph.Path source target
  source_eq : (source.1.val, source.2) = info.source
  target_eq : (target.1.val, target.2) = info.target
  steps_eq : p.orientedStepsOfPath path = steps
  length_eq : path.1.length = steps.length

noncomputable def Policy.pathOfComposableOrientedSteps (p : Policy)
    (steps : List OrientedGluing) (info : GluingPathInfo)
    (hne : steps ≠ [])
    (hall : ∀ step ∈ steps, step.1 ∈ p.gluingForest)
    (hinfo : p.gluingPathInfo steps = some info)
    (hn : (steps.map Prod.fst).Nodup) :
    OrientedStepsPathResult p steps info := by
  let r := p.walkOfComposableOrientedSteps steps info hne hall hinfo
  have hpath : r.walk.IsPath := r.isPath hn
  let q : p.typedGluingForestGraph.Path r.source r.target := ⟨r.walk, hpath⟩
  exact ⟨r.source, r.target, q, r.source_eq, r.target_eq,
    r.steps_eq, r.length_eq⟩

theorem OrientedStepsPathResult.path_unique
    {p : Policy} {steps : List OrientedGluing} {info : GluingPathInfo}
    (r : OrientedStepsPathResult p steps info)
    (q : p.typedGluingForestGraph.Path r.source r.target)
    (_hq : p.orientedStepsOfPath q = steps) : r.path = q :=
  p.typedGluingForest_path_unique r.path q

theorem OrientedStepsPathResult.eq_canonicalForestPath
    {p : Policy} {steps : List OrientedGluing} {info : GluingPathInfo}
    (r : OrientedStepsPathResult p steps info) :
    r.path = p.canonicalTypedGluingForestPath
      ((p.typedGluingForestGraph_reachable_iff r.source r.target).mp
        r.path.1.reachable) := by
  symm
  apply p.canonicalTypedGluingForestPath_unique

theorem Policy.orientedStepsOfWalk_indices_nodup_of_isTrail (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v) (hw : w.IsTrail) :
    ((p.orientedStepsOfWalk w).map Prod.fst).Nodup := by
  induction w with
  | nil => simp [Policy.orientedStepsOfWalk]
  | @cons u x v h rest ih =>
      let a := p.orientedForestAdjacencyWitness h
      rw [SimpleGraph.Walk.isTrail_cons] at hw
      simp only [Policy.orientedStepsOfWalk, List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hw.1⟩
      intro hmem
      obtain ⟨e, he, ig, hig, hin, hb, hkey⟩ :=
        p.mem_orientedStepsOfWalk_indices_has_edge rest hmem
      have higEq : ig = a.ig :=
        p.indexedGluingForest_index_unique hig a.member hin
      subst ig
      have haKey : s((typedEdge p a.ig a.bounds).1,
          (typedEdge p a.ig a.bounds).2) = s(u, x) := by
        simpa [a] using p.orientedForestAdjacencyWitness_endpointKey h
      have hsame : s(u, x) = e := by
        rw [← haKey]
        rw [← hkey]
      apply hw.2
      exact hsame.symm ▸ he

theorem Policy.orientedStepsOfPath_indices_nodup (p : Policy)
    {u v : Fin p.squares.length × Role}
    (q : p.typedGluingForestGraph.Path u v) :
    ((p.orientedStepsOfPath q).map Prod.fst).Nodup :=
  p.orientedStepsOfWalk_indices_nodup_of_isTrail q.1 q.2.isTrail

theorem Policy.orientedStepsOfPath_nil (p : Policy)
    (u : Fin p.squares.length × Role) :
    p.orientedStepsOfPath (SimpleGraph.Path.nil :
      p.typedGluingForestGraph.Path u u) = [] := by
  rfl

theorem Policy.canonical_orientedSteps_unique (p : Policy)
    {u v : Fin p.squares.length × Role}
    (h : p.admittedTypedGluingGraph.Reachable u v)
    (q : p.typedGluingForestGraph.Path u v) :
    p.orientedStepsOfPath (p.canonicalTypedGluingForestPath h) =
      p.orientedStepsOfPath q := by
  rw [p.canonicalTypedGluingForestPath_unique h q]

theorem Policy.gluingPathInfo_orientedStepsOfPath_nil (p : Policy)
    (u : Fin p.squares.length × Role) :
    p.gluingPathInfo (p.orientedStepsOfPath (SimpleGraph.Path.nil :
      p.typedGluingForestGraph.Path u u)) = none := by
  rfl

def Policy.orientedTransportFold (p : Policy) : List OrientedGluing → Option PMap
  | [] => none
  | [step] => (p.orientedGluing step).map (·.transport)
  | step :: rest =>
      match p.orientedGluing step, p.orientedTransportFold rest with
      | some first, some tail => some (PMap.comp first.transport tail)
      | _, _ => none

theorem Policy.gluingPathInfo_orientedStepsOfWalk (p : Policy)
    {u v : Fin p.squares.length × Role}
    (w : p.typedGluingForestGraph.Walk u v) (hne : ¬ w.Nil) :
    ∃ info,
      p.gluingPathInfo (p.orientedStepsOfWalk w) = some info ∧
      info.source = (u.1.val, u.2) ∧
      info.target = (v.1.val, v.2) ∧
      p.orientedTransportFold (p.orientedStepsOfWalk w) = some info.transport := by
  induction w with
  | nil => exact (hne (by simp)).elim
  | @cons u x v hadj rest ih =>
      let a := p.orientedForestAdjacencyWitness hadj
      obtain ⟨first, hfirst, hsource, htarget⟩ :=
        p.orientedGluing_of_forestAdjacencyWitness a
      cases rest with
      | nil =>
          refine ⟨first, ?_, hsource, ?_, ?_⟩
          · simpa [Policy.orientedStepsOfWalk, a, Policy.gluingPathInfo] using hfirst
          · simpa using htarget
          · simpa [Policy.orientedStepsOfWalk, Policy.orientedTransportFold, a,
              hfirst]
      | cons htail walk =>
          obtain ⟨last, hlast, hlastSource, hlastTarget, hfold⟩ :=
            ih (by simp)
          have hjoin : first.target = last.source := htarget.trans hlastSource.symm
          have hlast' : p.gluingPathInfo
              (((p.orientedForestAdjacencyWitness htail).ig.1,
                (p.orientedForestAdjacencyWitness htail).reversed) ::
                p.orientedStepsOfWalk walk) = some last := by
            simpa only [Policy.orientedStepsOfWalk] using hlast
          have hfold' : p.orientedTransportFold
              (((p.orientedForestAdjacencyWitness htail).ig.1,
                (p.orientedForestAdjacencyWitness htail).reversed) ::
                p.orientedStepsOfWalk walk) = some last.transport := by
            simpa only [Policy.orientedStepsOfWalk] using hfold
          let info : GluingPathInfo :=
            ⟨first.source, last.target, PMap.comp first.transport last.transport⟩
          refine ⟨info, ?_, ?_, ?_, ?_⟩
          · simp only [Policy.orientedStepsOfWalk, Policy.gluingPathInfo]
            rw [show p.orientedGluing
                ((p.orientedForestAdjacencyWitness hadj).ig.1,
                  (p.orientedForestAdjacencyWitness hadj).reversed) = some first by
                  simpa [a] using hfirst]
            rw [hlast']
            simp [hjoin, info]
          · exact hsource
          · exact hlastTarget
          · simp only [Policy.orientedStepsOfWalk, Policy.orientedTransportFold]
            rw [show p.orientedGluing
                ((p.orientedForestAdjacencyWitness hadj).ig.1,
                  (p.orientedForestAdjacencyWitness hadj).reversed) = some first by
                  simpa [a] using hfirst]
            rw [hfold']

theorem Policy.gluingPathInfo_orientedStepsOfPath (p : Policy)
    {u v : Fin p.squares.length × Role}
    (q : p.typedGluingForestGraph.Path u v) (hne : ¬ q.1.Nil) :
    ∃ info,
      p.gluingPathInfo (p.orientedStepsOfPath q) = some info ∧
      info.source = (u.1.val, u.2) ∧
      info.target = (v.1.val, v.2) ∧
      p.orientedTransportFold (p.orientedStepsOfPath q) = some info.transport :=
  p.gluingPathInfo_orientedStepsOfWalk q.1 hne

structure GluingCycleObligation where
  edge : Nat
  forestPath : List OrientedGluing
  deriving DecidableEq

structure RequiredCycleEdgeWitness (p : Policy) (k : Nat) where
  ig : Nat × Gluing
  admitted : ig ∈ admittedIndexedGluings p
  index_eq : ig.1 = k
  notRetained : ig ∉ p.indexedGluingForest
  bounds : ig.2.i < p.squares.length ∧ ig.2.j < p.squares.length

def RequiredCycleEdgeWitness.source {p : Policy} {k : Nat}
    (w : RequiredCycleEdgeWitness p k) : Fin p.squares.length × Role :=
  ((⟨w.ig.2.i, w.bounds.1⟩, w.ig.2.rᵢ))

def RequiredCycleEdgeWitness.target {p : Policy} {k : Nat}
    (w : RequiredCycleEdgeWitness p k) : Fin p.squares.length × Role :=
  ((⟨w.ig.2.j, w.bounds.2⟩, w.ig.2.rⱼ))

theorem Policy.requiredCycleEdge_has_witness (p : Policy) {k : Nat}
    (hk : k ∈ p.requiredCycleEdges) : Nonempty (RequiredCycleEdgeWitness p k) := by
  unfold Policy.requiredCycleEdges at hk
  obtain ⟨ig, hig, hfilter⟩ := List.mem_filterMap.mp hk
  by_cases hr : ig.1 ∈ p.gluingForest
  · simp [hr] at hfilter
  · have hindex : ig.1 = k := by simpa [hr] using hfilter
    have hwf := admittedIndexedGluings_wellFormed p ig hig
    refine ⟨⟨ig, hig, hindex, ?_, Gluing.wellFormed_endpoint_bounds hwf⟩⟩
    intro hret
    exact hr (List.mem_map.mpr ⟨ig, hret, rfl⟩)

theorem RequiredCycleEdgeWitness.admittedAdj
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k)
    (hne : w.source ≠ w.target) :
    p.admittedTypedGluingGraph.Adj w.source w.target := by
  change (FiniteListGraphClosure.graph
    (typedEdges p (admittedIndexedGluings p))).Adj w.source w.target
  rw [FiniteListGraphClosure.graph, SimpleGraph.fromRel_adj]
  refine ⟨hne, ?_⟩
  apply Or.inl
  apply List.mem_filterMap.mpr
  refine ⟨w.ig, w.admitted, ?_⟩
  simp [w.bounds, RequiredCycleEdgeWitness.source,
    RequiredCycleEdgeWitness.target]

theorem RequiredCycleEdgeWitness.forestReachable
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k) :
    p.typedGluingForestGraph.Reachable w.source w.target := by
  by_cases h : w.source = w.target
  · rw [h]
  · exact (p.typedGluingForestGraph_reachable_iff w.source w.target).mpr
      (w.admittedAdj h).reachable

noncomputable def RequiredCycleEdgeWitness.canonicalPath
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k) :
    p.typedGluingForestGraph.Path w.source w.target :=
  p.canonicalTypedGluingForestPath
    ((p.typedGluingForestGraph_reachable_iff w.source w.target).mp
      w.forestReachable)

noncomputable def RequiredCycleEdgeWitness.canonicalSteps
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k) :
    List OrientedGluing := p.orientedStepsOfPath w.canonicalPath

theorem RequiredCycleEdgeWitness.canonicalSteps_indices_nodup
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k) :
    (w.canonicalSteps.map Prod.fst).Nodup :=
  p.orientedStepsOfPath_indices_nodup w.canonicalPath

theorem RequiredCycleEdgeWitness.canonicalPath_nonempty
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k)
    (hne : w.source ≠ w.target) : ¬ w.canonicalPath.1.Nil := by
  intro hn
  exact hne ((w.canonicalPath.2.nil_iff_eq).mp hn)

theorem RequiredCycleEdgeWitness.canonicalPathInfo
    {p : Policy} {k : Nat} (w : RequiredCycleEdgeWitness p k)
    (hne : w.source ≠ w.target) :
    ∃ info,
      p.gluingPathInfo w.canonicalSteps = some info ∧
      info.source = (w.source.1.val, w.source.2) ∧
      info.target = (w.target.1.val, w.target.2) ∧
      p.orientedTransportFold w.canonicalSteps = some info.transport :=
  p.gluingPathInfo_orientedStepsOfPath w.canonicalPath
    (w.canonicalPath_nonempty hne)

private def GluingCycleObligation.valid (p : Policy)
    (o : GluingCycleObligation) : Bool :=
  decide (o.forestPath ≠ []) &&
    decide ((o.forestPath.map Prod.fst).eraseDups = o.forestPath.map Prod.fst) &&
    o.forestPath.all (fun step => decide (step.1 ∈ p.gluingForest)) &&
    match p.orientedGluing (o.edge, false), p.gluingPathInfo o.forestPath with
    | some direct, some path => decide (direct = path)
    | _, _ => false

/-- Semantic validity closes the path-choice self-exemption left open by the
executable compatibility check: the named path is exactly the unique forest
path derived from the required edge's typed endpoints. -/
def GluingCycleObligation.Valid (p : Policy) (o : GluingCycleObligation) : Prop :=
  o.valid p = true ∧
    ∃ w : RequiredCycleEdgeWitness p o.edge,
      o.forestPath = w.canonicalSteps

theorem GluingCycleObligation.Valid_forestPath_eq_canonical
    {p : Policy} {o : GluingCycleObligation} (h : o.Valid p) :
    ∃ w : RequiredCycleEdgeWitness p o.edge,
      o.forestPath = w.canonicalSteps := h.2

theorem GluingCycleObligation.Valid_not_typed_selfLoop
    {p : Policy} {o : GluingCycleObligation} (h : o.Valid p) :
    ∀ w : RequiredCycleEdgeWitness p o.edge, w.source ≠ w.target := by
  intro w heq
  obtain ⟨w', hcanonical⟩ := h.2
  have hw : w = w' := by
    cases w with
    | mk ig hig hindex hnot hb =>
      cases w' with
      | mk ig' hig' hindex' hnot' hb' =>
        have hii : ig.1 = ig'.1 := hindex.trans hindex'.symm
        have hnodup := admittedIndexedGluings_indices_nodup p
        have hsourceNodup : (admittedIndexedGluings p).Nodup :=
          hnodup.of_map Prod.fst
        have heqIg : ig = ig' :=
          (List.nodup_map_iff_inj_on hsourceNodup).mp hnodup
            ig hig ig' hig' hii
        subst ig'
        rfl
  subst w'
  have hnil : w.canonicalSteps = [] := by
    apply List.eq_nil_of_length_eq_zero
    unfold RequiredCycleEdgeWitness.canonicalSteps
    rw [Policy.orientedStepsOfPath_length]
    exact (w.canonicalPath.2.nil_iff_eq.mpr heq).length_eq_zero
  have hnonempty : o.forestPath ≠ [] := by
    have hv := h.1
    unfold GluingCycleObligation.valid at hv
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
    exact hv.1.1.1
  exact hnonempty (hcanonical.trans hnil)

theorem GluingCycleObligation.Valid_direct_eq_canonicalForestTransport
    {p : Policy} {o : GluingCycleObligation} (h : o.Valid p) :
    ∃ (w : RequiredCycleEdgeWitness p o.edge)
      (direct canonical : GluingPathInfo),
      o.forestPath = w.canonicalSteps ∧
      p.orientedGluing (o.edge, false) = some direct ∧
      p.gluingPathInfo w.canonicalSteps = some canonical ∧
      direct = canonical := by
  obtain ⟨w, hcanonical⟩ := h.2
  have hv := h.1
  unfold GluingCycleObligation.valid at hv
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hv
  have hm := hv.2
  rw [hcanonical] at hm
  cases hdirect : p.orientedGluing (o.edge, false) with
  | none => simp [hdirect] at hm
  | some direct =>
      cases hpath : p.gluingPathInfo w.canonicalSteps with
      | none => simp [hdirect, hpath] at hm
      | some canonical =>
          simp [hdirect, hpath] at hm
          exact ⟨w, direct, canonical, hcanonical, rfl, hpath, hm⟩

theorem GluingCycleObligation.Valid_directTransport_eq_canonicalForestTransport
    {p : Policy} {o : GluingCycleObligation} (h : o.Valid p) :
    ∃ (w : RequiredCycleEdgeWitness p o.edge)
      (direct canonical : GluingPathInfo),
      o.forestPath = w.canonicalSteps ∧
      p.orientedGluing (o.edge, false) = some direct ∧
      p.gluingPathInfo w.canonicalSteps = some canonical ∧
      direct.transport = canonical.transport := by
  obtain ⟨w, direct, canonical, hsteps, hdirect, hcanonical, heq⟩ :=
    GluingCycleObligation.Valid_direct_eq_canonicalForestTransport h
  exact ⟨w, direct, canonical, hsteps, hdirect, hcanonical,
    congrArg GluingPathInfo.transport heq⟩

structure GluingCoherenceCertificate where
  obligations : List GluingCycleObligation
  deriving DecidableEq

/-- Coverage is computed, never claimed: obligation edge indices must equal the
deterministic non-tree edge list exactly and each forest transport must equal
its direct edge.  A malformed policy cannot validate. -/
def GluingCoherenceCertificate.valid (p : Policy)
    (c : GluingCoherenceCertificate) : Bool :=
  p.wellFormed &&
    decide (c.obligations.map (·.edge) = p.requiredCycleEdges) &&
    c.obligations.all (GluingCycleObligation.valid p)

/-- Full semantic validity retains the executable gate and additionally binds
every listed obligation to the canonical typed forest path derived from its
required edge. -/
def GluingCoherenceCertificate.Valid (p : Policy)
    (c : GluingCoherenceCertificate) : Prop :=
  c.valid p = true ∧ ∀ o ∈ c.obligations, o.Valid p

theorem GluingCoherenceCertificate.Valid_covers_required_canonicalPaths
    {p : Policy} {c : GluingCoherenceCertificate} (h : c.Valid p) :
    c.obligations.map (·.edge) = p.requiredCycleEdges ∧
      ∀ o ∈ c.obligations,
        ∃ w : RequiredCycleEdgeWitness p o.edge,
          o.forestPath = w.canonicalSteps := by
  have hv := h.1
  simp only [GluingCoherenceCertificate.valid, Bool.and_eq_true,
    decide_eq_true_eq] at hv
  refine ⟨hv.1.2, ?_⟩
  intro o ho
  exact (h.2 o ho).2

/-- The strongest presently proved completeness result: a valid certificate
contains exactly every deterministic non-tree edge obligation, and every
listed forest transport agrees with that edge. -/
theorem GluingCoherenceCertificate.valid_covers_required_edges
    (p : Policy) (c : GluingCoherenceCertificate) (h : c.valid p = true) :
    c.obligations.map (·.edge) = p.requiredCycleEdges ∧
      c.obligations.all (GluingCycleObligation.valid p) = true := by
  simp only [GluingCoherenceCertificate.valid, Bool.and_eq_true,
    decide_eq_true_eq] at h
  exact ⟨h.1.2, h.2⟩

/-!
Still required for a semantic path-independence theorem: prove that the
ordered forest selected above is acyclic and spans each admitted component,
that its validated path is the unique simple forest path, and then derive
equality of arbitrary composable transports by reducing each path difference
to the checked non-tree obligations.  This executable slice does not claim
that theorem or a colimit/pasting result.
-/

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

/-! ## Additive application-order authorization

The meaning of an application-order triple is deliberately supplied by an
external law.  In particular, this model does not assume that application
order equals construction order. -/

structure ApplicationOrderLaw where
  identity : Nat
  version : Nat
  authority : Nat
  receipt : Nat
  decode : List (Nat × Nat × Nat) → Option (List Nat)
  accepts : List (Nat × Nat) → List Nat → Bool

structure ApplicationOrderCertificate where
  constructionOrder : List (Nat × Nat)
  applicationOrder : List (Nat × Nat × Nat)
  applicationSequence : List Nat
  lawIdentity : Nat
  lawVersion : Nat
  lawAuthority : Nat
  lawReceipt : Nat
  selectorAuthority : Nat
  deriving DecidableEq

private def exactSquarePopulation (p : Policy) (xs : List Nat) : Bool :=
  decide (xs.eraseDups = xs) &&
    decide (xs.toFinset = (List.range p.squares.length).toFinset)

/-- A certificate binds both policy orders and delegates their semantic
relation to an externally registered law.  Population validity is independent
of that law: every current square occurs exactly once and no foreign square
index occurs. -/
def ApplicationOrderCertificate.valid (p : Policy)
    (registry : List ApplicationOrderLaw) (c : ApplicationOrderCertificate) : Bool :=
  decide (c.constructionOrder = p.constructionOrder) &&
    decide (c.applicationOrder = p.applicationOrder) &&
    exactSquarePopulation p c.applicationSequence &&
    match registry.find? fun law =>
      law.identity = c.lawIdentity && law.version = c.lawVersion &&
        law.authority = c.lawAuthority && law.receipt = c.lawReceipt with
    | none => false
    | some law =>
        decide (law.identity ≠ 0) && decide (law.version ≠ 0) &&
          decide (law.authority ≠ 0) && decide (law.receipt ≠ 0) &&
          decide (c.selectorAuthority ≠ 0) &&
          decide (c.selectorAuthority ≠ law.authority) &&
          decide (law.decode c.applicationOrder = some c.applicationSequence) &&
          law.accepts c.constructionOrder c.applicationSequence

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

private def decodeFirstIndex (rows : List (Nat × Nat × Nat)) : Option (List Nat) :=
  some (rows.map fun row => row.1)

private def diamondExactOrderLaw : ApplicationOrderLaw :=
  { identity := 71
    version := 1
    authority := 72
    receipt := 73
    decode := decodeFirstIndex
    accepts := fun construction application =>
      decide (construction = [(0, 1), (0, 2), (1, 3), (2, 3)]) &&
        decide (application = [0, 1, 2, 3]) }

private def applicationRows (xs : List Nat) : List (Nat × Nat × Nat) :=
  xs.map fun i => (i, i + 10, i + 20)

private def orderedDiamondPolicy : Policy :=
  { diamondPolicy with
    applicationOrder := applicationRows [0, 1, 2, 3] }

private def diamondCertificateFor (xs : List Nat) : ApplicationOrderCertificate :=
  { constructionOrder := [(0, 1), (0, 2), (1, 3), (2, 3)]
    applicationOrder := applicationRows xs
    applicationSequence := xs
    lawIdentity := 71
    lawVersion := 1
    lawAuthority := 72
    lawReceipt := 73
    selectorAuthority := 74 }

private def orderedDiamondCertificate : ApplicationOrderCertificate :=
  diamondCertificateFor [0, 1, 2, 3]

private def diamondPolicyFor (xs : List Nat) : Policy :=
  { diamondPolicy with applicationOrder := applicationRows xs }

theorem ordered_diamond_certificate_valid :
    orderedDiamondCertificate.valid orderedDiamondPolicy [diamondExactOrderLaw] = true := by
  native_decide

/-- Equal square membership is weaker than authorized ordered equality. -/
theorem reordered_same_population_but_invalid :
    exactSquarePopulation orderedDiamondPolicy [0, 2, 1, 3] = true ∧
    (diamondCertificateFor [0, 2, 1, 3]).valid
      (diamondPolicyFor [0, 2, 1, 3]) [diamondExactOrderLaw] = false := by
  native_decide

theorem duplicate_square_invalid :
    (diamondCertificateFor [0, 1, 2, 2]).valid
      (diamondPolicyFor [0, 1, 2, 2]) [diamondExactOrderLaw] = false := by
  native_decide

theorem omitted_square_invalid :
    (diamondCertificateFor [0, 1, 2]).valid
      (diamondPolicyFor [0, 1, 2]) [diamondExactOrderLaw] = false := by
  native_decide

theorem unknown_square_invalid :
    (diamondCertificateFor [0, 1, 2, 4]).valid
      (diamondPolicyFor [0, 1, 2, 4]) [diamondExactOrderLaw] = false := by
  native_decide

theorem substituted_application_law_invalid :
    ({ orderedDiamondCertificate with lawIdentity := 74 }).valid
      orderedDiamondPolicy [diamondExactOrderLaw] = false := by
  native_decide

theorem self_authorized_application_order_invalid :
    ({ orderedDiamondCertificate with selectorAuthority := 72 }).valid
      orderedDiamondPolicy [diamondExactOrderLaw] = false := by
  native_decide

private def alternateDiamondLaw : ApplicationOrderLaw :=
  { identity := 71
    version := 1
    authority := 72
    receipt := 73
    decode := decodeFirstIndex
    accepts := fun construction application =>
      decide (construction = [(0, 1), (0, 2), (1, 3), (2, 3)]) &&
        decide (application = [0, 2, 1, 3]) }

/-- Matching labels do not make a substituted implementation authorized.  The
crafted certificate fails against the fixed registry.  Replacing the registry
itself makes it pass, because registry trust is an external premise rather
than cryptographic authentication supplied by Lean. -/
theorem substituted_law_implementation_boundary :
    (diamondCertificateFor [0, 2, 1, 3]).valid
        (diamondPolicyFor [0, 2, 1, 3]) [diamondExactOrderLaw] = false ∧
      (diamondCertificateFor [0, 2, 1, 3]).valid
        (diamondPolicyFor [0, 2, 1, 3]) [alternateDiamondLaw] = true := by
  native_decide

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
