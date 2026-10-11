import Mathlib.Combinatorics.SimpleGraph.Acyclic
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Finite
import Mathlib.Combinatorics.SimpleGraph.Paths

/-! Executable repeated edge-list closure agrees with finite undirected graph
reachability.  The list order may accelerate a scan but cannot change the
fixed point. -/

namespace DarkTower.WarMachine.FiniteListGraphClosure

variable {V : Type*} [DecidableEq V]

def graph (edges : List (V × V)) : SimpleGraph V :=
  SimpleGraph.fromRel fun u v => (u, v) ∈ edges

def step (edges : List (V × V)) (seen : Finset V) : Finset V :=
  edges.foldl (fun acc e =>
    if e.1 ∈ acc then insert e.2 acc
    else if e.2 ∈ acc then insert e.1 acc
    else acc) seen

def close (edges : List (V × V)) : Nat → Finset V → Finset V
  | 0, seen => seen
  | n + 1, seen => close edges n (step edges seen)

theorem subset_step (edges : List (V × V)) (seen : Finset V) :
    seen ⊆ step edges seen := by
  unfold step
  induction edges generalizing seen with
  | nil => exact Finset.Subset.rfl
  | cons e es ih =>
      simp only [List.foldl_cons]
      apply Finset.Subset.trans (s₂ :=
        if e.1 ∈ seen then insert e.2 seen
        else if e.2 ∈ seen then insert e.1 seen else seen)
      · split <;> rename_i h
        · simp
        · split <;> simp
      · exact ih _

theorem subset_close (edges : List (V × V)) (n : Nat) (seen : Finset V) :
    seen ⊆ close edges n seen := by
  induction n generalizing seen with
  | zero => exact Finset.Subset.rfl
  | succ n ih => exact Finset.Subset.trans (subset_step edges seen) (ih _)

private theorem adjacent_enters_step (edges : List (V × V)) {u v : V}
    (hu : u ∈ seen) (h : (graph edges).Adj u v) : v ∈ step edges seen := by
  change (SimpleGraph.fromRel (fun a b => (a, b) ∈ edges)).Adj u v at h
  rw [SimpleGraph.fromRel_adj] at h
  rcases h.2 with huv | hvu
  · induction edges generalizing seen with
    | nil => simp at huv
    | cons e es ih =>
        simp only [List.mem_cons] at huv
        rcases huv with rfl | huv
        · simp only [step, List.foldl_cons]
          exact subset_step es _ (by simp [hu])
        · simp only [step, List.foldl_cons]
          apply ih
          · exact (subset_step [e] seen hu)
          · exact ⟨h.1, Or.inl huv⟩
          · exact huv
  · induction edges generalizing seen with
    | nil => simp at hvu
    | cons e es ih =>
        simp only [List.mem_cons] at hvu
        rcases hvu with rfl | hvu
        · simp only [step, List.foldl_cons]
          apply subset_step es _
          by_cases hv : v ∈ seen <;> simp [hv, hu]
        · simp only [step, List.foldl_cons]
          apply ih
          · exact (subset_step [e] seen hu)
          · exact ⟨h.1, Or.inr hvu⟩
          · exact hvu

private theorem walk_end_mem_close (edges : List (V × V))
    {u v : V} (w : (graph edges).Walk u v) (hu : u ∈ seen) :
    v ∈ close edges w.length seen := by
  induction w generalizing seen with
  | nil => exact hu
  | cons h w ih =>
      simp only [SimpleGraph.Walk.length_cons, close]
      exact ih (adjacent_enters_step edges hu h)

private theorem step_sound_aux (full todo : List (V × V)) (root : V)
    (hsub : ∀ e ∈ todo, e ∈ full) {seen : Finset V}
    (hs : ∀ x ∈ seen, (graph full).Reachable root x) :
    ∀ x ∈ todo.foldl (fun acc e =>
      if e.1 ∈ acc then insert e.2 acc
      else if e.2 ∈ acc then insert e.1 acc else acc) seen,
      (graph full).Reachable root x := by
  induction todo generalizing seen with
  | nil => exact hs
  | cons e es ih =>
      simp only [List.foldl_cons]
      apply ih (fun a ha => hsub a (by simp [ha]))
      intro x hx
      split at hx <;> rename_i h₁
      · simp only [Finset.mem_insert] at hx
        rcases hx with rfl | hx
        · by_cases heq : e.1 = e.2
          · simpa [heq] using hs e.1 h₁
          · exact (hs e.1 h₁).trans <| by
              apply SimpleGraph.Adj.reachable
              change (SimpleGraph.fromRel (fun a b => (a, b) ∈ full)).Adj e.1 e.2
              rw [SimpleGraph.fromRel_adj]
              exact ⟨heq, Or.inl (hsub e (by simp))⟩
        · exact hs x hx
      · split at hx <;> rename_i h₂
        · simp only [Finset.mem_insert] at hx
          rcases hx with rfl | hx
          · by_cases heq : e.2 = e.1
            · simpa [heq] using hs e.2 h₂
            · exact (hs e.2 h₂).trans <| by
                apply SimpleGraph.Adj.reachable
                change (SimpleGraph.fromRel (fun a b => (a, b) ∈ full)).Adj e.2 e.1
                rw [SimpleGraph.fromRel_adj]
                exact ⟨heq, Or.inr (hsub e (by simp))⟩
          · exact hs x hx
        · exact hs x hx

private theorem step_sound (edges : List (V × V)) (root : V) {seen : Finset V}
    (hs : ∀ x ∈ seen, (graph edges).Reachable root x) :
    ∀ x ∈ step edges seen, (graph edges).Reachable root x := by
  exact step_sound_aux edges edges root (fun _ => id) hs

private theorem close_sound (edges : List (V × V)) (root : V) (n : Nat)
    {seen : Finset V} (hs : ∀ x ∈ seen, (graph edges).Reachable root x) :
    ∀ x ∈ close edges n seen, (graph edges).Reachable root x := by
  induction n generalizing seen with
  | zero => exact hs
  | succ n ih => exact ih (step_sound edges root hs)

private theorem close_add (edges : List (V × V)) (m n : Nat) (seen : Finset V) :
    close edges (m + n) seen = close edges n (close edges m seen) := by
  induction m generalizing seen with
  | zero => simp [close]
  | succ m ih => simpa [Nat.succ_add, close] using ih (step edges seen)

private theorem close_mono_rounds (edges : List (V × V)) {m n : Nat}
    (h : m ≤ n) {seen : Finset V} : close edges m seen ⊆ close edges n seen := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
  rw [close_add]
  exact subset_close edges k _

theorem mem_close_card_iff_reachable [Fintype V] (edges : List (V × V)) (u v : V) :
    v ∈ close edges (Fintype.card V) {u} ↔ (graph edges).Reachable u v := by
  constructor
  · intro hv
    exact close_sound edges u _ (by simp) v hv
  · intro h
    obtain ⟨w, hw⟩ := h.exists_isPath
    have hm := walk_end_mem_close edges w (by simp : u ∈ ({u} : Finset V))
    exact close_mono_rounds edges (Nat.le_of_lt hw.length_lt) hm

theorem empty_graph_closure [Fintype V] (u : V) :
    close ([] : List (V × V)) (Fintype.card V) {u} = {u} := by
  induction Fintype.card V <;> simp_all [close, step]

/-- Reverse edge order permits only one new chain vertex per scan; this catches
an iteration bound shorter than the finite vertex cardinality. -/
theorem reverse_order_chain_reaches_last :
    (4 : Fin 5) ∈ close
      [((3 : Fin 5), 4), (2, 3), (1, 2), (0, 1)]
      (Fintype.card (Fin 5)) {(0 : Fin 5)} := by
  native_decide

theorem edge_order_does_not_change_final_reachability :
    close [((3 : Fin 5), 4), (2, 3), (1, 2), (0, 1)]
        (Fintype.card (Fin 5)) {(0 : Fin 5)} =
      close [((0 : Fin 5), 1), (1, 2), (2, 3), (3, 4)]
        (Fintype.card (Fin 5)) {(0 : Fin 5)} := by
  native_decide

#print axioms mem_close_card_iff_reachable
#print axioms empty_graph_closure
#print axioms reverse_order_chain_reaches_last
#print axioms edge_order_does_not_change_final_reachability

end DarkTower.WarMachine.FiniteListGraphClosure
