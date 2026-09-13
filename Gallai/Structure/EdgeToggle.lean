/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.EdgeDeletion
import Mathlib.Data.Set.Card

/-! # Single-edge parity repair with original/synthetic status explicit -/
namespace Gallai
variable {V : Type*} [Fintype V] [DecidableEq V]
variable (G : SimpleGraph V) [DecidableRel G.Adj]

/-- Delete an original edge, or add the absent synthetic edge. -/
def toggleEdge (x y : V) : SimpleGraph V :=
  if G.Adj x y then G.deleteEdges {s(x, y)} else G ⊔ SimpleGraph.edge x y

instance (x y : V) : DecidableRel (toggleEdge G x y).Adj := by
  unfold toggleEdge
  split <;> infer_instance

omit [Fintype V] [DecidableEq V] [DecidableRel G.Adj] in
/-- Restoring a missing edge and deleting that same synthetic edge cancel. -/
theorem add_missing_delete (x y : V) (hmissing : ¬ G.Adj x y) :
    (G ⊔ SimpleGraph.edge x y).deleteEdges {s(x, y)} = G := by
  ext a b
  simp only [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
    Set.mem_singleton_iff, Sym2.eq_iff, SimpleGraph.edge_adj]
  constructor
  · rintro ⟨ha | ⟨ha, _⟩, hn⟩
    · exact ha
    · exact (hn ha).elim
  · intro ha
    refine ⟨Or.inl ha, ?_⟩
    rintro (⟨rfl, rfl⟩ | ⟨rfl, rfl⟩)
    · exact hmissing ha
    · exact hmissing ha.symm

/-- Toggle degree at the first end differs by precisely one, with status retained. -/
theorem toggleEdge_degree_endpoint (x y : V) (hne : x ≠ y) :
    if G.Adj x y then (toggleEdge G x y).degree x + 1 = G.degree x
    else (toggleEdge G x y).degree x = G.degree x + 1 := by
  classical
  by_cases hxy : G.Adj x y
  · simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', toggleEdge, if_pos hxy] using
      degree_delete_edge_add_one G x y hxy
  · have ha : (G ⊔ SimpleGraph.edge x y).Adj x y :=
      Or.inr ((SimpleGraph.edge_adj ..).mpr ⟨Or.inl ⟨rfl, rfl⟩, hne⟩)
    have hd := degree_delete_edge_add_one (G ⊔ SimpleGraph.edge x y) x y ha
    have he := add_missing_delete G x y hxy
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', toggleEdge, if_neg hxy, he] using hd.symm

/-- Unaffected vertices retain their exact degree in either repair status. -/
theorem toggleEdge_degree_of_ne (x y v : V) (hx : v ≠ x) (hy : v ≠ y) :
    (toggleEdge G x y).degree v = G.degree v := by
  classical
  by_cases hxy : G.Adj x y
  · simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', toggleEdge, if_pos hxy] using
      degree_delete_edge_of_ne G x y v hx hy
  · have hd := degree_delete_edge_of_ne (G ⊔ SimpleGraph.edge x y) x y v hx hy
    have he := add_missing_delete G x y hxy
    simpa only [SimpleGraph.degree, SimpleGraph.neighborFinset,
      ← Set.ncard_eq_toFinset_card', toggleEdge, if_neg hxy, he] using hd.symm

omit [Fintype V] [DecidableEq V] in
/-- Exchanging the names of the ends leaves the repair graph unchanged. -/
theorem toggleEdge_comm (x y : V) : toggleEdge G x y = toggleEdge G y x := by
  simp only [toggleEdge, G.adj_comm y x, Sym2.eq_swap (a := y) (b := x),
    SimpleGraph.edge_comm (s := y) (t := x)]

omit [Fintype V] [DecidableEq V] in
/-- Adjacency to a vertex outside the repair pair is unchanged. -/
theorem toggleEdge_adj_of_ne (x y u v : V) (hx : v ≠ x) (hy : v ≠ y) :
    (toggleEdge G x y).Adj u v ↔ G.Adj u v := by
  unfold toggleEdge
  split <;> simp [SimpleGraph.deleteEdges_adj, SimpleGraph.sup_adj,
    SimpleGraph.edge_adj, hx, hy]

/-- At either end, and only there, the toggle reverses degree parity. -/
theorem toggleEdge_even_iff (x y : V) (hne : x ≠ y) (v : V) :
    Even ((toggleEdge G x y).degree v) ↔
      if v = x ∨ v = y then ¬ Even (G.degree v) else Even (G.degree v) := by
  classical
  by_cases hx : v = x
  · subst v
    have hd := toggleEdge_degree_endpoint G x y hne
    split_ifs at hd <;> simp only [Nat.even_iff] at * <;> simp only [true_or, if_true]
    all_goals omega
  · by_cases hy : v = y
    · subst v
      have hd := toggleEdge_degree_endpoint G y x hne.symm
      have hd' : (toggleEdge G x y).degree y = (toggleEdge G y x).degree y := by
        simp only [SimpleGraph.degree, SimpleGraph.neighborFinset,
          ← Set.ncard_eq_toFinset_card', toggleEdge_comm G x y]
      rw [hd']
      split_ifs at hd <;> simp only [Nat.even_iff] at * <;> simp only [or_true, if_true]
      all_goals omega
    · rw [toggleEdge_degree_of_ne G x y v hx hy]
      simp [hx, hy]

end Gallai
