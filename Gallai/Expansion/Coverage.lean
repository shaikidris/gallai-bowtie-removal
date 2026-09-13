/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.LocalCoverage
import Gallai.Expansion.Boundary
import Gallai.Operations.EraseCarrier

/-!
# A genuine decomposition of the star expansion

Retained old edges and active local edges exhaust the expanded graph and
cannot overlap. Each part has unique ownership at the same candidate indices.
The resulting family therefore packages as a Decomposition of exact size +2.
This module does not yet assert the endpoint vector or sharpness of Theorem B.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]
variable [Fintype V] [DecidableRel H.Adj]

/-- The old nonspoke contribution at a candidate index; added indices have none. -/
def retainedEdges (D : Decomposition H) (x : V) :
    Fin D.size ⊕ Fin 2 → List (Sym2 V)
  | .inl i => (D.path i).walk.edges.filter (fun e => decide (x ∉ e))
  | .inr _ => []

omit [Fintype V] [DecidableRel H.Adj] in
/-- Every retained contribution is an old graph edge missing the hub. -/
theorem retainedEdges_sound (D : Decomposition H) (x : V)
    (j : Fin D.size ⊕ Fin 2) (f : Sym2 V) (hf : f ∈ retainedEdges D x j) :
    f ∈ H.edgeSet ∧ x ∉ f := by
  rcases j with j | j
  · have he := List.mem_filter.mp hf
    exact ⟨(D.path j).walk.edges_subset_edgeSet he.1, of_decide_eq_true he.2⟩
  · exact False.elim (List.not_mem_nil hf)

omit [Fintype V] [DecidableRel H.Adj] in
/-- Old unique ownership survives filtering out all spokes. -/
theorem retainedEdges_unique (D : Decomposition H) (x : V) (f : Sym2 V)
    (hf : f ∈ H.edgeSet) (hx : x ∉ f) :
    ∃! j : Fin D.size ⊕ Fin 2, f ∈ retainedEdges D x j := by
  obtain ⟨i, hi, hu⟩ := D.covers f hf
  refine ⟨.inl i, List.mem_filter.mpr ⟨hi, decide_eq_true hx⟩, ?_⟩
  intro j hj
  rcases j with j | j
  · exact congrArg Sum.inl (hu j (List.mem_filter.mp hj).1)
  · exact False.elim (List.not_mem_nil hj)

/-- Every candidate edge belongs to exactly one of its retained/local contributions. -/
theorem expansionFamily_mem_edges (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (j : Fin D.size ⊕ Fin 2) (e : Sym2 (V ⊕ Fin 4)) :
    e ∈ (expansionFamily D x hd j).walk.edges ↔
      e ∈ (retainedEdges D x j).map (Sym2.map (oldHom H x)) ∨
      e ∈ (wordEdges (candidateWord D x hd j)).map
        (Sym2.map (label H x (D.fourNeighborEquiv x hd))) := by
  rcases j with j | j
  · exact (restoredOldCarrier_edge_partition D x hd j).mem_iff.trans List.mem_append
  · change e ∈ (addedCarrier D x hd j).walk.edges ↔ _
    rw [addedCarrier_edges]
    simp only [retainedEdges, List.map_nil, List.not_mem_nil, false_or]
    rfl

/-- On an old nonspoke, the candidate's local contribution is impossible. -/
theorem expansionFamily_retained_iff (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (j : Fin D.size ⊕ Fin 2) (f : Sym2 V) (hx : x ∉ f) :
    Sym2.map (oldHom H x) f ∈ (expansionFamily D x hd j).walk.edges ↔
      f ∈ retainedEdges D x j := by
  rw [expansionFamily_mem_edges]
  constructor
  · rintro (hr | hl)
    · obtain ⟨g, hg, he⟩ := List.mem_map.mp hr
      exact (Sym2.map.injective (oldHom_injective H x) he) ▸ hg
    · obtain ⟨g, hg, he⟩ := List.mem_map.mp hl
      exact False.elim (retained_not_active H x (D.fourNeighborEquiv x hd) f hx
        (List.mem_map.mpr ⟨g, candidateWord_active D x hd j g hg, he⟩))
  · intro hf
    exact Or.inl (List.mem_map.mpr ⟨f, hf, rfl⟩)

/-- On an active local edge, the retained contribution is impossible. -/
theorem expansionFamily_active_iff (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (j : Fin D.size ⊕ Fin 2) (e : Sym2 Vertex)
    (he : e ∈ activeEdges) :
    Sym2.map (label H x (D.fourNeighborEquiv x hd)) e ∈
        (expansionFamily D x hd j).walk.edges ↔
      e ∈ wordEdges (candidateWord D x hd j) := by
  rw [expansionFamily_mem_edges]
  constructor
  · rintro (hr | hl)
    · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hr
      exact False.elim (retained_not_active H x (D.fourNeighborEquiv x hd) f
        (retainedEdges_sound D x j f hf).2 (hfe.symm ▸ List.mem_map.mpr ⟨e, he, rfl⟩))
    · obtain ⟨f, hf, hfe⟩ := List.mem_map.mp hl
      exact (Sym2.map.injective (label_injective H x (D.fourNeighborEquiv x hd)) hfe) ▸ hf
  · intro hf
    exact Or.inr (List.mem_map.mpr ⟨e, hf, rfl⟩)

/-- The actual family covers every expanded edge exactly once. -/
theorem expansionFamily_covers (D : Decomposition H) (x : V) (hd : H.degree x = 4) :
    ∀ e ∈ (expansion H x).edgeSet,
      ∃! j, e ∈ (expansionFamily D x hd j).walk.edges := by
  intro e he
  rcases (expansion_edge_partition H x (D.fourNeighborEquiv x hd) e).mp he with hr | hl
  · obtain ⟨f, hf, hx, rfl⟩ := hr
    obtain ⟨i, hi, hu⟩ := retainedEdges_unique D x f hf hx
    refine ⟨i, (expansionFamily_retained_iff D x hd i f hx).mpr hi, ?_⟩
    intro j hj
    exact hu j ((expansionFamily_retained_iff D x hd j f hx).mp hj)
  · obtain ⟨f, hf, rfl⟩ := List.mem_map.mp hl
    obtain ⟨i, hi, hu⟩ := candidateWord_unique D x hd f hf
    refine ⟨i, (expansionFamily_active_iff D x hd i f hf).mpr hi, ?_⟩
    intro j hj
    exact hu j ((expansionFamily_active_iff D x hd j f hf).mp hj)

/-- Expand any actual input decomposition, with no coverage premise left to supply. -/
noncomputable def expandDecomposition (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : Decomposition (expansion H x) :=
  Decomposition.ofFamily (expansionFamily D x hd) (expansionFamily_covers D x hd)

/-- The constructed decomposition has exactly two additional nonempty simple paths. -/
@[simp] theorem expandDecomposition_size (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : (expandDecomposition D x hd).size = D.size + 2 := by
  rw [expandDecomposition, Decomposition.ofFamily_size, expansionFamily_index_card]

/-- A path-count budget on any degree-four-hub graph increases by at most two. -/
theorem expansion_hasPathBudget (x : V) (hd : H.degree x = 4) (k : ℕ)
    (hk : HasPathBudget H k) : HasPathBudget (expansion H x) (k + 2) := by
  obtain ⟨D, hD⟩ := hk
  exact ⟨expandDecomposition D x hd, by rw [expandDecomposition_size]; omega⟩

end Gallai.Star
