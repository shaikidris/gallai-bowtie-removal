/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Edges

/-!
# The complete candidate family for star expansion

Every old carrier retains its index, whether unchanged or restored. Two
new indices contain the two added certificate paths. The local edge-accounting
theorem below does not yet supply unique global coverage.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]
variable [Fintype V] [DecidableRel H.Adj]

/-- Keep an old carrier's index, replacing its hub run when present. -/
noncomputable def restoredOldCarrier (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) : NonemptyPath (expansion H x) :=
  if ht : i ∈ D.terminalCarriers x then assignedTerminal D x hd ⟨i, ht⟩
  else if hp : i ∈ D.throughCarriers x then assignedThrough D x hd ⟨i, hp⟩
  else (D.path i).map (oldHom H x) (oldHom_injective H x)

/-- The old index of a terminal carrier selects its automatic terminal restoration. -/
theorem restoredOldCarrier_of_terminal (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) (ht : i ∈ D.terminalCarriers x) :
    restoredOldCarrier D x hd i = assignedTerminal D x hd ⟨i, ht⟩ := dif_pos ht

/-- The old index of a through carrier selects its automatic through restoration. -/
theorem restoredOldCarrier_of_through (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) (ht : i ∉ D.terminalCarriers x)
    (hp : i ∈ D.throughCarriers x) :
    restoredOldCarrier D x hd i = assignedThrough D x hd ⟨i, hp⟩ := by
  exact (dif_neg ht).trans (dif_pos hp)

/-- A carrier missing the hub is included without changing its vertex sequence. -/
theorem restoredOldCarrier_of_unaffected (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) (ht : i ∉ D.terminalCarriers x)
    (hp : i ∉ D.throughCarriers x) :
    restoredOldCarrier D x hd i = (D.path i).map (oldHom H x) (oldHom_injective H x) := by
  exact (dif_neg ht).trans (dif_neg hp)

/-- The local word assigned to an old carrier; empty when it misses the hub. -/
noncomputable def assignedWord (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) : List Vertex :=
  if ht : i ∈ D.terminalCarriers x then
    (profileOf D x).terminalWord (terminalNumber D x hd ⟨i, ht⟩)
  else if hp : i ∈ D.throughCarriers x then
    (profileOf D x).throughWord (throughNumber D x hd ⟨i, hp⟩)
  else []

/-- A carrier missing the hub has no local connector contribution. -/
theorem assignedWord_of_unaffected (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) (ht : i ∉ D.terminalCarriers x)
    (hp : i ∉ D.throughCarriers x) : assignedWord D x hd i = [] :=
  (dif_neg ht).trans (dif_neg hp)

/-- Each indexed old carrier contributes exactly its retained edges and its connector. -/
theorem restoredOldCarrier_edge_partition (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) :
    (restoredOldCarrier D x hd i).walk.edges.Perm
      (((D.path i).walk.edges.filter (fun e => decide (x ∉ e))).map
        (Sym2.map (oldHom H x)) ++
      (wordEdges (assignedWord D x hd i)).map
        (Sym2.map (label H x (D.fourNeighborEquiv x hd)))) := by
  by_cases ht : i ∈ D.terminalCarriers x
  · rw [restoredOldCarrier_of_terminal D x hd i ht]
    simpa only [assignedWord, dif_pos ht] using
      assignedTerminal_edge_partition D x hd ⟨i, ht⟩
  by_cases hp : i ∈ D.throughCarriers x
  · rw [restoredOldCarrier_of_through D x hd i ht hp]
    simpa only [assignedWord, dif_neg ht, dif_pos hp] using
      assignedThrough_edge_partition D x hd ⟨i, hp⟩
  · have hx : x ∉ (D.path i).walk.support := by
      rw [D.mem_support_iff_terminal_or_through x i]
      exact not_or.mpr ⟨ht, hp⟩
    rw [restoredOldCarrier_of_unaffected D x hd i ht hp]
    simp only [assignedWord, dif_neg ht, dif_neg hp]
    rw [hubFree_filter _ x hx, NonemptyPath.map_edges]
    simp [wordEdges]

/-- Realize either of the two added paths in the chosen profile. -/
noncomputable def addedCarrier (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin 2) : NonemptyPath (expansion H x) := by
  let p := profileOf D x
  have hi : i.val < p.added.length := by rw [p.valid.2.1]; exact i.isLt
  exact p.valid.realize H x (D.fourNeighborEquiv x hd) (p.added[i.val]'hi)
    (List.mem_append_right _ (List.getElem_mem hi))

/-- Actual old and new paths, with no assumed choice of a compatible family. -/
noncomputable def expansionFamily (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : Fin D.size ⊕ Fin 2 → NonemptyPath (expansion H x)
  | .inl i => restoredOldCarrier D x hd i
  | .inr i => addedCarrier D x hd i

omit [DecidableEq V] [Fintype V] [DecidableRel H.Adj] in
/-- The candidate has precisely the desired number of indices, before coverage is proved. -/
theorem expansionFamily_index_card (D : Decomposition H) :
    Fintype.card (Fin D.size ⊕ Fin 2) = D.size + 2 := by simp

/-- The added carrier contributes exactly its checked local edge list. -/
theorem addedCarrier_edges (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin 2) :
    (addedCarrier D x hd i).walk.edges =
      (wordEdges ((profileOf D x).added[i.val]'(by
        rw [(profileOf D x).valid.2.1]; exact i.isLt))).map
          (Sym2.map (label H x (D.fourNeighborEquiv x hd))) := by
  unfold addedCarrier
  exact Valid.realize_edges _ _ _ _ _ _

end Gallai.Star
