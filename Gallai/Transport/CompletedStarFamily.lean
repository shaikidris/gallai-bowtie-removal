/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarAssigned

/-! # The actual family selected by a completed-star record

Each old path retains one index, regardless of its hub profile. Added record
words get separate new indices. The family is constructed here with its
path budget and endpoint reserve; unique global coverage is proved separately.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (D : Decomposition B.completedStar) (hfour : #B.anchors = 4)
variable {replacements added : List (List Star.Vertex)}
variable (h : AcceptedRecord (B.completedStarState (B.carrierAnchorOrder D hfour))
  (profileInterface (Star.profileOf D B.completedHub)) replacements added)

/-- Retain every original carrier index and replace its run if it meets the hub. -/
noncomputable def completedRestoredOld (i : Fin D.size) : NonemptyPath G :=
  if ht : i ∈ D.terminalCarriers B.completedHub then
    B.completedAssignedTerminal D hfour h ⟨i, ht⟩
  else if hp : i ∈ D.throughCarriers B.completedHub then
    B.completedAssignedThrough D hfour h ⟨i, hp⟩
  else B.completedAvoidingPath (D.path i) (by
    rw [D.mem_support_iff_terminal_or_through B.completedHub i]
    exact not_or.mpr ⟨ht, hp⟩)

/-- Exactly the local replacement attached to an old carrier; empty if untouched. -/
noncomputable def completedAssignedWord (i : Fin D.size) : List Star.Vertex :=
  if ht : i ∈ D.terminalCarriers B.completedHub then
    (replacements ++ added)[B.completedAssignedIndex D hfour h (.inl ⟨i, ht⟩)]
  else if hp : i ∈ D.throughCarriers B.completedHub then
    (replacements ++ added)[B.completedAssignedIndex D hfour h (.inr ⟨i, hp⟩)]
  else []

theorem completedRestoredOld_terminal (i : Fin D.size)
    (ht : i ∈ D.terminalCarriers B.completedHub) :
    B.completedRestoredOld D hfour h i = B.completedAssignedTerminal D hfour h ⟨i, ht⟩ := by
  unfold completedRestoredOld
  exact dif_pos ht

theorem completedRestoredOld_through (i : Fin D.size)
    (ht : i ∉ D.terminalCarriers B.completedHub)
    (hp : i ∈ D.throughCarriers B.completedHub) :
    B.completedRestoredOld D hfour h i = B.completedAssignedThrough D hfour h ⟨i, hp⟩ := by
  unfold completedRestoredOld
  exact (dif_neg ht).trans (dif_pos hp)

theorem completedRestoredOld_avoiding (i : Fin D.size)
    (ht : i ∉ D.terminalCarriers B.completedHub)
    (hp : i ∉ D.throughCarriers B.completedHub)
    (hx : B.completedHub ∉ (D.path i).walk.support) :
    B.completedRestoredOld D hfour h i = B.completedAvoidingPath (D.path i) hx := by
  unfold completedRestoredOld
  exact (dif_neg ht).trans (dif_neg hp)

theorem completedRestoredOld_edge_partition (i : Fin D.size) :
    (B.completedRestoredOld D hfour h i).walk.edges.Perm
      (((D.path i).walk.edges.filter (fun e => decide (B.completedHub ∉ e))).map
        (Sym2.map Subtype.val) ++
      (Certificate.wordEdges (B.completedAssignedWord D hfour h i)).map
        (Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour)))) := by
  by_cases ht : i ∈ D.terminalCarriers B.completedHub
  · rw [B.completedRestoredOld_terminal D hfour h i ht]
    simpa only [completedAssignedWord, dif_pos ht] using
      B.completedAssignedTerminal_edge_partition D hfour h ⟨i, ht⟩
  by_cases hp : i ∈ D.throughCarriers B.completedHub
  · rw [B.completedRestoredOld_through D hfour h i ht hp]
    simpa only [completedAssignedWord, dif_neg ht, dif_pos hp] using
      B.completedAssignedThrough_edge_partition D hfour h ⟨i, hp⟩
  · have hx : B.completedHub ∉ (D.path i).walk.support := by
      rw [D.mem_support_iff_terminal_or_through B.completedHub i]
      exact not_or.mpr ⟨ht, hp⟩
    rw [B.completedRestoredOld_avoiding D hfour h i ht hp hx]
    simp only [completedAssignedWord, dif_neg ht, dif_neg hp,
      B.completedAvoidingPath_edges, Star.hubFree_filter _ B.completedHub hx,
      Certificate.wordEdges, List.tail_nil, List.zipWith_nil_left, List.map_nil, List.append_nil]
    exact List.Perm.refl _

theorem completedRestoredOld_endpoint_contribution (i : Fin D.size)
    (w : B.StarSurvivor) (hw : w.val ∉ B.vertices) :
    ((if (B.completedRestoredOld D hfour h i).start = w.val then 1 else 0) +
      (if (B.completedRestoredOld D hfour h i).finish = w.val then 1 else 0 : ℕ)) =
      ((if (D.path i).start = w then 1 else 0) +
        (if (D.path i).finish = w then 1 else 0)) := by
  by_cases ht : i ∈ D.terminalCarriers B.completedHub
  · simpa only [completedRestoredOld, dif_pos ht] using
      B.completedAssignedTerminal_endpoint_contribution D hfour h ⟨i, ht⟩ w hw
  by_cases hp : i ∈ D.throughCarriers B.completedHub
  · simpa only [completedRestoredOld, dif_neg ht, dif_pos hp] using
      B.completedAssignedThrough_endpoint_contribution D hfour h ⟨i, hp⟩ w
  · simp only [completedRestoredOld, dif_neg ht, dif_neg hp]
    exact B.completedAvoidingPath_endpoint_contribution _ _ w

/-- Each added word is realized in the original graph using the same row coordinates. -/
noncomputable def completedAddedCarrier (i : Fin added.length) : NonemptyPath G :=
  B.realizeCompletedWord (B.carrierAnchorOrder D hfour) (replacements ++ added) h.1
    (addedWordIndex replacements added i)

theorem completedAddedCarrier_edges (i : Fin added.length) :
    (B.completedAddedCarrier D hfour h i).walk.edges =
      (Certificate.wordEdges added[i]).map
        (Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour))) := by
  unfold completedAddedCarrier
  rw [B.realizeCompletedWord_edges, addedWordIndex_get]

/-- A concrete candidate family, with all paths simple and nonempty by construction. -/
noncomputable def completedFamily : Fin D.size ⊕ Fin added.length → NonemptyPath G
  | .inl i => B.completedRestoredOld D hfour h i
  | .inr i => B.completedAddedCarrier D hfour h i

include h in
/-- The actual family index count meets the two-new-path budget of the record. -/
theorem completedFamily_index_budget :
    Fintype.card (Fin D.size ⊕ Fin added.length) ≤ D.size + 2 := by
  simpa only [Fintype.card_sum, Fintype.card_fin] using Nat.add_le_add_left h.2.2.1 D.size

/-- Summing the old carrier contributions preserves every outside endpoint reserve. -/
theorem completedFamily_endpoint_reserve (w : B.StarSurvivor) (hw : w.val ∉ B.vertices) :
    D.endpointCount w ≤ ∑ i : Fin D.size ⊕ Fin added.length,
      ((if (B.completedFamily D hfour h i).start = w.val then 1 else 0) +
        (if (B.completedFamily D hfour h i).finish = w.val then 1 else 0 : ℕ)) := by
  rw [Fintype.sum_sum_type]
  have he : (∑ i : Fin D.size,
      ((if (B.completedRestoredOld D hfour h i).start = w.val then 1 else 0) +
        (if (B.completedRestoredOld D hfour h i).finish = w.val then 1 else 0 : ℕ))) =
      D.endpointCount w := Finset.sum_congr rfl (fun i _ =>
        B.completedRestoredOld_endpoint_contribution D hfour h i w hw)
  change D.endpointCount w ≤ (∑ i : Fin D.size,
      ((if (B.completedRestoredOld D hfour h i).start = w.val then 1 else 0) +
        (if (B.completedRestoredOld D hfour h i).finish = w.val then 1 else 0 : ℕ))) + _
  rw [he]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
