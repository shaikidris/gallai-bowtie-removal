/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarFamily

/-! # Unique local ownership at the actual sparse carrier indices

Every accepted word occurrence corresponds to exactly one used old carrier
or one added carrier. Unaffected carriers contribute no local edges.
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

/-- The actual occurrences that consume local words, including added paths. -/
abbrev CompletedUsedCarrier (n : ℕ) :=
  (D.TerminalIndex B.completedHub ⊕ D.ThroughIndex B.completedHub) ⊕ Fin n

/-- The record's ordered words biject with actual used carrier occurrences. -/
noncomputable def completedUsedNumber :
    B.CompletedUsedCarrier D added.length ≃ Fin (replacements ++ added).length :=
  (Equiv.sumCongr
    ((B.completedCarrierRoleEquiv D hfour).trans (finCongr h.replacements_length.symm))
    (Equiv.refl _)).trans (finSumFinEquiv.trans (finCongr List.length_append.symm))

/-- Used occurrences retain their original family indices. -/
def completedUsedCarrier (n : ℕ) :
    B.CompletedUsedCarrier D n → Fin D.size ⊕ Fin n
  | .inl (.inl i) => .inl i.val
  | .inl (.inr i) => .inl i.val
  | .inr i => .inr i

theorem completedUsedCarrier_injective (n : ℕ) :
    Function.Injective (B.completedUsedCarrier D n) := by
  intro i j hij
  rcases i with (i | i) | i <;> rcases j with (j | j) | j
  all_goals simp only [completedUsedCarrier] at hij
  · exact congrArg (fun k => Sum.inl (Sum.inl k)) (Subtype.ext (Sum.inl.inj hij))
  · have hv := Sum.inl.inj hij
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through B.completedHub))
      (hv ▸ i.property) j.property)
  · cases hij
  · have hv := Sum.inl.inj hij
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through B.completedHub))
      j.property (hv ▸ i.property))
  · exact congrArg (fun k => Sum.inl (Sum.inr k)) (Subtype.ext (Sum.inl.inj hij))
  · cases hij
  · cases hij
  · cases hij
  · exact congrArg Sum.inr (Sum.inr.inj hij)

theorem completedUsedNumber_old
    (i : D.TerminalIndex B.completedHub ⊕ D.ThroughIndex B.completedHub) :
    B.completedUsedNumber D hfour h (.inl i) = B.completedAssignedIndex D hfour h i := by
  apply Fin.ext
  rfl

theorem completedUsedNumber_added (i : Fin added.length) :
    B.completedUsedNumber D hfour h (.inr i) = addedWordIndex replacements added i := by
  apply Fin.ext
  rfl

/-- Local word contributed at every old or added family index. -/
noncomputable def completedCandidateWord : Fin D.size ⊕ Fin added.length → List Star.Vertex
  | .inl i => B.completedAssignedWord D hfour h i
  | .inr i => added[i]

theorem completedCandidateWord_used (i : B.CompletedUsedCarrier D added.length) :
    B.completedCandidateWord D hfour h (B.completedUsedCarrier D added.length i) =
      (replacements ++ added)[B.completedUsedNumber D hfour h i] := by
  rcases i with (i | i) | i
  · simp only [completedCandidateWord, completedUsedCarrier, completedAssignedWord,
      dif_pos i.property, B.completedUsedNumber_old]
  · have ht : i.val ∉ D.terminalCarriers B.completedHub := fun ht =>
      (Finset.disjoint_left.mp (D.disjoint_terminal_through B.completedHub)) ht i.property
    simp only [completedCandidateWord, completedUsedCarrier, completedAssignedWord,
      dif_neg ht, dif_pos i.property, B.completedUsedNumber_old]
  · simp only [completedCandidateWord, completedUsedCarrier,
      B.completedUsedNumber_added, addedWordIndex_get]

theorem completedCandidateWord_owner (j : Fin D.size ⊕ Fin added.length) (e : Sym2 Star.Vertex)
    (he : e ∈ Certificate.wordEdges (B.completedCandidateWord D hfour h j)) :
    ∃ i : B.CompletedUsedCarrier D added.length, B.completedUsedCarrier D added.length i = j := by
  rcases j with j | j
  · by_cases ht : j ∈ D.terminalCarriers B.completedHub
    · exact ⟨.inl (.inl ⟨j, ht⟩), rfl⟩
    by_cases hp : j ∈ D.throughCarriers B.completedHub
    · exact ⟨.inl (.inr ⟨j, hp⟩), rfl⟩
    · simp only [completedCandidateWord, completedAssignedWord, dif_neg ht, dif_neg hp,
        Certificate.wordEdges, List.tail_nil, List.zipWith_nil_left, List.not_mem_nil] at he
  · exact ⟨.inr j, rfl⟩

theorem completedCandidateWord_unique (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState (B.carrierAnchorOrder D hfour))) :
    ∃! j : Fin D.size ⊕ Fin added.length,
      e ∈ Certificate.wordEdges (B.completedCandidateWord D hfour h j) := by
  let state := B.completedStarState (B.carrierAnchorOrder D hfour)
  let L := h.1.toDecomposition (graph state) (graph_edges state)
  have hl : ∃! i : Fin (replacements ++ added).length,
      e ∈ Certificate.wordEdges (replacements ++ added)[i] := by
    have hc := L.covers e ((graph_edges state e).mp he)
    simpa only [L, Certificate.Accepted.toDecomposition, Decomposition.ofEdgeCounts,
      Certificate.Accepted.realize_edges] using hc
  obtain ⟨i, hi, hu⟩ := hl
  let k := (B.completedUsedNumber D hfour h).symm i
  refine ⟨B.completedUsedCarrier D added.length k, ?_, ?_⟩
  · change e ∈ Certificate.wordEdges
      (B.completedCandidateWord D hfour h (B.completedUsedCarrier D added.length k))
    rw [B.completedCandidateWord_used]
    simpa only [k, Equiv.apply_symm_apply] using hi
  · intro j hj
    obtain ⟨l, rfl⟩ := B.completedCandidateWord_owner D hfour h j e hj
    rw [B.completedCandidateWord_used] at hj
    have heq : l = k := (B.completedUsedNumber D hfour h).injective
      ((hu _ hj).trans (Equiv.apply_symm_apply _ i).symm)
    exact congrArg (B.completedUsedCarrier D added.length) heq

theorem completedCandidateWord_target (j : Fin D.size ⊕ Fin added.length) (e : Sym2 Star.Vertex)
    (he : e ∈ Certificate.wordEdges (B.completedCandidateWord D hfour h j)) :
    e ∈ targetEdges (B.completedStarState (B.carrierAnchorOrder D hfour)) := by
  obtain ⟨i, rfl⟩ := B.completedCandidateWord_owner D hfour h j e he
  rw [B.completedCandidateWord_used] at he
  change e ∈ (targetEdges (B.completedStarState (B.carrierAnchorOrder D hfour))).val
  rw [← h.1.2]
  exact List.mem_flatMap.mpr ⟨_, List.getElem_mem _, he⟩

end Gallai.WholeBowtie
