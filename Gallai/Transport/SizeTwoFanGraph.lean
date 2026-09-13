/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFanRestore

/-! # The restored Fan graph is exactly the original graph -/
namespace Gallai.WholeBowtie

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem sizeTwoFan_aux_le_original (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) : B.sizeTwoFanAux ≤ G := by
  have hp : G.Adj (B.label 0) (A 0).val :=
    B.completedLabel_target_edge A s(Star.Vertex.x,Star.Vertex.p) (by rw [hstate]; decide)
  have hq : G.Adj (B.label 0) (A 1).val :=
    B.completedLabel_target_edge A s(Star.Vertex.x,Star.Vertex.q) (by rw [hstate]; decide)
  intro u v ha
  rw [sizeTwoFanAux, SimpleGraph.map_adj] at ha
  obtain ⟨u',v',ha,rfl,rfl⟩ := ha
  change G.Adj u'.val v'.val
  rcases ha with ⟨ha,_,_⟩ | ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact ha
  · rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at hv
    rcases hv with hv | hv
    · simpa only [hu,hv] using hp
    · simpa only [hu,hv] using hq
  · rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at hu
    rcases hu with hu | hu
    · simpa only [hu,hv] using hp.symm
    · simpa only [hu,hv] using hq.symm

theorem sizeTwoFan_added_le_original (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state) : B.sizeTwoFanAdded A ≤ G := by
  intro u v ha
  rw [sizeTwoFanAdded, SimpleGraph.map_adj] at ha
  obtain ⟨u',v',ha,rfl,rfl⟩ := ha
  apply B.completedLabel_target_edge A s(u',v')
  rw [hstate,SizeTwo.Fan.target_partition]
  exact Finset.mem_union_left _ (Finset.mem_union_right _
    ((SizeTwo.Fan.initialGraph_edges _).mpr ha))

/-- The finite partition plus the retained nonspokes accounts for every
original edge; no original/synthetic edge convention is left implicit. -/
theorem sizeTwoFan_restored_eq_original (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) : B.sizeTwoFanRestored A = G := by
  have hxs : B.label 0 ≠ (A 3).val := B.label_ne_numberedAnchor A 0 3
  have hbs : B.label 2 ≠ (A 3).val := B.label_ne_numberedAnchor A 2 3
  have hbx : B.label 2 ≠ B.label 0 := fun h =>
    (by decide : (2 : Fin 5) ≠ 0) (B.label.injective h)
  have haux : B.sizeTwoFanAux ≤ B.sizeTwoFanRestored A :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_left))
  have hadd : B.sizeTwoFanAdded A ≤ B.sizeTwoFanRestored A :=
    le_sup_of_le_left (le_sup_of_le_left (le_sup_of_le_left le_sup_right))
  have hnewxs : (B.sizeTwoFanRestored A).Adj (B.label 0) (A 3).val :=
    Or.inl (Or.inl (Or.inr (by simp [SimpleGraph.edge_adj,hxs])))
  have hnewbx : (B.sizeTwoFanRestored A).Adj (B.label 2) (B.label 0) :=
    Or.inl (Or.inr (by simp [SimpleGraph.edge_adj,hbx]))
  have hnewbs : (B.sizeTwoFanRestored A).Adj (B.label 2) (A 3).val :=
    Or.inr (by simp [SimpleGraph.edge_adj,hbs])
  apply le_antisymm
  · apply sup_le
    · apply sup_le
      · apply sup_le
        · exact sup_le (B.sizeTwoFan_aux_le_original A hstate hSigma)
            (B.sizeTwoFan_added_le_original A hstate)
        · apply (SimpleGraph.edge_le_iff (G := G)).mpr
          exact Or.inr (B.completedLabel_target_edge A s(Star.Vertex.x,Star.Vertex.s)
            (by rw [hstate]; decide))
      · apply (SimpleGraph.edge_le_iff (G := G)).mpr
        exact Or.inr (B.completedLabel_target_edge A s(Star.Vertex.b,Star.Vertex.x)
          (by rw [hstate]; decide))
    · apply (SimpleGraph.edge_le_iff (G := G)).mpr
      exact Or.inr (B.completedLabel_target_edge A s(Star.Vertex.b,Star.Vertex.s)
        (by rw [hstate]; decide))
  · have hlocal (q : Sym2 Star.Vertex)
        (hq : q ∈ CompletedStar.targetEdges (B.completedStarState A)) :
        Sym2.map (B.completedLabel A) q ∈ (B.sizeTwoFanRestored A).edgeSet := by
      rw [hstate,SizeTwo.Fan.target_partition] at hq
      rcases Finset.mem_union.mp hq with hq | hq
      · rcases Finset.mem_union.mp hq with hq | hq
        · simp only [SizeTwo.Fan.retainedEdges,Finset.mem_insert,Finset.mem_singleton] at hq
          rcases hq with rfl | rfl
          · obtain ⟨f,hf,he⟩ := B.sizeTwo_spoke_has_preimage A hSigma 0 (Or.inl rfl)
            apply SimpleGraph.edgeSet_mono haux
            rw [sizeTwoFanAux,SimpleGraph.edgeSet_map]
            exact ⟨f,hf,he⟩
          · obtain ⟨f,hf,he⟩ := B.sizeTwo_spoke_has_preimage A hSigma 1 (Or.inr rfl)
            apply SimpleGraph.edgeSet_mono haux
            rw [sizeTwoFanAux,SimpleGraph.edgeSet_map]
            exact ⟨f,hf,he⟩
        · apply SimpleGraph.edgeSet_mono hadd
          rw [sizeTwoFanAdded,SimpleGraph.edgeSet_map]
          exact ⟨q,(SizeTwo.Fan.initialGraph_edges q).mp hq,rfl⟩
      · simp only [SizeTwo.Fan.restoredEdges,Finset.mem_insert,Finset.mem_singleton] at hq
        rcases hq with rfl | rfl | rfl
        · exact hnewxs
        · exact hnewbx
        · exact hnewbs
    intro u v huv
    change s(u,v) ∈ (B.sizeTwoFanRestored A).edgeSet
    rcases B.completed_edge_cases A s(u,v) huv with ⟨f,hf,hx,he⟩ | ⟨q,hq,he⟩
    · have hm : Sym2.map Subtype.val f ∈ (B.sizeTwoFanRestored A).edgeSet := by
        apply SimpleGraph.edgeSet_mono haux
        rw [sizeTwoFanAux,SimpleGraph.edgeSet_map]
        exact ⟨f,B.syndrome_contains_retained_nonspoke f hf hx,rfl⟩
      exact he ▸ hm
    · exact he ▸ hlocal q hq

end Gallai.WholeBowtie
