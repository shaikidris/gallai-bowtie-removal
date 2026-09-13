/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.SyndromeStarBudget
import Gallai.Structure.SET

/-! # SET components of the syndrome star are remote from the hub -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- No SET component contains the retained hub: all its neighbours are odd. -/
theorem syndromeStar_set_excludes_hub (C : B.syndromeStar.ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hC : IsSET (B.syndromeStar.induce C.supp)) :
    B.completedHub ∉ C.supp := by
  classical
  intro hx
  have hc : ∀ v ∈ C.supp, B.syndromeStar.neighborSet v ⊆ C.supp :=
    fun _ hv _ hw => C.mem_supp_of_adj_mem_supp hv hw
  have hp : 0 < (evenNeighbors (B.syndromeStar.induce C.supp)
      ⟨B.completedHub,hx⟩).card := by
    rcases hC.eDegree_two_or_three ⟨B.completedHub,hx⟩ with h | h <;>
      unfold eDegree at h <;> omega
  obtain ⟨w,hw⟩ := Finset.card_pos.mp hp
  obtain ⟨ha,he⟩ := (mem_evenNeighbors _ _).mp hw
  rw [SimpleGraph.degree_induce_of_neighborSet_subset (hc w w.property)] at he
  have hs := (B.syndromeStar_hub_adj w.val).mp ha
  exact (Nat.not_even_iff_odd.mpr
    (B.odd_degree_anchor (B.syndrome_subset_anchors hs)))
    ((B.syndromeStar_even_iff w.val).mp he)

/-- A SET component meets an odd anchor outside the syndrome, and therefore
outside the hub component. This supplies the location for the reserve lemma. -/
theorem syndromeStar_set_remote_anchor (hc : G.Connected)
    (hs : B.syndrome.Nonempty) (C : B.syndromeStar.ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hC : IsSET (B.syndromeStar.induce C.supp)) :
    ∃ w : B.StarSurvivor, w ∈ C.supp ∧ w.val ∈ B.anchors ∧
      w.val ∉ B.syndrome ∧ Odd (B.syndromeStar.degree w) := by
  classical
  obtain ⟨w,hw,hA⟩ := B.syndromeStar_component_anchor hc hs C
  refine ⟨w,hw,hA,?_,?_⟩
  · intro hS
    exact B.syndromeStar_set_excludes_hub C hC
      (C.mem_supp_of_adj_mem_supp hw ((B.syndromeStar_hub_adj w).mpr hS).symm)
  · apply Nat.not_even_iff_odd.mp
    intro he
    exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hA))
      ((B.syndromeStar_even_iff w).mp he)

/-- A remote SET component supplies a ceiling decomposition with three
endpoints at an anchor outside the syndrome. -/
theorem syndromeStar_set_remote_reserve (hc : G.Connected)
    (hs : B.syndrome.Nonempty) (C : B.syndromeStar.ConnectedComponent)
    [DecidablePred (· ∈ C.supp)] (hC : IsSET (B.syndromeStar.induce C.supp)) :
    ∃ w : C.supp, w.val.val ∈ B.anchors ∧ w.val.val ∉ B.syndrome ∧
      ∃ D : Decomposition (B.syndromeStar.induce C.supp),
        D.size ≤ (Fintype.card C.supp + 1) / 2 ∧ 3 ≤ D.endpointCount w := by
  classical
  obtain ⟨w,hw,hA,hsw,ho⟩ := B.syndromeStar_set_remote_anchor hc hs C hC
  obtain ⟨D,hD,he⟩ := hC.endpoint_reserve ⟨w,hw⟩
  refine ⟨⟨w,hw⟩,hA,hsw,D,hD,?_⟩
  apply D.three_le_endpointCount_of_odd_degree _ ?_ he
  have hclosed : B.syndromeStar.neighborSet w ⊆ C.supp :=
    fun _ ha => C.mem_supp_of_adj_mem_supp hw ha
  rw [SimpleGraph.degree_induce_of_neighborSet_subset hclosed]
  exact ho

end Gallai.WholeBowtie
