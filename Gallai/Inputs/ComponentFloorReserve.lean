/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ZeroSyndromeAssembly

/-! # One designated ceiling and non-SET floors on all other components -/
namespace Gallai

theorem endpoint_ceiling_of_other_components_not_set
    {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (y : W)
    (hp : 0 < H.degree y) (he : Even (H.degree y))
    (hcap : ∀ v, Even (H.degree v) → v ≠ y → eDegree H v ≤ 3)
    (hns : ∀ C : H.ConnectedComponent, y ∉ C.supp → ¬ IsSET (H.induce C.supp)) :
    ∃ D : Decomposition H, D.size ≤ (Fintype.card W + 1) / 2 ∧
      2 ≤ D.endpointCount y := by
  classical
  let C₀ := H.connectedComponentMk y
  let k (C : H.ConnectedComponent) :=
    if C = C₀ then (Fintype.card C.supp + 1) / 2 else Fintype.card C.supp / 2
  obtain ⟨D,hD,hy⟩ := component_endpoint_of_cap H y C₀ rfl hp he hcap
  obtain ⟨E,hE,hyE⟩ := endpoint_budget_of_components H y k D
    (by change D.size ≤ k C₀; simpa only [k,if_pos rfl] using hD) hy (by
      intro C hn
      change C ≠ C₀ at hn
      have hyC : y ∉ C.supp := fun h =>
        hn (SimpleGraph.ConnectedComponent.eq_of_common_vertex h rfl)
      have hclosed : ∀ v ∈ C.supp, H.neighborSet v ⊆ C.supp :=
        fun _ hv _ ha => C.mem_supp_of_adj_mem_supp hv ha
      have capC : ∀ v, Even ((H.induce C.supp).degree v) →
          eDegree (H.induce C.supp) v ≤ 3 := by
        intro v hv
        rw [eDegree_induce_of_closed H C.supp hclosed v]
        apply hcap v.val
        · rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v v.property)] at hv
        · intro h
          exact hyC (h ▸ v.property)
      rcases floor_or_set (H.induce C.supp) C.connected_toSimpleGraph capC with hb | hset
      · simpa only [k,if_neg hn] using hb
      · exact (hns C hyC hset).elim)
  have hcard : (∑ C : H.ConnectedComponent, Fintype.card C.supp) = Fintype.card W := by
    rw [← Fintype.card_sigma]
    exact Fintype.card_congr (Equiv.sigmaFiberEquiv H.connectedComponentMk)
  have hmul : 2 * (∑ C, k C) ≤ Fintype.card W + 1 := by
    rw [Finset.mul_sum]
    calc
      (∑ C, 2 * k C) ≤ ∑ C, (Fintype.card C.supp + if C = C₀ then 1 else 0) := by
        apply Finset.sum_le_sum
        intro C _
        by_cases h : C = C₀ <;> simp only [k,h,ite_true,ite_false] <;> omega
      _ = Fintype.card W + 1 := by rw [Finset.sum_add_distrib,hcard]; simp
  exact ⟨E,by omega,hyE⟩

end Gallai
