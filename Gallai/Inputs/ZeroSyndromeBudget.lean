/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Incidence
import Gallai.Structure.EvenSubgraphInduce
import Gallai.Inputs.OneException

/-! # Actual zero-syndrome puncture inputs

Whole deletion may disconnect the graph. Parity and E-degree bounds hold on
every retained vertex; the endpoint theorem is applied only to the actual
component of the designated vertex.
-/

namespace Gallai

/-- Restrict a one-exception endpoint input to the actual designated component. -/
theorem component_endpoint_of_cap {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (y : W)
    (C : H.ConnectedComponent) (hyC : y ∈ C.supp)
    (hp : 0 < H.degree y) (he : Even (H.degree y))
    (hcap : ∀ v, Even (H.degree v) → v ≠ y → eDegree H v ≤ 3) :
    ∃ D : Decomposition (H.induce C.supp),
      D.size ≤ (Fintype.card C.supp + 1) / 2 ∧
      2 ≤ D.endpointCount ⟨y, hyC⟩ := by
  classical
  have hclosed : ∀ v ∈ C.supp, H.neighborSet v ⊆ C.supp :=
    fun _ hv _ ha => C.mem_supp_of_adj_mem_supp hv ha
  have hd (v : C.supp) : (H.induce C.supp).degree v = H.degree v.val :=
    SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v v.property)
  apply one_exception_endpoint (H.induce C.supp) ⟨y, hyC⟩ C.connected_toSimpleGraph
    (by simpa only [hd] using hp) (by simpa only [hd] using he)
  intro v hv hne
  rw [eDegree_induce_of_closed H C.supp hclosed v]
  exact hcap v.val ((hd v) ▸ hv) (fun h => hne (Subtype.ext h))

namespace WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Whole deletion removes exactly five original vertices. -/
theorem puncture_card_add_five :
    Fintype.card {v : V // v ∉ B.vertices} + 5 = Fintype.card V := by
  have hs := Finset.card_le_univ B.vertices
  rw [B.card_vertices] at hs
  simp only [Fintype.card_subtype_compl, Fintype.card_coe, B.card_vertices]
  omega

/-- Empty syndrome preserves every retained degree parity. -/
theorem zero_puncture_even_iff (hz : B.syndrome = ∅)
    (v : {v : V // v ∉ B.vertices}) :
    Even (B.puncture.degree v) ↔ Even (G.degree v.val) := by
  have hp := (B.puncture_parity_eq_iff v).mpr (by simp [hz])
  simp only [Nat.even_iff, hp]

/-- Every actual anchor still supplies an odd endpoint in the puncture. -/
theorem zero_puncture_anchor_odd (hz : B.syndrome = ∅)
    (v : {v : V // v ∉ B.vertices}) (hv : v.val ∈ B.anchors) :
    Odd (B.puncture.degree v) := by
  apply Nat.not_even_iff_odd.mp
  intro he
  exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hv)
    ((B.zero_puncture_even_iff hz v).mp he)

/-- A retained even vertex has no incidence into the deleted even component. -/
theorem puncture_degree_of_even (v : {v : V // v ∉ B.vertices})
    (hv : Even (G.degree v.val)) : B.puncture.degree v = G.degree v.val := by
  have hz : B.columnCount v.val = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro i hi
    have ha : v.val ∈ B.anchors :=
      (B.mem_anchors _).mpr ⟨i, (Finset.mem_filter.mp hi).2⟩
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor ha) hv
  have h := B.puncture_degree_add_column v
  simpa only [hz, Nat.add_zero] using h

/-- No retained vertex gains an even neighbour under zero-syndrome deletion. -/
theorem zero_puncture_eDegree_le (hz : B.syndrome = ∅)
    (v : {v : V // v ∉ B.vertices}) : eDegree B.puncture v ≤ eDegree G v.val := by
  have hs : (evenNeighbors B.puncture v).map (Function.Embedding.subtype _) ⊆
      evenNeighbors G v.val := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hq
    exact (mem_evenNeighbors _ _).mpr
      ⟨ha, (B.zero_puncture_even_iff hz q).mp he⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hs

/-- The designated component has its own ceiling budget and two exposed ends.
No connectivity assumption is made on the entire puncture. -/
theorem zero_puncture_component_endpoint (hz : B.syndrome = ∅) (hc : G.Connected)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (C : B.puncture.ConnectedComponent) (hyC : y ∈ C.supp)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.puncture.induce C.supp),
      D.size ≤ (Fintype.card C.supp + 1) / 2 ∧
      2 ≤ D.endpointCount ⟨y, hyC⟩ := by
  classical
  have hyx : y.val ≠ B.label 0 := by
    intro he
    apply y.property
    rw [he]
    exact (B.mem_vertices _).mpr (B.label_mem_component 0)
  have : Nontrivial V := ⟨⟨y.val, B.label 0, hyx⟩⟩
  have hp : 0 < B.puncture.degree y := by
    rw [B.puncture_degree_of_even y hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  have he : Even (B.puncture.degree y) := by
    rw [B.puncture_degree_of_even y hy]
    exact hy
  apply component_endpoint_of_cap B.puncture y C hyC hp he
  intro v hv hne
  apply (B.zero_puncture_eDegree_le hz v).trans
  apply hcap v.val
  · exact (B.zero_puncture_even_iff hz v).mp hv
  · intro hx
    apply v.property
    rw [hx]
    exact (B.mem_vertices _).mpr (B.label_mem_component 0)
  · intro hyv
    exact hne (Subtype.ext hyv)

end WholeBowtie
end Gallai
