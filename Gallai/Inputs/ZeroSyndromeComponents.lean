/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.ZeroSyndromeBudget
import Gallai.Inputs.FloorOrSET
import Gallai.Inputs.SETReserve

/-! # Ceiling supply for every off-designated puncture component

The floor-or-SET alternative is retained. SET components use their proved
ceiling decomposition; they are not silently given a floor budget.
-/

namespace Gallai

/-- The floor-or-SET theorem supplies a ceiling budget, including singletons. -/
theorem ceiling_of_even_degree_cap {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (hc : H.Connected)
    (hcap : ∀ v, Even (H.degree v) → eDegree H v ≤ 3) :
    HasPathBudget H ((Fintype.card W + 1) / 2) := by
  classical
  rcases floor_or_set H hc hcap with ⟨D, hD⟩ | hset
  · exact ⟨D, hD.trans (by omega)⟩
  let u : W := Classical.choice hc.nonempty
  obtain ⟨D, hD, _⟩ := hset.endpoint_reserve u
  exact ⟨D, hD⟩

/-- An actual component away from the exception inherits a ceiling budget. -/
theorem other_component_ceiling {W : Type*} [Fintype W] [DecidableEq W]
    (H : SimpleGraph W) [DecidableRel H.Adj] (y : W)
    (C : H.ConnectedComponent) (hyC : y ∉ C.supp)
    (hcap : ∀ v, Even (H.degree v) → v ≠ y → eDegree H v ≤ 3) :
    HasPathBudget (H.induce C.supp) ((Fintype.card C.supp + 1) / 2) := by
  classical
  have hclosed : ∀ v ∈ C.supp, H.neighborSet v ⊆ C.supp :=
    fun _ hv _ ha => C.mem_supp_of_adj_mem_supp hv ha
  apply ceiling_of_even_degree_cap (H.induce C.supp) C.connected_toSimpleGraph
  intro v hv
  rw [eDegree_induce_of_closed H C.supp hclosed v]
  apply hcap v.val
  · rwa [SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v v.property)] at hv
  · intro heq
    exact hyC (heq ▸ v.property)

namespace WholeBowtie

open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every component away from y in the actual zero-syndrome deletion is supplied. -/
theorem zero_puncture_other_ceiling (hz : B.syndrome = ∅)
    (y : {v : V // v ∉ B.vertices}) (C : B.puncture.ConnectedComponent)
    (hyC : y ∉ C.supp)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    HasPathBudget (B.puncture.induce C.supp) ((Fintype.card C.supp + 1) / 2) := by
  apply other_component_ceiling B.puncture y C hyC
  intro v hv hne
  apply (B.zero_puncture_eDegree_le hz v).trans
  apply hcap v.val ((B.zero_puncture_even_iff hz v).mp hv)
  · intro hx
    apply v.property
    rw [hx]
    exact (B.mem_vertices _).mpr (B.label_mem_component 0)
  · intro heq
    exact hne (Subtype.ext heq)

end WholeBowtie
end Gallai
