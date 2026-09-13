/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PeelingPuncture
import Gallai.Structure.EdgePunctureComponents
import Gallai.Structure.EvenSubgraphInduce
import Gallai.Inputs.FloorOrSET

/-! # Floor budgets away from the exposed peeling component -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

open scoped Finset

/-- Every component not containing y in a peeling puncture has a floor budget
when the peeled hub has at least four even neighbours. The SET exclusion uses
four surviving even neighbours on the x-side or an E-isolated even w. -/
theorem peeling_other_component_floor (x y w : V) (hc : G.Connected)
    (hxw : G.Adj x w) (hx : Even (G.degree x)) (hw : Odd (G.degree w))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3)
    (hlarge : 4 ≤ eDegree G x) (C : (G.deleteEdges {s(x, w)}).ConnectedComponent)
    (hyC : y ∉ C.supp) :
    HasPathBudget ((G.deleteEdges {s(x, w)}).induce C.supp) (Fintype.card C.supp / 2) := by
  classical
  let H := G.deleteEdges {s(x, w)}
  have hclosed : ∀ v ∈ C.supp, H.neighborSet v ⊆ C.supp :=
    fun _ hv _ ha => C.mem_supp_of_adj_mem_supp hv ha
  have hdeg (v : C.supp) : (H.induce C.supp).degree v = H.degree v.val :=
    SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v v.property)
  have hcaps := odd_neighbor_peeling_cap x y w hxw hx hw hcontact hcap
  have hcapC : ∀ v, Even ((H.induce C.supp).degree v) →
      eDegree (H.induce C.supp) v ≤ 3 := by
    intro v hev
    rw [eDegree_induce_of_closed H C.supp hclosed v]
    exact hcaps v.val ((hdeg v) ▸ hev) (fun heq => hyC (heq ▸ v.property))
  rcases floor_or_set (H.induce C.supp) C.connected_toSimpleGraph hcapC with hfloor | hset
  · exact hfloor
  exfalso
  rcases component_contains_deleted_endpoint hc x w hxw C with hxC | hwC
  · have hsub : evenNeighbors G x ⊆
        (Finset.univ.filter (fun v : C.supp => Even ((H.induce C.supp).degree v))).map
          (Function.Embedding.subtype _) := by
      intro v hv
      obtain ⟨ha, hev⟩ := (mem_evenNeighbors x v).mp hv
      have hvw : v ≠ w := by
        rintro rfl
        exact Nat.not_even_iff_odd.mpr hw hev
      have hret : H.Adj x v := by
        apply SimpleGraph.deleteEdges_adj.mpr
        exact ⟨ha, by simp [hvw, ha.ne.symm]⟩
      have hvC : v ∈ C.supp := C.mem_supp_of_adj_mem_supp hxC hret
      have heH : Even (H.degree v) :=
        (degree_delete_edge_of_ne G x w v ha.ne.symm hvw).symm ▸ hev
      refine Finset.mem_map.mpr ⟨⟨v, hvC⟩, ?_, rfl⟩
      simpa only [Finset.mem_filter, Finset.mem_univ, true_and, hdeg] using heH
    have hn : eDegree G x ≤ 3 := by
      calc
        eDegree G x ≤ #((Finset.univ.filter
          (fun v : C.supp => Even ((H.induce C.supp).degree v))).map
            (Function.Embedding.subtype _)) := Finset.card_le_card hsub
        _ = 3 := by rw [Finset.card_map, hset.card_even]
    omega
  · have hew : Even ((H.induce C.supp).degree ⟨w, hwC⟩) := by
      rw [hdeg]
      exact (odd_neighbor_peeling_parity x w hxw hx hw).2.1
    have hzero : eDegree (H.induce C.supp) ⟨w, hwC⟩ = 0 := by
      apply Finset.card_eq_zero.mpr
      apply Finset.eq_empty_iff_forall_notMem.mpr
      intro v hv
      obtain ⟨ha, hev⟩ :=
        (mem_evenNeighbors (G := H.induce C.supp) (⟨w, hwC⟩ : C.supp) v).mp hv
      have hvy : v.val ≠ y := fun heq => hyC (heq ▸ v.property)
      have ho := odd_neighbor_peeling_neighbors x y w hcontact v.val ha hvy
      exact Nat.not_even_iff_odd.mpr ho ((hdeg v) ▸ hev)
    have htwo := hset.eDegree_even ⟨w, hwC⟩ hew
    omega

end Gallai
