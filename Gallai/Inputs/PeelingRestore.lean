/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PeelingPuncture
import Gallai.Inputs.SingleEdge
import Gallai.Foundations.EndpointBounds

/-! # Same-count restoration after odd-neighbour peeling

The second exception's exposure prevents it from being a passing neighbour.
Every other remaining neighbour is odd. Connectivity of the puncture is not
needed by this restoration, so it also serves the bridge branch.
-/

namespace Gallai.Decomposition

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Restore the peeled edge at unchanged size and preserve every endpoint
away from its ends. A positive exposed count at y is sufficient. -/
theorem restore_odd_neighbor_peeling (x y w : V) (hxw : G.Adj x w)
    (hx : Even (G.degree x))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (D : Decomposition (G.deleteEdges {s(x, w)})) (hy : 0 < D.endpointCount y) :
    ∃ E : Decomposition G, E.size = D.size ∧
      ∀ v, v ≠ x → v ≠ w → E.endpointCount v = D.endpointCount v := by
  classical
  let H := G.deleteEdges {s(x, w)}
  have hdx := degree_delete_edge_add_one G x w hxw
  have hxOdd : Odd (H.degree x) := by
    rw [Nat.even_iff] at hx
    rw [Nat.odd_iff]
    change H.degree x + 1 = G.degree x at hdx
    omega
  have hxp := D.endpointCount_pos_of_odd_degree x hxOdd
  have hpass : #{v ∈ H.neighborFinset w | D.endpointCount v = 0} = 0 := by
    apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨ha, hz⟩ := Finset.mem_filter.mp hv
    have ha := (H.mem_neighborFinset w v).mp ha
    by_cases hvy : v = y
    · subst v
      omega
    · have ho := odd_neighbor_peeling_neighbors x y w hcontact v ha hvy
      have hp := D.endpointCount_pos_of_odd_degree v ho
      omega
  have hmissing : ¬ H.Adj w x := by
    simp [H, SimpleGraph.deleteEdges_adj, Sym2.eq_swap]
  have hstrict : #{v ∈ H.neighborFinset w | D.endpointCount v = 0} <
      D.endpointCount x := by
    rw [hpass]
    exact hxp
  obtain ⟨E, hs, he⟩ := D.single_edge_addibility (G := H) w x hxw.ne.symm hmissing hstrict
  have hgraph : H ⊔ SimpleGraph.edge w x = G := by
    rw [SimpleGraph.edge_comm]
    exact delete_edge_sup_edge G x w hxw
  have hout : ∃ E : Decomposition (H ⊔ SimpleGraph.edge w x), E.size = D.size ∧
      ∀ v, v ≠ x → v ≠ w → E.endpointCount v = D.endpointCount v := by
    refine ⟨E, hs, ?_⟩
    intro v hvx hvw
    simpa only [if_neg hvx.symm, if_neg hvw.symm, Nat.add_zero] using he v
  rwa [hgraph] at hout

end Gallai.Decomposition
