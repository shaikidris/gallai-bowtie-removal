/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.PeelingRestore
import Gallai.Inputs.OneException

/-! # The connected-puncture case of odd-neighbour peeling

The decomposition is selected by the proved endpoint theorem on the actual
edge-deleted graph, then lifted at the same count by Fan addibility.
-/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- A connected peeling puncture yields the original ceiling budget with y
exposed twice. The original graph's connectedness follows from that of the
puncture; nonadjacency of x and y is unnecessary for this subcase. -/
theorem odd_neighbor_peeling_connected (x y w : V) (hxy : x ≠ y)
    (hxw : G.Adj x w) (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hw : Odd (G.degree w))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3)
    (hconn : (G.deleteEdges {s(x, w)}).Connected) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  classical
  let H := G.deleteEdges {s(x, w)}
  have hyw : y ≠ w := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hw hy
  have hdegree : H.degree y = G.degree y := degree_delete_edge_of_ne G x w y hxy.symm hyw
  have hye : Even (H.degree y) := hdegree.symm ▸ hy
  have : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
  have hpos : 0 < H.degree y := hconn.preconnected.degree_pos_of_nontrivial y
  have hcaps := odd_neighbor_peeling_cap x y w hxw hx hw hcontact hcap
  obtain ⟨D, hs, he⟩ := one_exception_endpoint H y hconn hpos hye hcaps
  obtain ⟨E, hE, hcounts⟩ := D.restore_odd_neighbor_peeling x y w hxw hx hcontact (by omega)
  refine ⟨E, by omega, ?_⟩
  rwa [hcounts y hxy.symm hyw]

end Gallai
