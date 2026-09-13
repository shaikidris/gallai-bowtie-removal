/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.PeelingConnected
import Gallai.Inputs.PeelingComponentFloor
import Gallai.Operations.ComponentEndpointAssembly

/-! # Odd-neighbour peeling, including bridge punctures -/

namespace Gallai

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Four even neighbours at the peeled hub supply every off-y component floor
budget. The actual puncture need not be connected and may have an isolated leaf. -/
theorem peeling_puncture_endpoint (x y w : V) (hc : G.Connected) (hxy : x ≠ y)
    (hxw : G.Adj x w) (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hw : Odd (G.degree w))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3)
    (hlarge : 4 ≤ eDegree G x) :
    ∃ D : Decomposition (G.deleteEdges {s(x, w)}),
      D.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ D.endpointCount y := by
  classical
  let H := G.deleteEdges {s(x, w)}
  let C := H.connectedComponentMk y
  have hclosed : ∀ v ∈ C.supp, H.neighborSet v ⊆ C.supp :=
    fun _ hv _ ha => C.mem_supp_of_adj_mem_supp hv ha
  have hdeg (v : C.supp) : (H.induce C.supp).degree v = H.degree v.val :=
    SimpleGraph.degree_induce_of_neighborSet_subset (hclosed v v.property)
  have hyw : y ≠ w := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hw hy
  have hdy : H.degree y = G.degree y := degree_delete_edge_of_ne G x w y hxy.symm hyw
  have hyEven : Even ((H.induce C.supp).degree ⟨y, rfl⟩) := by
    rw [hdeg, hdy]
    exact hy
  have : Nontrivial V := ⟨⟨x, y, hxy⟩⟩
  have hyPos : 0 < (H.induce C.supp).degree ⟨y, rfl⟩ := by
    rw [hdeg, hdy]
    exact hc.preconnected.degree_pos_of_nontrivial y
  have hcaps := odd_neighbor_peeling_cap x y w hxw hx hw hcontact hcap
  have hcapC : ∀ v, Even ((H.induce C.supp).degree v) → v ≠ ⟨y, rfl⟩ →
      eDegree (H.induce C.supp) v ≤ 3 := by
    intro v hev hvy
    rw [eDegree_induce_of_closed H C.supp hclosed v]
    exact hcaps v.val ((hdeg v) ▸ hev) (fun heq => hvy (Subtype.ext heq))
  obtain ⟨D, hs, he⟩ := one_exception_endpoint (H.induce C.supp) ⟨y, rfl⟩
    C.connected_toSimpleGraph hyPos hyEven hcapC
  apply endpoint_ceiling_of_component_floors H y D hs he
  intro B hB
  apply peeling_other_component_floor x y w hc hxw hx hw hcontact hcap hlarge B
  intro hyB
  exact hB (SimpleGraph.ConnectedComponent.eq_of_common_vertex hyB rfl)

/-- Literal peeling budget and endpoint conclusion. Connected deletion or four
even neighbours at x suffice; adjacency between the two even vertices is not needed. -/
theorem odd_neighbor_peeling (x y w : V) (hc : G.Connected) (hxy : x ≠ y)
    (hxw : G.Adj x w) (hx : Even (G.degree x)) (hy : Even (G.degree y))
    (hw : Odd (G.degree w))
    (hcontact : ∀ v, G.Adj w v → Even (G.degree v) → v = x ∨ v = y)
    (hcap : ∀ v, Even (G.degree v) → v ≠ x → v ≠ y → eDegree G v ≤ 3)
    (hcase : (G.deleteEdges {s(x, w)}).Connected ∨ 4 ≤ eDegree G x) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  rcases hcase with hconn | hlarge
  · exact odd_neighbor_peeling_connected x y w hxy hxw hx hy hw hcontact hcap hconn
  obtain ⟨D, hs, he⟩ := peeling_puncture_endpoint x y w hc hxy hxw hx hy hw
    hcontact hcap hlarge
  have hyw : y ≠ w := by
    rintro rfl
    exact Nat.not_even_iff_odd.mpr hw hy
  obtain ⟨E, hE, hcounts⟩ := D.restore_odd_neighbor_peeling x y w hxw hx hcontact (by omega)
  refine ⟨E, by omega, ?_⟩
  rwa [hcounts y hxy.symm hyw]

end Gallai
