/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.SyndromeStarSET
import Gallai.Operations.ComponentReserves

/-! # Simultaneous designated and remote reserves in the actual auxiliary -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem syndromeStar_set_simultaneous (hc : G.Connected)
    (hs : B.syndrome.Nonempty) (y : B.StarSurvivor)
    (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3)
    (C : B.syndromeStar.ConnectedComponent) [DecidablePred (· ∈ C.supp)]
    (hyC : y ∉ C.supp) (hC : IsSET (B.syndromeStar.induce C.supp)) :
    ∃ w : B.StarSurvivor, w.val ∈ B.anchors ∧ w.val ∉ B.syndrome ∧
      w ∈ C.supp ∧ ∃ E : Decomposition B.syndromeStar,
        E.size ≤ ∑ K : B.syndromeStar.ConnectedComponent,
          (Fintype.card K.supp + 1) / 2 ∧
        2 ≤ E.endpointCount y ∧ 3 ≤ E.endpointCount w := by
  classical
  obtain ⟨w,hA,hwS,D,hD,hwD⟩ := B.syndromeStar_set_remote_reserve hc hs C hC
  have : Nontrivial V := ⟨⟨y.val,B.label 0,hx⟩⟩
  have hp : 0 < B.syndromeStar.degree y := by
    rw [B.syndromeStar_degree_of_even y hx hy]
    exact hc.preconnected.degree_pos_of_nontrivial y.val
  have he := (B.syndromeStar_even_iff y).mpr hy
  have cap := B.syndromeStar_cap y hcap
  have supply (K : B.syndromeStar.ConnectedComponent) :
      ∃ Q : Decomposition (B.syndromeStar.induce K.supp),
        Q.size ≤ (Fintype.card K.supp + 1) / 2 ∧
        (∀ h : y ∈ K.supp, 2 ≤ Q.endpointCount ⟨y,h⟩) ∧
        (∀ h : w.val ∈ K.supp, 3 ≤ Q.endpointCount ⟨w.val,h⟩) := by
    by_cases hKC : K = C
    · subst K
      refine ⟨D,?_,fun h => (hyC h).elim,fun _ => hwD⟩
      simpa only [← Nat.card_eq_fintype_card] using hD
    have hremote : w.val ∉ K.supp := fun h =>
      hKC (SimpleGraph.ConnectedComponent.eq_of_common_vertex h w.property)
    by_cases hyK : y ∈ K.supp
    · obtain ⟨Q,hQ,hyQ⟩ := component_endpoint_of_cap B.syndromeStar y K hyK hp he cap
      exact ⟨Q,hQ,fun _ => hyQ,fun h => (hremote h).elim⟩
    · obtain ⟨Q,hQ⟩ := other_component_ceiling B.syndromeStar y K hyK cap
      exact ⟨Q,hQ,fun h => (hyK h).elim,fun h => (hremote h).elim⟩
  choose Q hQ hyQ hwQ using supply
  obtain ⟨E,hE,hEv⟩ := decomposition_component_reserves B.syndromeStar Q
  refine ⟨w.val,hA,hwS,w.property,E,?_,?_,?_⟩
  · rw [hE]
    exact Finset.sum_le_sum fun K _ => hQ K
  · exact (hyQ (B.syndromeStar.connectedComponentMk y) rfl).trans
      (hEv (B.syndromeStar.connectedComponentMk y) ⟨y,rfl⟩)
  · exact (hwQ C w.property).trans (hEv C w)

end Gallai.WholeBowtie
