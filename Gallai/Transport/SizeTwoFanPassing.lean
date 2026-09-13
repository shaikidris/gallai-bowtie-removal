/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFanNeighbors
import Gallai.Structure.SyndromeStarParity
import Gallai.Foundations.EndpointBounds

/-! # Passing bounds derived from the actual Fan initial decomposition -/
namespace Gallai.WholeBowtie

noncomputable section

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

local instance (A : B.AnchorNumbering) :
    DecidableRel (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj := Classical.decRel _

/-- Anchor parity and the two added paths give all reserves on one witness. -/
theorem sizeTwoFan_initial_reserves (A : B.AnchorNumbering)
    (D : Decomposition B.syndromeStar)
    (E : Decomposition (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A))
    (he : ∀ v, E.endpointCount v =
      (D.map (Function.Embedding.subtype _)).endpointCount v +
      (B.sizeTwoFanAddedDecomposition A).endpointCount v) :
    (∀ j : Fin 4, 1 ≤ E.endpointCount (A j).val) ∧
      2 ≤ E.endpointCount (B.label 1) ∧ 3 ≤ E.endpointCount (A 3).val := by
  classical
  have hanchor (j : Fin 4) :
      1 ≤ (D.map (Function.Embedding.subtype _)).endpointCount (A j).val := by
    let w : B.StarSurvivor := ⟨(A j).val,B.anchor_survives (A j).property⟩
    have ho : Odd (B.syndromeStar.degree w) := by
      apply Nat.not_even_iff_odd.mp
      intro hh
      exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (A j).property)
        ((B.syndromeStar_even_iff w).mp hh)
    have hp := D.endpointCount_pos_of_odd_degree w ho
    have hm := D.map_endpointCount (Function.Embedding.subtype _) w
    change (D.map (Function.Embedding.subtype _)).endpointCount (A j).val =
      D.endpointCount w at hm
    omega
  refine ⟨?_,?_,?_⟩
  · intro j
    rw [he]
    exact (hanchor j).trans (Nat.le_add_right _ _)
  · have ha := B.sizeTwoFanAdded_endpoints A .a
    change (B.sizeTwoFanAddedDecomposition A).endpointCount (B.label 1) = 2 at ha
    rw [he,ha]
    omega
  · have hs := B.sizeTwoFanAdded_endpoints A .s
    change (B.sizeTwoFanAddedDecomposition A).endpointCount (A 3).val = 2 at hs
    rw [he,hs]
    have hh := hanchor 3
    omega

/-- Every potential passing neighbour is explicitly confined; these are the
strict bounds consumed by three_edge_fan_restore. -/
theorem sizeTwoFan_initial_passing (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (E : Decomposition (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A))
    (hanchor : ∀ j : Fin 4, 1 ≤ E.endpointCount (A j).val)
    (ha : 2 ≤ E.endpointCount (B.label 1)) :
    #{v ∈ (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).neighborFinset (B.label 0) |
      E.endpointCount v = 0} ≤ 2 ∧
    #{v ∈ (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).neighborFinset (B.label 2) |
      E.endpointCount v = 0} = 0 := by
  classical
  constructor
  · have hsub :
        ((B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).neighborFinset (B.label 0)).filter
          (fun v => E.endpointCount v = 0) ⊆ {B.label 3,B.label 4} := by
      intro v hv
      obtain ⟨hv,hzero⟩ := Finset.mem_filter.mp hv
      have hadj := ((B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).mem_neighborFinset
        (B.label 0) v).mp hv
      obtain ⟨t,ht,he⟩ := (B.sizeTwoFan_initial_hub_adj A hSigma v).mp hadj
      simp only [Finset.mem_insert,Finset.mem_singleton] at ht
      rcases ht with rfl | rfl | rfl | rfl | rfl | rfl
      · have he' : B.label 1 = v := he
        rw [← he'] at hzero
        omega
      · exact Finset.mem_insert.mpr (Or.inl he.symm)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_singleton.mpr he.symm))
      · have hh := hanchor 0
        change (A 0).val = v at he
        rw [he] at hh
        omega
      · have hh := hanchor 1
        change (A 1).val = v at he
        rw [he] at hh
        omega
      · have hh := hanchor 2
        change (A 2).val = v at he
        rw [he] at hh
        omega
    exact (Finset.card_le_card hsub).trans (by simp)
  · apply Finset.card_eq_zero.mpr
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro v hv
    obtain ⟨hv,hzero⟩ := Finset.mem_filter.mp hv
    have hadj := ((B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).mem_neighborFinset
      (B.label 2) v).mp hv
    obtain ⟨t,ht,he⟩ := (B.sizeTwoFan_initial_b_adj A hSigma v).mp hadj
    simp only [Finset.mem_insert,Finset.mem_singleton] at ht
    rcases ht with rfl | rfl
    · have he' : B.label 1 = v := he
      rw [← he'] at hzero
      omega
    · have hh := hanchor 2
      change (A 2).val = v at he
      rw [he] at hh
      omega

end
end Gallai.WholeBowtie
