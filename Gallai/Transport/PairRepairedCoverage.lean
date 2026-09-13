/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.PairRepairedFamily
import Gallai.Foundations.EdgeCounts
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Original-edge coverage after synthetic pair restoration

The local certificate contract counts only edges incident with the deleted
bowtie. All other original edges are supplied by the actual auxiliary family.
-/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An original edge meeting the deleted bowtie occurs on no auxiliary carrier. -/
theorem pairRepaired_count_local (p q : {v : V // v ∉ B.vertices})
    (D : Decomposition (B.pairRepairedPuncture p q)) (e : Sym2 V)
    (hl : ∃ v ∈ e, v ∈ B.vertices) :
    (∑ i, (B.pairRepairedCarrier p q (D.path i)).walk.edges.count e) = 0 := by
  obtain ⟨v, hv, hvB⟩ := hl
  apply Finset.sum_eq_zero
  intro i _
  apply List.count_eq_zero.mpr
  rw [B.pairRepairedCarrier_edges]
  intro he
  obtain ⟨f, _, hfe⟩ := List.mem_map.mp he
  rw [← hfe] at hv
  obtain ⟨w, _, hw⟩ := Sym2.mem_map.mp hv
  exact w.property (hw ▸ hvB)

/-- Every original edge outside the bowtie retains multiplicity one after adding
a missing repair edge; connectedness and order parity play no role here. -/
theorem pairRepaired_count_outside (p q : {v : V // v ∉ B.vertices})
    (hmissing : ¬ G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (e : Sym2 V) (he : e ∈ G.edgeSet) (hl : ¬ ∃ v ∈ e, v ∈ B.vertices) :
    (∑ i, (B.pairRepairedCarrier p q (D.path i)).walk.edges.count e) = 1 := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hu : u ∉ B.vertices := fun h => hl ⟨u, by simp, h⟩
    have hv : v ∉ B.vertices := fun h => hl ⟨v, by simp, h⟩
    let f : Sym2 {v // v ∉ B.vertices} := s(⟨u, hu⟩, ⟨v, hv⟩)
    have hf : f ∈ (B.pairRepairedPuncture p q).edgeSet := by
      change (toggleEdge B.puncture p q).Adj ⟨u, hu⟩ ⟨v, hv⟩
      simp only [toggleEdge, show ¬ B.puncture.Adj p q from hmissing, if_false]
      exact Or.inl he
    change (∑ i, (B.pairRepairedCarrier p q (D.path i)).walk.edges.count
      (Sym2.map Subtype.val f)) = 1
    simp only [B.pairRepairedCarrier_edges,
      List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
    exact (D.sum_edge_count f).trans (if_pos hf)

/-- Local certificate paths complete the synthetic family to a decomposition
with exact cost and every retained endpoint reserve. -/
theorem syntheticPair_reconstruction (p q : {v : V // v ∉ B.vertices}) (hne : p ≠ q)
    (hmissing : ¬ G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (M : G.Walk p.val q.val) (hM : M.IsPath)
    (hcore : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ B.vertices)
    {t : ℕ} (N : Fin t → NonemptyPath G)
    (hlocal : ∀ e ∈ G.edgeSet, M.edges.count e + (∑ j, (N j).walk.edges.count e) =
      if ∃ v ∈ e, v ∈ B.vertices then 1 else 0) :
    ∃ E : Decomposition G, E.size = D.size + t ∧
      ∀ w : {v // v ∉ B.vertices}, D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  obtain ⟨F, hends, hcount⟩ := B.syntheticPairFamily p q hne hmissing D M hM hcore
  let family : Fin D.size ⊕ Fin t → NonemptyPath G := Sum.elim F N
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) :
      (∑ i, (family i).walk.edges.count e) = 1 := by
    have hneE : s(p.val, q.val) ≠ e := by
      intro h
      apply hmissing
      change s(p.val, q.val) ∈ G.edgeSet
      rw [h]
      exact he
    have hc := hcount e
    rw [if_neg hneE] at hc
    have hl := hlocal e he
    rw [Fintype.sum_sum_type]
    change (∑ i, (F i).walk.edges.count e) + (∑ j, (N j).walk.edges.count e) = 1
    by_cases hB : ∃ v ∈ e, v ∈ B.vertices
    · rw [B.pairRepaired_count_local p q D e hB] at hc
      rw [if_pos hB] at hl
      omega
    · rw [B.pairRepaired_count_outside p q hmissing D e he hB] at hc
      rw [if_neg hB] at hl
      omega
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + t) => family (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
        (fun i => (family i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E, rfl, ?_⟩
  intro w
  have hF := B.repairedFamily_endpoint_count p q D F hends w
  change D.endpointCount w ≤ ∑ i : Fin (D.size + t),
    ((if (family (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (family (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
      (fun i => (if (family i).start = w.val then 1 else 0) +
        (if (family i).finish = w.val then 1 else 0)),
    Fintype.sum_sum_type]
  change D.endpointCount w ≤
    (∑ i, ((if (F i).start = w.val then 1 else 0) +
      (if (F i).finish = w.val then 1 else 0))) + _
  rw [hF]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
