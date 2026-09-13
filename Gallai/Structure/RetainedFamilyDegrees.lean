/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtieRetainedHub

/-! # Degree interfaces for retained-hub family induction -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Outside even vertices have no neighbour among the deleted private vertices. -/
theorem retainedHub_degree_even_outside (v : B.StarSurvivor)
    (hv : Even (G.degree v.val)) (hout : v.val ∉ B.vertices) :
    B.retainedHubGraph.degree v = G.degree v.val := by
  have hz : G.neighborFinset v.val ∩ (Finset.univ.erase 0).map B.label = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hw
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hm
    have hr := (B.mem_row i v.val).mpr
      ⟨((G.mem_neighborFinset _ _).mp ha).symm, hout⟩
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (B.row_subset_anchors i hr)) hv
  have hd := B.privateDeletion_degree_add_deleted (Finset.univ.erase 0) v
  simpa only [hz, Finset.card_empty, Nat.add_zero] using hd

variable (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
variable (hpar : ∀ v : B.StarSurvivor, Even (H.degree v) ↔ Even (G.degree v.val))
variable (hadj : ∀ u v : B.StarSurvivor, Even (G.degree u.val) →
  (H.Adj u v ↔ G.Adj u.val v.val))

include hadj in
/-- Even adjacency preservation preserves the full retained degree. -/
theorem retainedAux_degree (v : B.StarSurvivor) (hv : Even (G.degree v.val)) :
    H.degree v = B.retainedHubGraph.degree v := by
  have he : H.neighborFinset v = B.retainedHubGraph.neighborFinset v := by
    ext w
    simp only [SimpleGraph.mem_neighborFinset]
    exact hadj v w hv
  exact congrArg Finset.card he

include hadj in
/-- Outside even vertices retain their positive degree in either actual auxiliary. -/
theorem retainedAux_degree_even_outside (v : B.StarSurvivor)
    (hv : Even (G.degree v.val)) (hout : v.val ∉ B.vertices) :
    H.degree v = G.degree v.val :=
  (B.retainedAux_degree H hadj v hv).trans (B.retainedHub_degree_even_outside v hv hout)

include hpar hadj in
/-- Parity and even adjacency preservation introduce no even neighbour. -/
theorem retainedAux_eDegree_le (v : B.StarSurvivor) : eDegree H v ≤ eDegree G v.val := by
  have hsub : (evenNeighbors H v).map (Function.Embedding.subtype _) ⊆
      evenNeighbors G v.val := by
    intro w hw
    obtain ⟨u, hu, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hu
    have he' := (hpar u).mp he
    exact (mem_evenNeighbors _ _).mpr ⟨((hadj u v he').mp ha.symm).symm, he'⟩
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hsub

include hadj in
/-- The retained hub is nonexceptional when it has at most three surviving spokes. -/
theorem retainedAux_hub_cap (hr : (B.row 0).card ≤ 3) :
    eDegree H B.completedHub ≤ 3 := by
  apply (eDegree_le_degree _).trans
  rw [B.retainedAux_degree H hadj B.completedHub (B.even_degree_label 0),
    B.retainedHub_degree]
  exact hr

end Gallai.WholeBowtie
