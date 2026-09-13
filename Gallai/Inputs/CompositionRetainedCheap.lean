/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedComponentInduction
import Gallai.Transport.RetainedCheapActual
import Gallai.Inputs.RetainedHubCredit

/-! # Actual retained representatives and family-compatible original-edge lifts -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable (B : WholeBowtie G) (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
variable (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
  (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
    (A k).val = v)
variable (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)

include hrows in
/-- Every cheap representative has exactly two retained hub spokes. -/
theorem retained_cheap_row_card : (B.row 0).card = 2 := by
  rw [← B.retainedHub_degree]
  exact (B.retainedNormalized_spokes_degree A _ hrows
    (Retained.cheapPassing_checked i).1 B.retainedHubGraph false
    (fun u v => by simp)).2

include hrows hcover in
/-- The actual retained repair preserves adjacency at each original even vertex. -/
theorem retained_cheap_even_adj (u v : B.StarSurvivor) (hu : Even (G.degree u.val)) :
    (B.retainedCheapAuxiliary A i).Adj u v ↔ G.Adj u.val v.val := by
  have hs := (Retained.cheapPassing_checked i).2.1
  by_cases hr : Retained.repair (Retained.cheapIndex i) = true
  · simp only [hr, if_true] at hs
    have ha := B.retainedRepair_even_adj (B.retainedSlot A 1) (B.retainedSlot A 2)
      (B.threeAnchor_private_pair A _ hrows hcover 1 2 hs) u v hu
    simpa only [WholeBowtie.retainedCheapAuxiliary, hr, if_true] using ha
  · simp only [WholeBowtie.retainedCheapAuxiliary, hr, Bool.false_eq_true, if_false]
    exact Iff.rfl

include hrows hcover in
/-- The actual auxiliary has at most two components in either repair-edge status. -/
theorem retained_cheap_components (hc : G.Connected) :
    Fintype.card (B.retainedCheapAuxiliary A i).ConnectedComponent ≤ 2 := by
  classical
  have hr := retained_cheap_row_card B A i hrows
  have hA : B.anchors.card ≤ 3 := by
    have hsub : B.anchors ⊆ Finset.univ.image (fun j : Fin 3 => (A j).val) := by
      intro v hv
      obtain ⟨j, hj⟩ := hcover v hv
      exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
    exact (Finset.card_le_card hsub).trans (Finset.card_image_le.trans (by decide))
  have hs := (Retained.cheapPassing_checked i).2.1
  simp only [← Nat.card_eq_fintype_card]
  by_cases hp : Retained.repair (Retained.cheapIndex i) = true
  · simp only [WholeBowtie.retainedCheapAuxiliary, hp, if_true]
    simp only [hp, if_true] at hs
    simpa only [Nat.card_eq_fintype_card] using
      B.retainedHubRepair_components_le_two (B.retainedSlot A 1) (B.retainedSlot A 2)
        (B.threeAnchor_private_pair A _ hrows hcover 1 2 hs) hc hA (by omega)
  · simp only [WholeBowtie.retainedCheapAuxiliary, hp, Bool.false_eq_true, if_false]
    simpa only [Nat.card_eq_fintype_card] using B.retainedHub_components_le_two hc hA
      (show 2 ≤ (B.row 0).card by omega)

include hrows hcover in
/-- A sum-budget witness lifts through every unrepaired or original-edge cheap case. -/
theorem retained_cheap_original_lift (hc : G.Connected)
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (D : Decomposition (B.retainedCheapAuxiliary A i))
    (hb : D.size ≤ ∑ K : (B.retainedCheapAuxiliary A i).ConnectedComponent,
      (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ w : B.StarSurvivor, w.val ≠ B.label 0 → Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hbudget := B.retained_credit_of_component_budget _ D hb
    (retained_cheap_components B A i hrows hcover hc)
  rcases hbudget with htwo | ⟨hone, hC, _⟩
  · obtain ⟨E, hsize, hends⟩ := B.retainedOrdinary_representative A _ hrows _
      (B.retainedCheapAuxiliary_original_adj A i hp) hp D
    exact ⟨E, hsize.trans htwo,
      fun w hx _ => hends w (fun he => hx (congrArg Subtype.val he))⟩
  · obtain ⟨E, hsize, hends⟩ :=
      B.retainedCheap_actual_reconstruction A i hrows hcover hc hp hC D
    refine ⟨E, hsize.trans hone, ?_⟩
    intro w hx hw
    apply hends w (fun he => hx (congrArg Subtype.val he))
    intro he
    subst w
    exact Nat.not_even_iff_odd.mpr
      (B.odd_degree_anchor (B.retainedCheap_remote_anchor A i hrows)) hw

end Gallai.Composition
