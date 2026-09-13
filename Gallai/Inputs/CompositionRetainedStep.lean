/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionRetainedZero
import Gallai.Structure.RetainedComponentInduction

/-! # Retained-hub induction steps with an optional designated endpoint -/
namespace Gallai.Composition
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Consume the same auxiliary witness supplied by strict smaller-family induction. -/
theorem retained_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d)
    (H : SimpleGraph (Bs 0).StarSurvivor) [DecidableRel H.Adj]
    (hpar : ∀ v, Even (H.degree v) ↔ Even (G.degree v.val))
    (hadj : ∀ u v, Even (G.degree u.val) → (H.Adj u v ↔ G.Adj u.val v.val))
    (hr : ((Bs 0).row 0).card ≤ 3)
    (lift : ∀ D : Decomposition H,
      D.size ≤ ∑ K : H.ConnectedComponent, (Fintype.card K.supp + 1) / 2 →
      ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
        ∀ w : (Bs 0).StarSurvivor, w.val ≠ (Bs 0).label 0 → Even (G.degree w.val) →
          D.endpointCount w ≤ E.endpointCount w.val)
    (ih : RetainedComponentIH Bs H) : Conclusion G d := by
  cases d with
  | none =>
    obtain ⟨D, hD⟩ := retained_induction_sum Bs h.1 H hpar hadj hr h ih
    obtain ⟨E, hE, _⟩ := lift D hD
    exact ⟨E, hE, by simp⟩
  | some y =>
    have hy := h.2.2.1 y (by simp)
    have hs : y ∉ (Finset.univ.erase 0).map (Bs 0).label := by
      intro hm
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hm
      exact hy.2.2 0 (((Bs 0).mem_vertices _).mpr ((Bs 0).label_mem_component j))
    let y' : (Bs 0).StarSurvivor := ⟨y, hs⟩
    have hx : y ≠ (Bs 0).label 0 := by
      intro he
      exact hy.2.2 0 (he ▸ ((Bs 0).mem_vertices _).mpr ((Bs 0).label_mem_component 0))
    obtain ⟨D, hD, he⟩ := retained_induction_endpoint_sum Bs h.1 H hpar hadj hr y' h ih
    obtain ⟨E, hE, hends⟩ := lift D hD
    refine ⟨E, hE, ?_⟩
    intro z hz
    have heq : z = y := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    subst z
    exact he.trans (hends y' hx hy.1)

/-- The five nonzero normalized retained cases, with either designation choice. -/
theorem retained_five_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (A : Fin 3 ↪ {v : V // v ∉ (Bs 0).vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ (Bs 0).row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hcover : ∀ v ∈ (Bs 0).anchors, ∃ j, (A j).val = v)
    (ih : RetainedComponentIH Bs ((Bs 0).retainedCheapAuxiliary A i)) :
    Conclusion G d := by
  apply retained_step Bs d h ((Bs 0).retainedCheapAuxiliary A i)
    ((Bs 0).retainedCheapAuxiliary_even_iff A i hrows hcover)
    (retained_cheap_even_adj (Bs 0) A i hrows hcover)
    (by have := retained_cheap_row_card (Bs 0) A i hrows; omega)
    (retained_five_lift (Bs 0) A i hrows hcover hc) ih

/-- The zero normalized retained case, with either designation choice. -/
theorem retained_zero_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (A : Fin 3 ↪ {v : V // v ∉ (Bs 0).vertices})
    (hrows : ∀ j v, v ∈ (Bs 0).row j ↔ ∃ k,
      (rowMask (Retained.state 0 j)).val.testBit k.val = true ∧ (A k).val = v)
    (hcover : ∀ v ∈ (Bs 0).anchors, ∃ j, (A j).val = v)
    (ih : RetainedComponentIH Bs (Bs 0).retainedHubGraph) : Conclusion G d := by
  have hs := (Bs 0).threeAnchor_private_empty A _ hrows hcover
    (by decide : privateSyndrome (Retained.state 0) = ∅)
  obtain ⟨_, hd⟩ := (Bs 0).retainedNormalized_spokes_degree A _ hrows
    (by decide : Retained.state 0 0 = 1) (Bs 0).retainedHubGraph false
    (fun u v => by simp)
  have hr : ((Bs 0).row 0).card = 2 := (Bs 0).retainedHub_degree.symm.trans hd
  apply retained_step Bs d h (Bs 0).retainedHubGraph
    ((Bs 0).retainedHub_even_iff hs) ((Bs 0).retained_even_adj) (by omega) ?_ ih
  intro D hb
  obtain ⟨E, hE, hends⟩ := retained_zero_lift (Bs 0) A hrows hc D hb
  exact ⟨E, hE, fun w hw _ => hends w hw⟩

end Gallai.Composition
