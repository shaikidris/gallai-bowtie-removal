/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapActual
import Gallai.Inputs.RetainedHubCredit

/-! # Normalized retained removal without a supplied auxiliary decomposition -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual normalized auxiliary supplies the required exposed
decomposition and either two credits or the sharp two-component credit. -/
theorem retainedCheap_credit_exists
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ D : Decomposition (B.retainedCheapAuxiliary A i), 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Fintype.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Fintype.card V + 1) / 2 ∧
          Fintype.card (B.retainedCheapAuxiliary A i).ConnectedComponent = 2)) := by
  classical
  let credit (H : SimpleGraph B.StarSurvivor) : Prop :=
    ∃ D : Decomposition H, 2 ≤ D.endpointCount y ∧
      (D.size + 2 ≤ (Nat.card V + 1) / 2 ∨
        (D.size + 1 ≤ (Nat.card V + 1) / 2 ∧ Nat.card H.ConnectedComponent = 2))
  simp only [← Nat.card_eq_fintype_card]
  change credit (B.retainedCheapAuxiliary A i)
  have hs0 := (Retained.cheapPassing_checked i).1
  have hr : (B.row 0).card = 2 := by
    rw [← B.retainedHub_degree]
    exact (B.retainedNormalized_spokes_degree A _ hrows hs0 B.retainedHubGraph false
      (fun u v => by simp)).2
  have ha : B.anchors.card ≤ 3 := by
    have hsub : B.anchors ⊆ Finset.univ.image (fun j : Fin 3 => (A j).val) := by
      intro v hv
      obtain ⟨j,hj⟩ := hA v hv
      exact Finset.mem_image.mpr ⟨j,Finset.mem_univ _,hj⟩
    exact (Finset.card_le_card hsub).trans ((Finset.card_image_le).trans (by decide))
  have hs := (Retained.cheapPassing_checked i).2.1
  by_cases hp : Retained.repair (Retained.cheapIndex i) = true
  · have hH : B.retainedCheapAuxiliary A i =
        B.retainedHubRepair (B.retainedSlot A 1) (B.retainedSlot A 2) := by
      simp [retainedCheapAuxiliary, hp]
    rw [hH]
    simp only [hp, if_true] at hs
    have hne : B.retainedSlot A 1 ≠ B.retainedSlot A 2 := by
      intro h
      have he : (1 : Fin 3) = 2 := A.injective
        (Subtype.ext (congrArg (fun w : B.StarSurvivor => w.val) h))
      exact (by decide : (1 : Fin 3) ≠ 2) he
    obtain ⟨D,he,hb⟩ := B.retainedHubRepair_endpoint_credit _ _ hne
      (B.threeAnchor_private_pair A _ hrows hA 1 2 hs) hr ha hG y hx hy hcap
    simp only [← Nat.card_eq_fintype_card] at hb
    exact ⟨D,he,hb.imp id (fun h => ⟨h.1,h.2.1⟩)⟩
  · have hH : B.retainedCheapAuxiliary A i = B.retainedHubGraph := by
      simp [retainedCheapAuxiliary, hp]
    rw [hH]
    simp [hp] at hs
    obtain ⟨D,he,hb⟩ := B.retainedHub_endpoint_credit
      (B.threeAnchor_private_empty A _ hrows hA hs) hr ha hG y hx hy hcap
    simp only [← Nat.card_eq_fintype_card] at hb
    exact ⟨D,he,hb.imp id (fun h => ⟨h.1,h.2.1⟩)⟩

/-- Five normalized retained representatives satisfy the actual removal
conclusion whenever the indicated repair is absent or deletes an original edge.
Synthetic repair and orbit selection are separate remaining branches. -/
theorem retainedCheap_original_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (i : Fin 5)
    (hrows : ∀ j v, v ∈ B.row j ↔ ∃ k,
      (rowMask (Retained.state (Retained.cheapIndex i) j)).val.testBit k.val = true ∧
        (A k).val = v)
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hG : G.Connected)
    (hp : Retained.repair (Retained.cheapIndex i) = true → G.Adj (A 1).val (A 2).val)
    (y : B.StarSurvivor) (hx : y.val ≠ B.label 0) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
  obtain ⟨D,he,hb⟩ := B.retainedCheap_credit_exists A i hrows hA hG y hx hy hcap
  exact B.retainedCheap_actual_budget A i hrows hA hG hp D y hx hy he hb

end Gallai.WholeBowtie
