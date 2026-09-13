/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ThreeAnchorRows

/-! # Three actual anchors fill every injectively labelled anchor slot -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Exact boundary cardinality turns the covering slots into used anchor labels. -/
theorem threeAnchor_all_used (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcard : B.anchors.card = 3) :
    ∀ j : Fin 3, ∃ i : Fin 5, (rowMask (s i)).val.testBit j.val = true := by
  classical
  let U := Finset.univ.image (fun j : Fin 3 => (A j).val)
  have hU : U.card = 3 := by
    rw [Finset.card_image_of_injective _ (fun i j he => A.injective (Subtype.ext he))]
    simp
  have hsub : B.anchors ⊆ U := by
    intro v hv
    obtain ⟨j, hj⟩ := hcover v hv
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, hj⟩
  have heq : B.anchors = U := Finset.eq_of_subset_of_card_le hsub (by omega)
  intro j
  have hj : (A j).val ∈ B.anchors := by
    rw [heq]
    exact Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩
  obtain ⟨i, hi⟩ := (B.mem_anchors _).mp hj
  obtain ⟨r, hr, he⟩ := (hrows i _).mp hi
  have hrj : r = j := A.injective (Subtype.ext he)
  exact ⟨i, hrj ▸ hr⟩

end Gallai.WholeBowtie
