/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie
import Gallai.Certificates.CompletedStar
import Mathlib.Data.Fintype.Powerset
import Mathlib.Data.Fintype.EquivFin

/-! # Actual bowtie rows as completed-star inputs

Every four-anchor bowtie determines the catalogue masks. The mask/adjacency
correspondence is proved from the graph, not supplied as a certificate premise.
This module does not yet construct the completed auxiliary or release carriers.
-/

namespace Gallai.Certificate.CompletedStar

/-- Every subset of four bit positions has an exact four-bit encoding. -/
theorem exists_mask (row : Finset (Fin 4)) :
    ∃ mask : Fin 16, ∀ j : Fin 4, mask.val.testBit j.val = true ↔ j ∈ row := by
  revert row
  decide

/-- Select an encoding after the finite existence proof, without an input oracle. -/
noncomputable def maskOf (row : Finset (Fin 4)) : Fin 16 :=
  Classical.choose (exists_mask row)

/-- Selected masks preserve each incidence bit exactly. -/
theorem maskOf_spec (row : Finset (Fin 4)) (j : Fin 4) :
    (maskOf row).val.testBit j.val = true ↔ j ∈ row :=
  Classical.choose_spec (exists_mask row) j

/-- The finite support represented by a row mask. -/
def maskSupport (mask : Fin 16) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => mask.val.testBit j.val)

/-- Encoding then decoding retains the entire subset, not only its size. -/
theorem maskSupport_maskOf (row : Finset (Fin 4)) : maskSupport (maskOf row) = row := by
  ext j
  simp [maskSupport, maskOf_spec]

end Gallai.Certificate.CompletedStar

namespace Gallai.WholeBowtie

open Certificate.CompletedStar

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Anchor numbering comes from the actual four-element external neighbourhood. -/
abbrev AnchorNumbering := Fin 4 ≃ {v // v ∈ B.anchors}

/-- Four anchors supply a numbering, rather than requiring one as an extra premise. -/
noncomputable def anchorNumbering (h : B.anchors.card = 4) : B.AnchorNumbering :=
  (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using h)).symm

/-- No numbered anchor is an internal bowtie vertex. -/
theorem numberedAnchor_not_mem (A : B.AnchorNumbering) (j : Fin 4) :
    (A j).val ∉ B.vertices := by
  obtain ⟨i, hi⟩ := (B.mem_anchors _).mp (A j).property
  exact ((B.mem_row i _).mp hi).2

/-- A numbered anchor differs from each of the five internal labels. -/
theorem label_ne_numberedAnchor (A : B.AnchorNumbering) (i : Fin 5) (j : Fin 4) :
    B.label i ≠ (A j).val := by
  intro h
  apply B.numberedAnchor_not_mem A j
  rw [← h]
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- Actual external incidences, expressed in four finite anchor coordinates. -/
def numberedRow (A : B.AnchorNumbering) (i : Fin 5) : Finset (Fin 4) :=
  Finset.univ.filter (fun j => (A j).val ∈ B.row i)

/-- Graph-derived five-row catalogue input. -/
noncomputable def completedStarState (A : B.AnchorNumbering) : State :=
  fun i => maskOf (B.numberedRow A i)

/-- The encoded row bit is equivalent to original graph adjacency. -/
theorem completedStarState_bit (A : B.AnchorNumbering) (i : Fin 5) (j : Fin 4) :
    (B.completedStarState A i).val.testBit j.val = true ↔
      G.Adj (B.label i) (A j).val := by
  rw [completedStarState, maskOf_spec]
  simp [numberedRow, B.numberedAnchor_not_mem A j]

/-- Numbered incidences reconstruct the entire original external row. -/
theorem numberedRow_image (A : B.AnchorNumbering) (i : Fin 5) :
    (B.numberedRow A i).image (fun j => (A j).val) = B.row i := by
  ext v
  constructor
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
    exact (Finset.mem_filter.mp hj).2
  · intro h
    have hv : v ∈ B.anchors := (B.mem_anchors v).mpr ⟨i, h⟩
    let j := A.symm ⟨v, hv⟩
    have hj : (A j).val = v := congrArg Subtype.val (A.apply_symm_apply ⟨v, hv⟩)
    exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
      ⟨Finset.mem_univ _, by simpa [hj] using h⟩, hj⟩

/-- Row cardinality is preserved by numbering actual distinct anchors. -/
theorem numberedRow_card (A : B.AnchorNumbering) (i : Fin 5) :
    (B.numberedRow A i).card = (B.row i).card := by
  rw [← B.numberedRow_image A i]
  exact (Finset.card_image_of_injective _
    (Subtype.val_injective.comp A.injective)).symm

/-- Catalogue row evenness is inherited from the original whole bowtie. -/
theorem numberedRow_even (A : B.AnchorNumbering) (i : Fin 5) :
    Even (B.numberedRow A i).card := by
  rw [B.numberedRow_card A i]
  exact B.even_card_row i

/-- Actual completed-star state masks belong to the even-row domain. -/
theorem completedStarState_even (A : B.AnchorNumbering) (i : Fin 5) :
    Even (maskSupport (B.completedStarState A i)).card := by
  rw [completedStarState, maskSupport_maskOf]
  exact B.numberedRow_even A i

/-- A four-anchor bowtie supplies all five even masks with exact adjacency.
The full-syndrome condition is separate and is not inferred from four anchors. -/
theorem exists_completedStarState (h : B.anchors.card = 4) :
    ∃ (A : B.AnchorNumbering) (state : State),
      (∀ i, Even (maskSupport (state i)).card) ∧
      ∀ i j, (state i).val.testBit j.val = true ↔ G.Adj (B.label i) (A j).val :=
  ⟨B.anchorNumbering h, B.completedStarState (B.anchorNumbering h),
    B.completedStarState_even _, B.completedStarState_bit _⟩

end Gallai.WholeBowtie
