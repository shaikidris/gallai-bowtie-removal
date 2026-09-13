/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorLabels
import Gallai.Structure.Incidence
import Gallai.Structure.LowActivity

/-! # Actual even incidence rows produce the four-choice finite state -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Covering the actual anchors by three retained slots suffices to encode all
five rows exactly; unused slots have no incidence bit. -/
theorem exists_threeAnchorState (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v) :
    ∃ s : State, ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v := by
  classical
  have hfinite : ∀ T : Finset (Fin 3), Even T.card →
      ∃ c : Fin 4, ∀ j, (rowMask c).val.testBit j.val = true ↔ j ∈ T := by decide
  have hrow (i : Fin 5) : ∃ c : Fin 4, ∀ v, v ∈ B.row i ↔
      ∃ j, (rowMask c).val.testBit j.val = true ∧ (A j).val = v := by
    let T : Finset (Fin 3) := Finset.univ.filter fun j => (A j).val ∈ B.row i
    have himage : T.image (fun j => (A j).val) = B.row i := by
      ext v
      constructor
      · rintro hv
        obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
        exact (Finset.mem_filter.mp hj).2
      · intro hv
        obtain ⟨j, hj⟩ := hA v (B.row_subset_anchors i hv)
        exact Finset.mem_image.mpr ⟨j, Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hj ▸ hv⟩, hj⟩
    have heven : Even T.card := by
      have hcard := Finset.card_image_of_injective T (Subtype.val_injective.comp A.injective)
      change (T.image (fun j => (A j).val)).card = T.card at hcard
      rw [himage] at hcard
      rw [← hcard]
      exact B.even_card_row i
    obtain ⟨c, hc⟩ := hfinite T heven
    refine ⟨c, ?_⟩
    intro v
    rw [← himage, Finset.mem_image]
    constructor
    · rintro ⟨j, hj, he⟩
      exact ⟨j, (hc j).mpr hj, he⟩
    · rintro ⟨j, hj, he⟩
      exact ⟨j, (hc j).mp hj, he⟩
  choose s hs using hrow
  exact ⟨s, hs⟩

/-- Exact row encoding also preserves the count at each anchor column. -/
theorem threeAnchor_column_count (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (j : Fin 3) :
    (Finset.univ.filter fun i : Fin 5 =>
      (rowMask (s i)).val.testBit j.val = true).card = B.columnCount (A j).val := by
  unfold columnCount
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  rw [hrows]
  constructor
  · intro hj
    exact ⟨j, hj, rfl⟩
  · rintro ⟨k, hk, hkj⟩
    have he : k = j := A.injective (Subtype.ext hkj)
    exact he ▸ hk

/-- Encoded syndrome membership is actual syndrome membership at the same slot. -/
theorem threeAnchor_mem_syndrome (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (j : Fin 3) :
    j ∈ Certificate.ThreeAnchor.syndrome s ↔ (A j).val ∈ B.syndrome := by
  simp only [Certificate.ThreeAnchor.syndrome, Finset.mem_filter,
    Finset.mem_univ, true_and]
  rw [B.threeAnchor_column_count A s hrows j, B.mem_syndrome_iff_odd_column]

/-- Covering slots identify the entire actual syndrome, not just its cardinality. -/
theorem threeAnchor_syndrome_image (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v) :
    (Certificate.ThreeAnchor.syndrome s).image (fun j => (A j).val) = B.syndrome := by
  ext v
  constructor
  · rintro hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact (B.threeAnchor_mem_syndrome A s hrows j).mp hj
  · intro hv
    obtain ⟨j, rfl⟩ := hA v (B.syndrome_subset_anchors hv)
    exact Finset.mem_image.mpr ⟨j, (B.threeAnchor_mem_syndrome A s hrows j).mpr hv, rfl⟩

/-- A pair syndrome in the record specifies exactly the actual repair pair. -/
theorem threeAnchor_syndrome_pair (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (p q : Fin 3) (hs : Certificate.ThreeAnchor.syndrome s = {p, q}) :
    B.syndrome = {(A p).val, (A q).val} := by
  rw [← B.threeAnchor_syndrome_image A hA s hrows, hs]
  simp

/-- A nonzero finite row code is exactly a nonempty actual incidence row. -/
theorem threeAnchor_row_nonempty (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (i : Fin 5) : (B.row i).Nonempty ↔ s i ≠ 0 := by
  have hc : (∃ j : Fin 3, (rowMask (s i)).val.testBit j.val = true) ↔ s i ≠ 0 :=
    (by decide : ∀ c : Fin 4,
      (∃ j : Fin 3, (rowMask c).val.testBit j.val = true) ↔ c ≠ 0) (s i)
  rw [← hc]
  constructor
  · rintro ⟨v, hv⟩
    obtain ⟨j, hj, _⟩ := (hrows i v).mp hv
    exact ⟨j, hj⟩
  · rintro ⟨j, hj⟩
    exact ⟨(A j).val, (hrows i _).mpr ⟨j, hj, rfl⟩⟩

/-- Encoded private activity agrees with the manuscript's actual activity. -/
theorem threeAnchor_activity (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v) :
    (Finset.univ.filter fun i : Fin 5 => i ≠ 0 ∧ s i ≠ 0).card = B.activity := by
  unfold activity activePrivate
  congr 1
  ext i
  simp only [Finset.mem_filter, B.threeAnchor_row_nonempty A s hrows i]

end Gallai.WholeBowtie
