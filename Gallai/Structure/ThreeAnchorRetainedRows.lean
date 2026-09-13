/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubCap
import Gallai.Structure.ThreeAnchorRows
import Gallai.Certificates.ThreeAnchorRetained

/-! # Finite private syndromes identify actual retained-hub repairs -/
namespace Gallai.WholeBowtie
open Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A whole-deletion slot also survives private deletion. -/
def retainedSlot (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (j : Fin 3) :
    B.StarSurvivor := ⟨(A j).val, by
  intro h
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp h
  exact (A j).property (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩)⟩

variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows

/-- Private column counts equal the exact number of incident edges deleted. -/
theorem threeAnchor_private_column_count (j : Fin 3) :
    (Finset.univ.filter fun i : Fin 5 =>
      i ≠ 0 ∧ (rowMask (s i)).val.testBit j.val = true).card =
      (G.neighborFinset (A j).val ∩ (Finset.univ.erase 0).map B.label).card := by
  have he : (Finset.univ.filter fun i : Fin 5 =>
      i ≠ 0 ∧ (rowMask (s i)).val.testBit j.val = true).map B.label =
      G.neighborFinset (A j).val ∩ (Finset.univ.erase 0).map B.label := by
    ext v
    constructor
    · intro hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨hn, hb⟩ := (Finset.mem_filter.mp hi).2
      have hr := (hrows i _).mpr ⟨j, hb, rfl⟩
      exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr
        ((B.mem_row i _).mp hr).1.symm,
        Finset.mem_map.mpr ⟨i, by simp [hn], rfl⟩⟩
    · intro hv
      obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hv
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hm
      have hr := (B.mem_row i _).mpr
        ⟨((G.mem_neighborFinset _ _).mp ha).symm, (A j).property⟩
      obtain ⟨k, hk, he⟩ := (hrows i _).mp hr
      have hkj : k = j := A.injective (Subtype.ext he)
      exact Finset.mem_map.mpr ⟨i, Finset.mem_filter.mpr
        ⟨Finset.mem_univ _, (Finset.mem_erase.mp hi).1, hkj ▸ hk⟩, rfl⟩
  simpa only [Finset.card_map] using congrArg Finset.card he

/-- Finite private-syndrome membership agrees with the actual auxiliary. -/
theorem threeAnchor_private_mem (j : Fin 3) :
    j ∈ privateSyndrome s ↔ B.retainedSlot A j ∈ B.privateDeletionSyndrome := by
  simp only [privateSyndrome, privateDeletionSyndrome, Finset.mem_filter,
    Finset.mem_univ, true_and]
  change Odd _ ↔ Odd (G.neighborFinset (A j).val ∩
    (Finset.univ.erase 0).map B.label).card
  rw [B.threeAnchor_private_column_count A s hrows j]

/-- Coverage transfers the complete syndrome, including unused finite slots. -/
theorem threeAnchor_private_image
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v) :
    (privateSyndrome s).image (B.retainedSlot A) = B.privateDeletionSyndrome := by
  ext v
  constructor
  · intro hv
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp hv
    exact (B.threeAnchor_private_mem A s hrows j).mp hj
  · intro hv
    obtain ⟨j, hj⟩ := hcover v.val (B.privateDeletionSyndrome_anchor v hv)
    have he : B.retainedSlot A j = v := Subtype.ext hj
    exact Finset.mem_image.mpr ⟨j,
      (B.threeAnchor_private_mem A s hrows j).mpr (he.symm ▸ hv), he⟩

/-- A finite pair determines the actual two repair vertices. -/
theorem threeAnchor_private_pair
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (p q : Fin 3) (hs : privateSyndrome s = {p,q}) :
    B.privateDeletionSyndrome = {B.retainedSlot A p, B.retainedSlot A q} := by
  rw [← B.threeAnchor_private_image A s hrows hcover, hs]
  simp

/-- A finite empty syndrome certifies that no repair is needed. -/
theorem threeAnchor_private_empty
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hs : privateSyndrome s = ∅) : B.privateDeletionSyndrome = ∅ := by
  rw [← B.threeAnchor_private_image A s hrows hcover, hs]
  simp

/-- Every encoded three-anchor row has at most two entries, so the retained
hub meets the cap without a separately supplied degree bound. -/
theorem threeAnchor_retained_degree_le : B.retainedHubGraph.degree B.completedHub ≤ 2 := by
  rw [B.retainedHub_degree]
  let T : Finset (Fin 3) := Finset.univ.filter fun j =>
    (rowMask (s 0)).val.testBit j.val = true
  have he : T.image (fun j => (A j).val) = B.row 0 := by
    ext v
    simp only [Finset.mem_image, T, Finset.mem_filter, Finset.mem_univ, true_and]
    exact (hrows 0 v).symm
  have hc := Finset.card_image_le (s := T) (f := fun j => (A j).val)
  rw [he] at hc
  have hb : T.card ≤ 2 :=
    (by decide : ∀ c : Fin 4, (Finset.univ.filter fun j : Fin 3 =>
      (rowMask c).val.testBit j.val = true).card ≤ 2) (s 0)
  exact hc.trans hb

end Gallai.WholeBowtie
