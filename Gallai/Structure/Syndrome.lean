/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie
import Mathlib.Data.Finset.SymmDiff

/-! # Syndrome parity and the complete four-anchor size restriction -/

namespace Gallai

open scoped Finset symmDiff

universe u

variable {V : Type u} [DecidableEq V]

/-- Symmetric difference preserves even cardinality of two finite sets. -/
theorem even_card_symmDiff (s t : Finset V) (hs : Even #s) (ht : Even #t) :
    Even #(s ∆ t) := by
  have hd : Disjoint (s \ t) (t \ s) := by
    apply Finset.disjoint_left.mpr
    intro v hv hw
    exact (Finset.mem_sdiff.mp hv).2 (Finset.mem_sdiff.mp hw).1
  have h₁ := Finset.card_sdiff_add_card_inter s t
  have h₂ := Finset.card_sdiff_add_card_inter t s
  rw [Finset.inter_comm t s] at h₂
  rw [Finset.symmDiff_def, Finset.card_union_of_disjoint hd, Nat.even_iff]
  rw [Nat.even_iff] at hs ht
  omega

private theorem symmDiff_subset_of_subset {s t A : Finset V}
    (hs : s ⊆ A) (ht : t ⊆ A) : s ∆ t ⊆ A :=
  Finset.symmDiff_subset_union.trans (Finset.union_subset hs ht)

namespace WholeBowtie

variable [Fintype V] {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The parity syndrome of all five external incidence rows. -/
def syndrome : Finset V := B.row 0 ∆ (B.row 1 ∆ (B.row 2 ∆ (B.row 3 ∆ B.row 4)))

/-- Every incidence row belongs to the complete anchor set. -/
theorem row_subset_anchors (i : Fin 5) : B.row i ⊆ B.anchors := by
  intro v hv
  exact (B.mem_anchors v).mpr ⟨i, hv⟩

/-- No syndrome vertex lies outside the actual anchor set. -/
theorem syndrome_subset_anchors : B.syndrome ⊆ B.anchors := by
  exact symmDiff_subset_of_subset (B.row_subset_anchors 0)
    (symmDiff_subset_of_subset (B.row_subset_anchors 1)
      (symmDiff_subset_of_subset (B.row_subset_anchors 2)
        (symmDiff_subset_of_subset (B.row_subset_anchors 3) (B.row_subset_anchors 4))))

/-- Evenness of all five rows forces evenness of their syndrome. -/
theorem even_card_syndrome : Even #B.syndrome := by
  exact even_card_symmDiff _ _ (B.even_card_row 0)
    (even_card_symmDiff _ _ (B.even_card_row 1)
      (even_card_symmDiff _ _ (B.even_card_row 2)
        (even_card_symmDiff _ _ (B.even_card_row 3) (B.even_card_row 4))))

/-- With at most four anchors, the three syndrome sizes zero, two and four are exhaustive. -/
theorem syndrome_card_cases (hA : #B.anchors ≤ 4) :
    #B.syndrome = 0 ∨ #B.syndrome = 2 ∨ #B.syndrome = 4 := by
  have hle := (Finset.card_le_card B.syndrome_subset_anchors).trans hA
  have he := Nat.even_iff.mp B.even_card_syndrome
  omega

end WholeBowtie
end Gallai
