/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarAuxiliary
import Gallai.Structure.EdgeToggle

/-! # Private deletion with the original hub retained

Unlike star completion, this auxiliary adds no hub spokes. Its repair toggles
an actual anchor edge and restores precisely the private-deletion syndrome.
-/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Delete the four private vertices, without completing the retained star. -/
abbrev retainedHubGraph : SimpleGraph B.StarSurvivor :=
  B.privateDeletion (Finset.univ.erase 0)

/-- The original hub retains exactly its original external row. -/
theorem retainedHub_adj (v : B.StarSurvivor) :
    B.retainedHubGraph.Adj B.completedHub v ↔ v.val ∈ B.row 0 := by
  change G.Adj (B.label 0) v.val ↔ _
  constructor
  · intro ha
    exact (B.mem_row 0 _).mpr ⟨ha, fun h =>
      ha.ne (B.survivor_mem_vertices v h).symm⟩
  · intro h
    exact ((B.mem_row 0 _).mp h).1

/-- Neighbour correspondence is independent of the rest of the graph. -/
def retainedHubNeighborEquiv : B.retainedHubGraph.neighborSet B.completedHub ≃
    {v // v ∈ B.row 0} where
  toFun v := ⟨v.val.val, (B.retainedHub_adj v.val).mp v.property⟩
  invFun v := ⟨⟨v.val, B.anchor_survives ((B.mem_anchors _).mpr ⟨0, v.property⟩)⟩,
    (B.retainedHub_adj _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- A two-anchor hub row gives the degree-two carrier interface. -/
theorem retainedHub_degree : B.retainedHubGraph.degree B.completedHub = (B.row 0).card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr B.retainedHubNeighborEquiv).trans (Fintype.card_coe _)

/-- Exact parity defect from deleting only private vertices. -/
def privateDeletionSyndrome : Finset B.StarSurvivor :=
  Finset.univ.filter fun v => Odd
    (G.neighborFinset v.val ∩ (Finset.univ.erase 0).map B.label).card

/-- Degree balance identifies the syndrome without a row-count oracle. -/
theorem retainedHub_parity_eq_iff (v : B.StarSurvivor) :
    B.retainedHubGraph.degree v % 2 = G.degree v.val % 2 ↔
      v ∉ B.privateDeletionSyndrome := by
  have hd := B.privateDeletion_degree_add_deleted (Finset.univ.erase 0) v
  change B.retainedHubGraph.degree v +
    (G.neighborFinset v.val ∩ (Finset.univ.erase 0).map B.label).card =
      G.degree v.val at hd
  simp only [privateDeletionSyndrome, Finset.mem_filter, Finset.mem_univ,
    true_and, Nat.odd_iff]
  omega

/-- Repair the private syndrome by toggling its actual pair. -/
abbrev retainedHubRepair (p q : B.StarSurvivor) : SimpleGraph B.StarSurvivor :=
  toggleEdge B.retainedHubGraph p q

/-- Both original-edge and synthetic-edge repairs restore all survivor parities. -/
theorem retainedHubRepair_even_iff (p q : B.StarSurvivor) (hne : p ≠ q)
    (hs : B.privateDeletionSyndrome = {p,q}) (v : B.StarSurvivor) :
    Even ((B.retainedHubRepair p q).degree v) ↔ Even (G.degree v.val) := by
  have hp : B.retainedHubGraph.degree v % 2 = G.degree v.val % 2 ↔
      ¬ (v = p ∨ v = q) := by
    simpa only [hs, Finset.mem_insert, Finset.mem_singleton] using
      B.retainedHub_parity_eq_iff v
  rw [toggleEdge_even_iff B.retainedHubGraph p q hne v]
  by_cases hv : v = p ∨ v = q
  · have hn : B.retainedHubGraph.degree v % 2 ≠ G.degree v.val % 2 :=
      fun he => hp.mp he hv
    simp only [if_pos hv, Nat.even_iff]
    omega
  · have he := hp.mpr hv
    simp only [if_neg hv, Nat.even_iff]
    omega

/-- Empty private syndrome requires no repair at all. -/
theorem retainedHub_even_iff (hs : B.privateDeletionSyndrome = ∅)
    (v : B.StarSurvivor) :
    Even (B.retainedHubGraph.degree v) ↔ Even (G.degree v.val) := by
  have hp := (B.retainedHub_parity_eq_iff v).mpr (by simp [hs])
  simp only [Nat.even_iff, hp]

end Gallai.WholeBowtie
