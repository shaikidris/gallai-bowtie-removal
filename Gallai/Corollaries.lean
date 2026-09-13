/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.TheoremA
import Gallai.Structure.TwoBowtieKernel

/-! # The two-bowtie corollaries of Theorem A -/
namespace Gallai.TwoBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {X Y : WholeBowtie G}

/-- A small anchor set at the first bowtie exposes the other centre. -/
theorem Kernel.expose_other (h : Kernel X Y) (hc : G.Connected)
    (ha : X.anchors.card ≤ 4) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ D.endpointCount (Y.label 0) := by
  obtain ⟨D, hD, hy, _⟩ := X.theoremA hc (Y.label 0) h.hub_out
    (Y.even_degree_label 0) h.exception_cap (Or.inl ha)
  exact ⟨D, hD, hy⟩

/-- Corollary A1: either prescribed centre can be exposed when there are at
most four odd vertices. The two choices need not use the same decomposition. -/
theorem corollaryA1 (hc : G.Connected) (h : Kernel X Y)
    (ho : (oddVertices G).card ≤ 4) :
    ∀ z ∈ ({X.label 0, Y.label 0} : Finset V),
      ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
        2 ≤ D.endpointCount z := by
  intro z hz
  simp only [Finset.mem_insert, Finset.mem_singleton] at hz
  rcases hz with rfl | rfl
  · exact h.symm.expose_other hc ((Finset.card_le_card (anchors_subset_odd Y)).trans ho)
  · exact h.expose_other hc ((Finset.card_le_card (anchors_subset_odd X)).trans ho)

end Gallai.TwoBowtie
