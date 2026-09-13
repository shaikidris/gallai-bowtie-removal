/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie
import Gallai.Certificates.ThreeAnchorRetainedOrbits

/-! # Actual whole-bowtie relabelling for retained normalization -/
namespace Gallai.WholeBowtie
open Certificate.ThreeAnchor.RetainedOrbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem retainedCore_preserves : ∀ c : Fin 8, ∀ i j : Fin 5,
    bowtieGraph.Adj (coreOrder c i) (coreOrder c j) ↔ bowtieGraph.Adj i j := by decide

/-- Relabel the same whole component by a certified bowtie automorphism. -/
def retainedRelabel (c : Fin 8) : WholeBowtie G where
  label := ⟨fun i => B.label (coreOrder c i), B.label.injective.comp (coreOrder_bijective c).1⟩
  component := B.component
  component_vertices := by
    rw [B.component_vertices]
    ext v
    constructor
    · rintro ⟨i,rfl⟩
      obtain ⟨j,hj⟩ := (coreOrder_bijective c).2 i
      exact ⟨j,congrArg B.label hj⟩
    · rintro ⟨i,rfl⟩
      exact ⟨coreOrder c i,rfl⟩
  adj_iff := fun i j => (B.adj_iff _ _).trans (retainedCore_preserves c i j)

theorem retainedRelabel_hub (c : Fin 8) : (B.retainedRelabel c).label 0 = B.label 0 := by
  change B.label (coreOrder c 0) = _
  rw [coreOrder_zero]

theorem retainedRelabel_vertices (c : Fin 8) : (B.retainedRelabel c).vertices = B.vertices := by
  ext v
  rw [(B.retainedRelabel c).mem_vertices, B.mem_vertices]
  rfl

theorem retainedRelabel_row (c : Fin 8) (j : Fin 5) :
    (B.retainedRelabel c).row j = B.row (coreOrder c j) := by
  ext v
  rw [(B.retainedRelabel c).mem_row, B.mem_row, B.retainedRelabel_vertices]
  rfl

theorem retainedRelabel_anchors (c : Fin 8) : (B.retainedRelabel c).anchors = B.anchors := by
  ext v
  rw [(B.retainedRelabel c).mem_anchors, B.mem_anchors]
  constructor
  · rintro ⟨j,hj⟩
    exact ⟨coreOrder c j,by simpa only [B.retainedRelabel_row] using hj⟩
  · rintro ⟨j,hj⟩
    obtain ⟨k,hk⟩ := (coreOrder_bijective c).2 j
    exact ⟨k,by simpa only [B.retainedRelabel_row,hk] using hj⟩

end Gallai.WholeBowtie
