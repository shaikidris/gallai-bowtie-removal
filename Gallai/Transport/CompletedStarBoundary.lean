/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarWords

/-! # Original edges split into retained nonspokes and sparse local edges

This separation uses the actual original rows. Synthetic completion spokes
are never treated as retained original edges.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every sparse local edge meets an original bowtie vertex. -/
theorem completed_target_incident (A : B.AnchorNumbering) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    ∃ v ∈ Sym2.map (B.completedLabel A) e, v ∈ B.vertices := by
  have hi : ∃ i : Fin 5, core i ∈ e := by
    have hall : ∀ e : Sym2 Star.Vertex, e ∈ Star.activeEdges.toFinset →
        ∃ i : Fin 5, core i ∈ e := by
      intro e
      induction e using Sym2.inductionOn with
      | hf u v => cases u <;> cases v <;> decide
    exact hall e (targetEdges_subset _ he)
  obtain ⟨i, hi⟩ := hi
  refine ⟨B.label i, Sym2.mem_map.mpr ⟨core i, hi, B.completedLabel_core A i⟩, ?_⟩
  exact Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩

/-- A retained auxiliary nonspoke cannot be one of the local target edges. -/
theorem completed_retained_ne_target (A : B.AnchorNumbering) (f : Sym2 B.StarSurvivor)
    (hx : B.completedHub ∉ f) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    Sym2.map Subtype.val f ≠ Sym2.map (B.completedLabel A) e := by
  intro heq
  obtain ⟨v, hv, hvB⟩ := B.completed_target_incident A e he
  rw [← heq] at hv
  obtain ⟨w, hw, rfl⟩ := Sym2.mem_map.mp hv
  have hwx : w = B.completedHub := Subtype.ext (B.survivor_mem_vertices w hvB)
  exact hx (hwx ▸ hw)

/-- Every original edge is represented either by a retained auxiliary
nonspoke or by the sparse target, with no connectedness premise. -/
theorem completed_edge_cases (A : B.AnchorNumbering) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∃ f ∈ B.completedStar.edgeSet, B.completedHub ∉ f ∧ Sym2.map Subtype.val f = e) ∨
      ∃ f ∈ targetEdges (B.completedStarState A), Sym2.map (B.completedLabel A) f = e := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    change G.Adj u v at he
    by_cases hu : u ∈ B.vertices
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hu
      exact Or.inr (B.completedLabel_target_covers A i v he)
    by_cases hv : v ∈ B.vertices
    · obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hv
      obtain ⟨f, hf, hfuv⟩ := B.completedLabel_target_covers A i u he.symm
      exact Or.inr ⟨f, hf, hfuv.trans Sym2.eq_swap⟩
    · let U := B.completedOutside u hu
      let W := B.completedOutside v hv
      have hu0 : u ≠ B.label 0 := fun h =>
        hu (h ▸ Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
      have hv0 : v ≠ B.label 0 := fun h =>
        hv (h ▸ Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
      refine Or.inl ⟨s(U, W), (B.completedStar_adj_off_hub U W hu0 hv0).mpr he, ?_, rfl⟩
      simp only [Sym2.mem_iff, not_or]
      exact ⟨fun h => hu0 (congrArg Subtype.val h).symm,
        fun h => hv0 (congrArg Subtype.val h).symm⟩

end Gallai.WholeBowtie
