/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoRich
import Gallai.Transport.SizeTwoWords

/-! # Rich-reserve words realized as original-graph paths

These paths consume the rich contract, not the ordinary same-owner contract.
Each nonempty role has exact edges and support; connector endpoints and old
vertex avoidance provide the inputs to the component-safe merging lemmas.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (i : Fin 4)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Rich.AcceptedRecord (B.completedStarState A) i words added)

/-- Each nonempty rich role is a simple nonempty path using original edges. -/
noncomputable def sizeTwoRichRole (j : Fin 4) (hj : words j ≠ []) : NonemptyPath G :=
  B.realizeOriginalMember A (activeWords words ++ added) h.2.1 (words j)
    (active_word_mem words added j hj)

/-- Literal support of the realized role. -/
theorem sizeTwoRichRole_support (j : Fin 4) (hj : words j ≠ []) :
    (B.sizeTwoRichRole A i words added h j hj).walk.support =
      (words j).map (B.completedLabel A) :=
  B.realizeOriginalMember_support A _ h.2.1 _ _

/-- Literal edge accounting of the realized role. -/
theorem sizeTwoRichRole_edges (j : Fin 4) (hj : words j ≠ []) :
    (B.sizeTwoRichRole A i words added h j hj).walk.edges =
      (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) :=
  B.realizeOriginalMember_edges A _ h.2.1 _ _

/-- A specified initial symbol determines the actual start vertex. -/
theorem sizeTwoRichRole_start (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hu : (words j).head? = some u) :
    (B.sizeTwoRichRole A i words added h j hj).start = B.completedLabel A u := by
  have he := congrArg List.head? (B.sizeTwoRichRole_support A i words added h j hj)
  rw [List.head?_map,hu] at he
  rw [List.head?_eq_some_head (by simp),SimpleGraph.Walk.head_support] at he
  exact Option.some.inj he

/-- A specified final symbol determines the actual finish vertex. -/
theorem sizeTwoRichRole_finish (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hu : (words j).getLast? = some u) :
    (B.sizeTwoRichRole A i words added h j hj).finish = B.completedLabel A u := by
  have he := congrArg List.getLast? (B.sizeTwoRichRole_support A i words added h j hj)
  rw [List.getLast?_map,hu] at he
  rw [List.getLast?_eq_some_getLast (by simp),SimpleGraph.Walk.getLast_support] at he
  exact Option.some.inj he

/-- A nonempty optional tail avoids every unused surviving vertex. -/
theorem sizeTwoRichRole_single (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hb : Rich.boundary i j = [u]) :
    (B.sizeTwoRichRole A i words added h j hj).start = B.completedLabel A u ∧
    ∀ v ∈ (B.sizeTwoRichRole A i words added h j hj).walk.support,
      v = B.completedLabel A u ∨ v ∈ B.vertices := by
  have hr := Rich.role_compatible (h.1 j) hj
  rw [hb] at hr
  refine ⟨B.sizeTwoRichRole_start A i words added h j hj u hr.1,?_⟩
  intro v hv
  rw [B.sizeTwoRichRole_support] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  rcases compatible_single_support hr hw with he | hf
  · exact Or.inl (congrArg (B.completedLabel A) he)
  · exact Or.inr (B.completedLabel_fresh A w hf)

/-- A rich connector supplies the exact two attachments and the released-hub
exception required by the component-safe arm merging API. -/
theorem sizeTwoRichRole_pair (j : Fin 4) (hj : words j ≠ [])
    (u w : Star.Vertex) (hb : Rich.boundary i j = [u,w]) :
    (B.sizeTwoRichRole A i words added h j hj).start = B.completedLabel A u ∧
    (B.sizeTwoRichRole A i words added h j hj).finish = B.completedLabel A w ∧
    ∀ v : B.StarSurvivor,
      v.val ∈ (B.sizeTwoRichRole A i words added h j hj).walk.support →
      v.val = B.completedLabel A u ∨ v.val = B.completedLabel A w ∨
        v.val = B.label 0 := by
  have hr := Rich.role_compatible (h.1 j) hj
  rw [hb] at hr
  refine ⟨B.sizeTwoRichRole_start A i words added h j hj u hr.1,
    B.sizeTwoRichRole_finish A i words added h j hj w hr.2.1,?_⟩
  intro v hv
  rw [B.sizeTwoRichRole_support] at hv
  obtain ⟨t,ht,htv⟩ := List.mem_map.mp hv
  rcases compatible_pair_support hr ht with he | he | hf
  · exact Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he))
  · exact Or.inr (Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he)))
  · exact Or.inr (Or.inr (B.survivor_mem_vertices v
      (htv ▸ B.completedLabel_fresh A t hf)))

end Gallai.WholeBowtie
