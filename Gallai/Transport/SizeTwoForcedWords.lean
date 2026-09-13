/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoForced
import Gallai.Transport.SizeTwoWords

/-! # Actual paths for the forced size-two reconstruction

The connector and optional s-tail share a carrier; the extra endpoint tail
does not. Only the former pair needs disjoint fresh support. All realized
edges belong to the original graph, not to a repaired auxiliary.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (j : Fin 2)
variable (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex))
variable (h : Forced.AcceptedRecord (B.completedStarState A) j connector extra tail added)

/-- A local forced word is interpreted as a nonempty simple path in G. -/
noncomputable def sizeTwoForcedWord (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added) : NonemptyPath G :=
  B.realizeOriginalMember A _ h.2.2.2.2.1 word hw

/-- The exact symbolic support is retained. -/
theorem sizeTwoForcedWord_support (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).walk.support =
      word.map (B.completedLabel A) :=
  B.realizeOriginalMember_support A _ h.2.2.2.2.1 word hw

/-- Edge multiplicities are those of the checked word under the actual labels. -/
theorem sizeTwoForcedWord_edges (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.completedLabel A)) :=
  B.realizeOriginalMember_edges A _ h.2.2.2.2.1 word hw

/-- First-symbol data determines the actual attachment. -/
theorem sizeTwoForcedWord_start (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added)
    (u : Star.Vertex) (hu : word.head? = some u) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).start =
      B.completedLabel A u := by
  have he := congrArg List.head?
    (B.sizeTwoForcedWord_support A j connector extra tail added h word hw)
  rw [List.head?_map,hu] at he
  rw [List.head?_eq_some_head (by simp),SimpleGraph.Walk.head_support] at he
  exact Option.some.inj he

/-- Last-symbol data determines the other connector attachment. -/
theorem sizeTwoForcedWord_finish (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added)
    (u : Star.Vertex) (hu : word.getLast? = some u) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).finish =
      B.completedLabel A u := by
  have he := congrArg List.getLast?
    (B.sizeTwoForcedWord_support A j connector extra tail added h word hw)
  rw [List.getLast?_map,hu] at he
  rw [List.getLast?_eq_some_getLast (by simp),SimpleGraph.Walk.getLast_support] at he
  exact Option.some.inj he

/-- Either endpoint tail contains no old vertex other than its attachment. -/
theorem sizeTwoForcedWord_single (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added)
    (u : Star.Vertex) (hu : Compatible [u] Star.fresh.toFinset word) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).start =
        B.completedLabel A u ∧
    ∀ v ∈ (B.sizeTwoForcedWord A j connector extra tail added h word hw).walk.support,
      v = B.completedLabel A u ∨ v ∈ B.vertices := by
  refine ⟨B.sizeTwoForcedWord_start A j connector extra tail added h word hw u hu.1,?_⟩
  intro v hv
  rw [B.sizeTwoForcedWord_support] at hv
  obtain ⟨w,hw',rfl⟩ := List.mem_map.mp hv
  rcases compatible_single_support hu hw' with he | hf
  · exact Or.inl (congrArg (B.completedLabel A) he)
  · exact Or.inr (B.completedLabel_fresh A w hf)

/-- The connector can traverse the released hub but no unused old anchor. -/
theorem sizeTwoForcedWord_pair (word : List Star.Vertex)
    (hw : word ∈ Forced.localWords connector extra tail added)
    (u w : Star.Vertex) (hu : Compatible [u,w] Star.fresh.toFinset word) :
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).start =
        B.completedLabel A u ∧
    (B.sizeTwoForcedWord A j connector extra tail added h word hw).finish =
        B.completedLabel A w ∧
    ∀ v : B.StarSurvivor,
      v.val ∈ (B.sizeTwoForcedWord A j connector extra tail added h word hw).walk.support →
      v.val = B.completedLabel A u ∨ v.val = B.completedLabel A w ∨ v.val = B.label 0 := by
  refine ⟨B.sizeTwoForcedWord_start A j connector extra tail added h word hw u hu.1,
    B.sizeTwoForcedWord_finish A j connector extra tail added h word hw w hu.2.1,?_⟩
  intro v hv
  rw [B.sizeTwoForcedWord_support] at hv
  obtain ⟨t,ht,htv⟩ := List.mem_map.mp hv
  rcases compatible_pair_support hu ht with he | he | hf
  · exact Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he))
  · exact Or.inr (Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he)))
  · exact Or.inr (Or.inr (B.survivor_mem_vertices v
      (htv ▸ B.completedLabel_fresh A t hf)))

/-- Checked fresh disjointness transfers to actual path supports. -/
theorem sizeTwoForcedWord_disjoint (word₁ word₂ : List Star.Vertex)
    (h₁ : word₁ ∈ Forced.localWords connector extra tail added)
    (h₂ : word₂ ∈ Forced.localWords connector extra tail added)
    (hd : Disjoint (internal word₁) (internal word₂)) :
    Disjoint
      ((B.sizeTwoForcedWord A j connector extra tail added h word₁ h₁).freshSupport B.vertices)
      ((B.sizeTwoForcedWord A j connector extra tail added h word₂ h₂).freshSupport B.vertices) := by
  apply Finset.disjoint_left.mpr
  intro v hv₁ hv₂
  obtain ⟨hv₁,hB⟩ := Finset.mem_inter.mp hv₁
  obtain ⟨hv₂,_⟩ := Finset.mem_inter.mp hv₂
  have hv₁' := List.mem_toFinset.mp hv₁
  have hv₂' := List.mem_toFinset.mp hv₂
  rw [B.sizeTwoForcedWord_support] at hv₁' hv₂'
  obtain ⟨u,hu,huv⟩ := List.mem_map.mp hv₁'
  obtain ⟨w,hw,hwv⟩ := List.mem_map.mp hv₂'
  have huw := B.completedLabel_injective A (huv.trans hwv.symm)
  subst w
  have hf := (B.completedLabel_mem_core_iff A u).mp (huv.symm ▸ hB)
  exact Finset.disjoint_left.mp hd
    (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hu,hf⟩)
    (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hw,hf⟩)

end Gallai.WholeBowtie
