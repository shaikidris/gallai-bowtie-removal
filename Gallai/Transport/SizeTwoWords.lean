/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoOrdinary
import Gallai.Transport.ZeroSyndromeWords
import Gallai.Transport.FreshCarrierTail

/-! # Ordinary size-two records realized in the original graph

The checked words supply actual simple paths and same-carrier freshness.
Empty optional words remain absent, not zero-edge paths.
-/
namespace Gallai.Certificate.SizeTwo

theorem active_word_mem (words : Fin 4 → List Vertex) (added : List (List Vertex))
    (j : Fin 4) (hj : words j ≠ []) : words j ∈ activeWords words ++ added := by
  apply List.mem_append_left
  apply List.mem_filter.mpr
  exact ⟨List.mem_ofFn.mpr ⟨j,rfl⟩,by simpa using hj⟩

theorem roleAccepted_compatible {i : Fin 13} {j : Fin 4} {word : List Vertex}
    (h : roleAccepted i j word) (hne : word ≠ []) :
    Compatible (boundary i j) Star.fresh.toFinset word := by
  unfold roleAccepted at h
  split at h
  · exact (hne h).elim
  · exact h.resolve_left (fun he => hne he.1)

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The finite core is exactly the preimage of the ambient bowtie. -/
theorem completedLabel_mem_core_iff (A : B.AnchorNumbering) (v : Star.Vertex) :
    B.completedLabel A v ∈ B.vertices ↔ v ∈ Star.fresh.toFinset := by
  refine ⟨?_, B.completedLabel_fresh A v⟩
  intro hv
  cases v <;> solve
    | simp [Star.fresh]
    | exact (B.numberedAnchor_not_mem A 0 hv).elim
    | exact (B.numberedAnchor_not_mem A 1 hv).elim
    | exact (B.numberedAnchor_not_mem A 2 hv).elim
    | exact (B.numberedAnchor_not_mem A 3 hv).elim

variable (A : B.AnchorNumbering) (i : Fin 13)
variable (words : Fin 4 → List Star.Vertex) (added : List (List Star.Vertex))
variable (h : OrdinaryAccepted (B.completedStarState A) i words added)

/-- Each used role is realized using only original edges, including old spokes
that the local reconstruction deliberately releases and redistributes. -/
noncomputable def sizeTwoRole (j : Fin 4) (hj : words j ≠ []) : NonemptyPath G :=
  B.realizeOriginalMember A (activeWords words ++ added) h.2.2.1 (words j)
    (active_word_mem words added j hj)

theorem sizeTwoRole_support (j : Fin 4) (hj : words j ≠ []) :
    (B.sizeTwoRole A i words added h j hj).walk.support =
      (words j).map (B.completedLabel A) :=
  B.realizeOriginalMember_support A _ h.2.2.1 _ _

theorem sizeTwoRole_edges (j : Fin 4) (hj : words j ≠ []) :
    (B.sizeTwoRole A i words added h j hj).walk.edges =
      (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) :=
  B.realizeOriginalMember_edges A _ h.2.2.1 _ _

/-- Literal first-symbol data determines the actual attachment vertex. -/
theorem sizeTwoRole_start (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hu : (words j).head? = some u) :
    (B.sizeTwoRole A i words added h j hj).start = B.completedLabel A u := by
  have he := congrArg List.head? (B.sizeTwoRole_support A i words added h j hj)
  rw [List.head?_map,hu] at he
  rw [List.head?_eq_some_head (by simp),SimpleGraph.Walk.head_support] at he
  exact Option.some.inj he

theorem sizeTwoRole_finish (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hu : (words j).getLast? = some u) :
    (B.sizeTwoRole A i words added h j hj).finish = B.completedLabel A u := by
  have he := congrArg List.getLast? (B.sizeTwoRole_support A i words added h j hj)
  rw [List.getLast?_map,hu] at he
  rw [List.getLast?_eq_some_getLast (by simp),SimpleGraph.Walk.getLast_support] at he
  exact Option.some.inj he

/-- A terminal record directly supplies the support premise for appendFresh. -/
theorem sizeTwoRole_single (j : Fin 4) (hj : words j ≠ [])
    (u : Star.Vertex) (hb : boundary i j = [u]) :
    (B.sizeTwoRole A i words added h j hj).start = B.completedLabel A u ∧
    ∀ v ∈ (B.sizeTwoRole A i words added h j hj).walk.support,
      v = B.completedLabel A u ∨ v ∈ B.vertices := by
  have hr := roleAccepted_compatible (h.1 j) hj
  rw [hb] at hr
  refine ⟨B.sizeTwoRole_start A i words added h j hj u hr.1,?_⟩
  intro v hv
  rw [B.sizeTwoRole_support] at hv
  obtain ⟨w,hw,rfl⟩ := List.mem_map.mp hv
  rcases compatible_single_support hr hw with he | hf
  · exact Or.inl (congrArg (B.completedLabel A) he)
  · exact Or.inr (B.completedLabel_fresh A w hf)

/-- A connector record supplies both actual endpoints and excludes every
other surviving vertex except the released hub. -/
theorem sizeTwoRole_pair (j : Fin 4) (hj : words j ≠ [])
    (u w : Star.Vertex) (hb : boundary i j = [u,w]) :
    (B.sizeTwoRole A i words added h j hj).start = B.completedLabel A u ∧
    (B.sizeTwoRole A i words added h j hj).finish = B.completedLabel A w ∧
    ∀ v : B.StarSurvivor,
      v.val ∈ (B.sizeTwoRole A i words added h j hj).walk.support →
      v.val = B.completedLabel A u ∨ v.val = B.completedLabel A w ∨
        v.val = B.label 0 := by
  have hr := roleAccepted_compatible (h.1 j) hj
  rw [hb] at hr
  refine ⟨B.sizeTwoRole_start A i words added h j hj u hr.1,
    B.sizeTwoRole_finish A i words added h j hj w hr.2.1,?_⟩
  intro v hv
  rw [B.sizeTwoRole_support] at hv
  obtain ⟨t,ht,htv⟩ := List.mem_map.mp hv
  rcases compatible_pair_support hr ht with he | he | hf
  · exact Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he))
  · exact Or.inr (Or.inl (htv.symm.trans (congrArg (B.completedLabel A) he)))
  · exact Or.inr (Or.inr (B.survivor_mem_vertices v
      (htv ▸ B.completedLabel_fresh A t hf)))

/-- Optional roles are absent exactly when the stored word is empty. -/
noncomputable def sizeTwoOptionalRole (j : Fin 4) : Option (NonemptyPath G) :=
  if hj : words j = [] then none else some (B.sizeTwoRole A i words added h j hj)

theorem sizeTwoOptionalRole_mem (j : Fin 4) (T : NonemptyPath G)
    (hT : T ∈ B.sizeTwoOptionalRole A i words added h j) :
    ∃ hj : words j ≠ [], T = B.sizeTwoRole A i words added h j hj := by
  unfold sizeTwoOptionalRole at hT
  split at hT
  · simp at hT
  · rename_i hj
    exact ⟨hj,(show B.sizeTwoRole A i words added h j hj = T from
      by simpa only [Option.mem_some_iff] using hT).symm⟩

/-- Optional-word edge accounting has no exceptional empty-word term. -/
theorem sizeTwoOptionalRole_edges (j : Fin 4) :
    ((B.sizeTwoOptionalRole A i words added h j).map (fun T => T.walk.edges)).getD [] =
      (wordEdges (words j)).map (Sym2.map (B.completedLabel A)) := by
  unfold sizeTwoOptionalRole
  split
  · rename_i hj
    simp [hj,wordEdges]
  · simpa only [Option.map_some,Option.getD_some] using
      B.sizeTwoRole_edges A i words added h j ‹words j ≠ []›

/-- Same-owner finite footprint checks imply disjointness of the realized
core supports, even though the old carriers need not avoid other anchors. -/
theorem sizeTwoRole_same_owner_disjoint (j k : Fin 4)
    (hj : words j ≠ []) (hk : words k ≠ []) (hne : j ≠ k)
    (ho : owner i j = owner i k) :
    Disjoint ((B.sizeTwoRole A i words added h j hj).freshSupport B.vertices)
      ((B.sizeTwoRole A i words added h k hk).freshSupport B.vertices) := by
  apply Finset.disjoint_left.mpr
  intro v hvj hvk
  obtain ⟨hvj,hB⟩ := Finset.mem_inter.mp hvj
  obtain ⟨hvk,_⟩ := Finset.mem_inter.mp hvk
  have hvj' := List.mem_toFinset.mp hvj
  have hvk' := List.mem_toFinset.mp hvk
  rw [B.sizeTwoRole_support] at hvj' hvk'
  obtain ⟨u,hu,huv⟩ := List.mem_map.mp hvj'
  obtain ⟨w,hw,hwv⟩ := List.mem_map.mp hvk'
  have huw := B.completedLabel_injective A (huv.trans hwv.symm)
  subst w
  have hf := (B.completedLabel_mem_core_iff A u).mp (huv.symm ▸ hB)
  exact Finset.disjoint_left.mp (h.2.1 j k hne ho)
    (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hu,hf⟩)
    (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hw,hf⟩)

end Gallai.WholeBowtie
