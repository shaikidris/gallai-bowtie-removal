/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.InactiveBowtieCross
import Gallai.Operations.InactiveBowtieTriangle
import Gallai.Operations.DecompositionInduce
import Gallai.Structure.InactiveBowtieDeletion

/-! # Inactive restoration interfaces for family induction

The input decomposition is arbitrary. No one-exception theorem is used;
the family induction will supply this decomposition on the smaller graph.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Cross-pair restoration in the exact deletion subtype used by the family. -/
theorem inactive_cross_family_lift (left right : Bool)
    (h1 : B.row (bowtieCrossLabels left right 1) = ∅)
    (h3 : B.row (bowtieCrossLabels left right 3) = ∅)
    (D : Decomposition (B.privateDeletion
      {bowtieCrossLabels left right 1, bowtieCrossLabels left right 3})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v, v.val ∉ B.vertices → E.endpointCount v.val = D.endpointCount v := by
  classical
  let f := bowtieCrossLabels left right
  have hset : {v : V | v ∉ ({f 1, f 3} : Finset (Fin 5)).map B.label} =
      {v | v ≠ B.label (f 1) ∧ v ≠ B.label (f 3)} := by
    ext v
    simp
  obtain ⟨D', hs, he⟩ := D.induce_set_congr hset
  obtain ⟨E, hE, hc⟩ := B.restore_inactive_cross left right h1 h3 D'
  refine ⟨E, hE.trans (congrArg (fun n => n + 1) hs), ?_⟩
  intro v hv
  have haway (i : Fin 5) : v.val ≠ B.label i := by
    intro h
    exact hv (h ▸ (B.mem_vertices (B.label i)).mpr (B.label_mem_component i))
  rw [hc ⟨v.val, haway (f 1), haway (f 3)⟩ (haway (f 2)) (haway (f 4))]
  exact he v

/-- Same-triangle restoration preserves every outside endpoint in the family subtype. -/
theorem inactive_triangle_family_lift (right : Bool)
    (hrows : ∀ i : Fin 3, i ≠ 0 → B.row (bowtieTriangle right i) = ∅)
    (D : Decomposition (B.privateDeletion
      {bowtieTriangle right 1, bowtieTriangle right 2})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v, v.val ∉ B.vertices → E.endpointCount v.val = D.endpointCount v := by
  classical
  let f := bowtieTriangle right
  have hset : {v : V | v ∉ ({f 1, f 2} : Finset (Fin 5)).map B.label} =
      {v | v ≠ B.label (f 1) ∧ v ≠ B.label (f 2)} := by
    ext v
    simp
  obtain ⟨D', hs, he⟩ := D.induce_set_congr hset
  obtain ⟨E, hE, hc⟩ := B.restore_inactive_triangle right hrows D'
  refine ⟨E, hE.trans (congrArg (fun n => n + 1) hs), ?_⟩
  intro v hv
  have haway (i : Fin 5) : v.val ≠ B.label i := by
    intro h
    exact hv (h ▸ (B.mem_vertices (B.label i)).mpr (B.label_mem_component i))
  rw [hc ⟨v.val, haway (f 1), haway (f 2)⟩]
  exact he v

end Gallai.WholeBowtie
