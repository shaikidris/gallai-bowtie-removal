/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CrossTriangleGraph
import Gallai.Operations.DecompositionMap
import Gallai.Operations.Union

/-! # Restore two inactive vertices in different bowtie triangles

The two old hub edges are subdivided on their actual carriers, which need
not be distinct. One further two-edge path restores the original spokes.
-/

namespace Gallai.Decomposition

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Two degree-two private vertices in different triangles can be restored at
exactly one additional path. Endpoints outside their four private labels are
preserved, including the hub and every external vertex. -/
theorem restore_cross_triangle_deletion (f : Fin 5 ↪ V)
    (h02 : G.Adj (f 0) (f 2)) (h04 : G.Adj (f 0) (f 4))
    (h1 : ∀ v, G.Adj (f 1) v ↔ v = f 0 ∨ v = f 2)
    (h3 : ∀ v, G.Adj (f 3) v ↔ v = f 0 ∨ v = f 4)
    (D : Decomposition (G.induce {v | v ≠ f 1 ∧ v ≠ f 3})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v : {v : V // v ≠ f 1 ∧ v ≠ f 3}, v.val ≠ f 2 → v.val ≠ f 4 →
        E.endpointCount v.val = D.endpointCount v := by
  classical
  let S : Set V := {v | v ≠ f 1 ∧ v ≠ f 3}
  let H := crossTriangleBase G f
  let H1 := subdividedGraph H (f 1) (f 0) (f 2)
  let H2 := subdividedGraph H1 (f 3) (f 0) (f 4)
  let D0 : Decomposition H := D.map (Function.Embedding.subtype _)
  obtain ⟨hz1, he02, hz3, he04, hdis, hgraph⟩ := cross_triangle_graph f h02 h04 h1 h3
  obtain ⟨D1, hs1, hc1⟩ := D0.subdivide_edge (f 1) (f 0) (f 2) he02 hz1
  obtain ⟨D2, hs2, hc2⟩ := D1.subdivide_edge (f 3) (f 0) (f 4) he04 hz3
  have h20 : f 2 ≠ f 0 := by simp [f.injective.eq_iff]
  have h04' : f 0 ≠ f 4 := by simp [f.injective.eq_iff]
  have h24 : f 2 ≠ f 4 := by simp [f.injective.eq_iff]
  let L := twoEdgeDecomposition (f 0) (f 2) (f 4) h20 h04' h24
  obtain ⟨E, hs, hc⟩ := D2.union_disjoint_endpoints L hdis
  have hout : ∃ E : Decomposition (H2 ⊔ twoEdgeGraph (f 0) (f 2) (f 4)),
      E.size = D.size + 1 ∧
      ∀ v : S, v.val ≠ f 2 → v.val ≠ f 4 →
        E.endpointCount v.val = D.endpointCount v := by
    refine ⟨E, ?_, ?_⟩
    · have hLs : L.size = 1 := rfl
      have hD0s : D0.size = D.size := rfl
      omega
    · intro v hv2 hv4
      rw [hc, hc2, hc1]
      have hLz : L.endpointCount v.val = 0 := by
        rw [twoEdgeDecomposition_endpointCount]
        simp [Ne.symm hv2, Ne.symm hv4]
      rw [hLz, Nat.add_zero]
      exact D.map_endpointCount (Function.Embedding.subtype _) v
  rwa [hgraph] at hout

end Gallai.Decomposition
