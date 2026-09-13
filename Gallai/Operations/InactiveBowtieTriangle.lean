/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.PendantTriangleDeletion
import Gallai.Structure.LowActivity

/-! # Labelled inactive-triangle restoration in a whole bowtie -/

namespace Gallai

/-- Select either bowtie triangle, with the common hub first. -/
def bowtieTriangle (right : Bool) : Fin 3 ↪ Fin 5 where
  toFun i := if i = 0 then 0 else if right then (if i = 1 then 3 else 4)
    else (if i = 1 then 1 else 2)
  inj' := by cases right <;> decide

/-- Both selections give a triangle and contain every neighbour of their private labels. -/
theorem bowtieTriangle_local (right : Bool) :
    (∀ i j, i ≠ j → bowtieGraph.Adj (bowtieTriangle right i) (bowtieTriangle right j)) ∧
    (∀ i, i ≠ 0 → ∀ j, bowtieGraph.Adj (bowtieTriangle right i) j →
      ∃ k, bowtieTriangle right k = j) ∧
    (∃ j, j ≠ bowtieTriangle right 1 ∧ j ≠ bowtieTriangle right 2 ∧
      bowtieGraph.Adj (bowtieTriangle right 0) j) := by
  constructor
  · intro i j hij
    cases right <;> fin_cases i <;> fin_cases j <;>
      simp_all [bowtieTriangle, bowtieGraph, SimpleGraph.fromEdgeSet_adj]
  constructor
  · intro i hi j hj
    cases right <;> fin_cases i <;> fin_cases j <;>
      simp_all [bowtieTriangle, bowtieGraph, SimpleGraph.fromEdgeSet_adj]
    all_goals first | exact ⟨0, by decide⟩ | exact ⟨1, by decide⟩ | exact ⟨2, by decide⟩
  · cases right
    · exact ⟨3, by decide, by decide, by decide⟩
    · exact ⟨1, by decide, by decide, by decide⟩

namespace WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Restore either inactive private pair from the actual induced deletion,
with one additional path and no endpoint loss at any retained vertex. -/
theorem restore_inactive_triangle (right : Bool)
    (hrows : ∀ i : Fin 3, i ≠ 0 → B.row (bowtieTriangle right i) = ∅)
    (D : Decomposition (G.induce {v | v ≠ B.label (bowtieTriangle right 1) ∧
      v ≠ B.label (bowtieTriangle right 2)})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v : {v : V // v ≠ B.label (bowtieTriangle right 1) ∧
        v ≠ B.label (bowtieTriangle right 2)},
        E.endpointCount v.val = D.endpointCount v := by
  classical
  let f := (bowtieTriangle right).trans B.label
  obtain ⟨ht, hp, j, hj1, hj2, hj⟩ := bowtieTriangle_local right
  apply Decomposition.restore_pendant_triangle_deletion f ?_ ?_ ?_ D
  · intro i k hik
    exact (B.adj_iff _ _).mpr (ht i k hik)
  · intro i hi v hv
    have hn : v ∈ G.neighborFinset (B.label (bowtieTriangle right i)) :=
      (G.mem_neighborFinset _ _).mpr hv
    rw [B.neighbors_of_row_empty _ (hrows i hi)] at hn
    obtain ⟨k, hk, hkv⟩ := Finset.mem_map.mp hn
    obtain ⟨l, hl⟩ := hp i hi k ((bowtieGraph.mem_neighborFinset _ _).mp hk)
    refine ⟨l, ?_⟩
    change B.label (bowtieTriangle right l) = v
    simpa only [hl] using hkv
  · refine ⟨B.label j, ⟨?_, ?_⟩, (B.adj_iff _ _).mpr hj⟩
    · exact fun h => hj1 (B.label.injective h)
    · exact fun h => hj2 (B.label.injective h)

end WholeBowtie
end Gallai
