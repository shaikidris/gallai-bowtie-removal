/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.InactiveBowtieCross
import Gallai.Operations.DecompositionInduce
import Gallai.Inputs.InactiveBowtieBudget

/-! # Original-graph ceiling budget for every inactive cross-pair -/

namespace Gallai.WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Selecting one inactive vertex from each triangle closes the ceiling budget
of the original graph, with two endpoints at the other exception. -/
theorem inactive_cross_endpoint (left right : Bool)
    (h1 : B.row (bowtieCrossLabels left right 1) = ∅)
    (h3 : B.row (bowtieCrossLabels left right 3) = ∅)
    (hc : G.Connected) (y : V) (hy : y ∉ B.vertices)
    (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  classical
  let f := bowtieCrossLabels left right
  let I : Finset (Fin 5) := {f 1, f 3}
  have hf0 : f 0 = 0 := (bowtieCrossLabels_local left right).1
  have h0 : 0 ∉ I := by
    simp only [I, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h
    · exact (by decide : (0 : Fin 5) ≠ 1) (f.injective (hf0.trans h))
    · exact (by decide : (0 : Fin 5) ≠ 3) (f.injective (hf0.trans h))
  have hI : I.card = 2 := by
    have h13 : f 1 ≠ f 3 := fun h => (by decide : (1 : Fin 5) ≠ 3) (f.injective h)
    simp [I, h13]
  have hi : ∀ i ∈ I, B.row i = ∅ := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact h1
    · have heq := Finset.mem_singleton.mp hi
      subst i
      exact h3
  have hset : {v : V | v ∉ I.map B.label} =
      {v | v ≠ B.label (f 1) ∧ v ≠ B.label (f 3)} := by
    ext v
    simp [I]
  have haway (i : Fin 5) : y ≠ B.label i := by
    intro h
    exact hy (by simp [h, WholeBowtie.vertices])
  obtain ⟨D, hs, he⟩ := B.privateDeletion_endpoint_budget I h0 hI hi hc y hy hyEven hcap
  obtain ⟨D', hs', he'⟩ := D.induce_set_congr hset
  obtain ⟨E, hE, hcounts⟩ := B.restore_inactive_cross left right h1 h3 D'
  refine ⟨E, by omega, ?_⟩
  rw [hcounts ⟨y, haway (f 1), haway (f 3)⟩ (haway (f 2)) (haway (f 4))]
  have hyI : y ∉ I.map B.label := by
    intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
    exact hy (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  rw [he' ⟨y, hyI⟩]
  exact he

end Gallai.WholeBowtie
