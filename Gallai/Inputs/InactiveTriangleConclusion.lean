/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.InactiveBowtieTriangle
import Gallai.Operations.DecompositionInduce
import Gallai.Inputs.InactiveBowtieBudget

/-! # Ceiling-budget conclusion for an inactive bowtie triangle -/

namespace Gallai.WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An entirely inactive private pair in either triangle closes the original
graph's ceiling budget, preserving two endpoints at the other exception. -/
theorem inactive_triangle_endpoint (right : Bool)
    (hrows : ∀ i : Fin 3, i ≠ 0 → B.row (bowtieTriangle right i) = ∅)
    (hc : G.Connected) (y : V) (hy : y ∉ B.vertices)
    (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y := by
  classical
  let f := bowtieTriangle right
  let I : Finset (Fin 5) := {f 1, f 2}
  have hf0 : f 0 = 0 := by cases right <;> rfl
  have h0 : 0 ∉ I := by
    simp only [I, Finset.mem_insert, Finset.mem_singleton, not_or]
    constructor <;> intro h
    · exact (by decide : (0 : Fin 3) ≠ 1) (f.injective (hf0.trans h))
    · exact (by decide : (0 : Fin 3) ≠ 2) (f.injective (hf0.trans h))
  have hI : I.card = 2 := by
    have h12 : f 1 ≠ f 2 := fun h => (by decide : (1 : Fin 3) ≠ 2) (f.injective h)
    simp [I, h12]
  have hi : ∀ i ∈ I, B.row i = ∅ := by
    intro i hi
    rcases Finset.mem_insert.mp hi with rfl | hi
    · exact hrows 1 (by decide)
    · have heq := Finset.mem_singleton.mp hi
      subst i
      exact hrows 2 (by decide)
  have hset : {v : V | v ∉ I.map B.label} =
      {v | v ≠ B.label (f 1) ∧ v ≠ B.label (f 2)} := by
    ext v
    simp [I]
  have hsurv : y ≠ B.label (f 1) ∧ y ≠ B.label (f 2) := by
    constructor <;> intro h <;> apply hy <;>
      simp [h, WholeBowtie.vertices]
  have lift := B.restore_inactive_triangle right hrows
  obtain ⟨D, hs, he⟩ := B.privateDeletion_endpoint_budget I h0 hI hi hc y hy hyEven hcap
  obtain ⟨D', hs', he'⟩ := D.induce_set_congr hset
  obtain ⟨E, hE, hcounts⟩ := lift D'
  refine ⟨E, by omega, ?_⟩
  rw [hcounts ⟨y, hsurv⟩]
  have hyI : y ∉ I.map B.label := by
    intro h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp h
    exact hy (Finset.mem_map.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  rw [he' ⟨y, hyI⟩]
  exact he

end Gallai.WholeBowtie
