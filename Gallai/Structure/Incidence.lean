/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Syndrome
import Mathlib.Data.Fintype.Fin

/-!
# Column incidence and parity after deleting a whole bowtie

The puncture is the induced graph on the complement of all five vertices.
It need not be connected. Exact degree accounting links its parity to the
actual syndrome rather than to an independently chosen repair mask.
-/

namespace Gallai.WholeBowtie

open scoped Finset symmDiff

universe u

variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Number of the five external rows containing an original vertex. -/
def columnCount (v : V) : ℕ := #{i : Fin 5 | v ∈ B.row i}

/-- Syndrome membership is precisely odd column incidence in the five actual rows. -/
theorem mem_syndrome_iff_odd_column (v : V) :
    v ∈ B.syndrome ↔ Odd (B.columnCount v) := by
  simp only [columnCount, Fin.card_filter_univ_succ']
  by_cases h0 : v ∈ B.row 0 <;> by_cases h1 : v ∈ B.row 1 <;>
    by_cases h2 : v ∈ B.row 2 <;> by_cases h3 : v ∈ B.row 3 <;>
    by_cases h4 : v ∈ B.row 4 <;>
    simp [syndrome, Finset.mem_symmDiff, Nat.odd_iff, h0, h1, h2, h3, h4, -mem_row]

/-- Outside the bowtie, column labels biject onto the neighbours that will be deleted. -/
theorem deleted_neighbors_eq_column (v : V) (hv : v ∉ B.vertices) :
    G.neighborFinset v ∩ B.vertices =
      (Finset.univ.filter fun i : Fin 5 => v ∈ B.row i).map B.label := by
  ext w
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp h
    obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hb
    refine Finset.mem_map.mpr ⟨i, ?_, rfl⟩
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, (B.mem_row i v).mpr
      ⟨((G.mem_neighborFinset _ _).mp ha).symm, hv⟩⟩
  · intro h
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp h
    have ha := ((B.mem_row i v).mp (Finset.mem_filter.mp hi).2).1
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ha.symm,
      Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩⟩

/-- The column count equals the actual number of deleted incident edges. -/
theorem columnCount_eq_deleted_degree (v : V) (hv : v ∉ B.vertices) :
    B.columnCount v = #(G.neighborFinset v ∩ B.vertices) := by
  rw [B.deleted_neighbors_eq_column v hv, Finset.card_map]
  rfl

/-- The whole-deletion puncture on the subtype of retained original vertices. -/
abbrev puncture : SimpleGraph {v : V // v ∉ B.vertices} :=
  G.induce {v | v ∉ B.vertices}

/-- Exact degree splitting at every retained vertex, without a connectivity premise. -/
theorem puncture_degree_add_column (v : {v : V // v ∉ B.vertices}) :
    B.puncture.degree v + B.columnCount v = G.degree v := by
  have hmap := congrArg Finset.card
    (G.map_neighborFinset_induce (s := {v | v ∉ B.vertices}) v)
  have hset : G.neighborFinset v ∩ ({v | v ∉ B.vertices} : Set V).toFinset =
      G.neighborFinset v \ B.vertices := by
    ext w
    simp
  rw [hset] at hmap
  have hdegree : B.puncture.degree v = #(G.neighborFinset v \ B.vertices) := by
    simpa using hmap
  rw [hdegree, B.columnCount_eq_deleted_degree v v.property]
  simp

/-- Deletion preserves degree parity precisely when the retained vertex is outside the syndrome. -/
theorem puncture_parity_eq_iff (v : {v : V // v ∉ B.vertices}) :
    B.puncture.degree v % 2 = G.degree v % 2 ↔ (v : V) ∉ B.syndrome := by
  have h := B.puncture_degree_add_column v
  rw [B.mem_syndrome_iff_odd_column, Nat.odd_iff]
  omega

/-- Since anchors were odd, they become even in the puncture exactly at the syndrome vertices. -/
theorem anchor_even_puncture_iff (v : {v : V // v ∉ B.vertices})
    (hv : (v : V) ∈ B.anchors) :
    Even (B.puncture.degree v) ↔ (v : V) ∈ B.syndrome := by
  have ho := Nat.odd_iff.mp (B.odd_degree_anchor hv)
  have h := B.puncture_degree_add_column v
  rw [Nat.even_iff, B.mem_syndrome_iff_odd_column, Nat.odd_iff]
  omega

end Gallai.WholeBowtie
