/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie

/-! # Low-activity bowtie interfaces

An inactive private vertex has no external incidence and ordinary degree two.
At most two active private vertices forces either an inactive vertex in each
triangle or a completely inactive private pair. These are the two deletion
geometries consumed by the manuscript's low-activity restoration proof.
-/

namespace Gallai.WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Labels of private vertices having at least one external incidence. -/
def activePrivate : Finset (Fin 5) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ (B.row i).Nonempty)

/-- The manuscript's private activity counts vertices, not external edges. -/
def activity : ℕ := #B.activePrivate

/-- For a private vertex, inactivity is precisely absence from the active set. -/
theorem notMem_activePrivate_iff (i : Fin 5) (hi : i ≠ 0) :
    i ∉ B.activePrivate ↔ B.row i = ∅ := by
  simp [activePrivate, hi, Finset.not_nonempty_iff_eq_empty]

/-- A private incidence row is empty exactly when the ordinary degree is two. -/
theorem row_empty_iff_degree_two (i : Fin 5) (hi : i ≠ 0) :
    B.row i = ∅ ↔ G.degree (B.label i) = 2 := by
  have h := B.card_row_add_internal_degree i
  rw [bowtieGraph_degree, if_neg hi] at h
  rw [← Finset.card_eq_zero]
  omega

/-- Inactivity leaves exactly the fixed internal neighbours, with no hidden
restriction on the external anchors of any other bowtie vertex. -/
theorem neighbors_of_row_empty (i : Fin 5) (hi : B.row i = ∅) :
    G.neighborFinset (B.label i) = (bowtieGraph.neighborFinset i).map B.label := by
  have hsub : G.neighborFinset (B.label i) ⊆ B.vertices := by
    apply Finset.sdiff_eq_empty_iff_subset.mp
    exact hi
  have h := B.internal_neighbors i
  rwa [Finset.inter_eq_left.mpr hsub] at h

/-- The two labelled deletion geometries exhaust private activity at most two.
The disjunction does not assume a relabelling or connectedness after deletion. -/
theorem low_activity_cases (h : B.activity ≤ 2) :
    ((B.row 1 = ∅ ∨ B.row 2 = ∅) ∧ (B.row 3 = ∅ ∨ B.row 4 = ∅)) ∨
      (B.row 1 = ∅ ∧ B.row 2 = ∅) ∨ (B.row 3 = ∅ ∧ B.row 4 = ∅) := by
  have finite_cases : ∀ S : Finset (Fin 5), #S ≤ 2 →
      ((1 ∉ S ∨ 2 ∉ S) ∧ (3 ∉ S ∨ 4 ∉ S)) ∨
        (1 ∉ S ∧ 2 ∉ S) ∨ (3 ∉ S ∧ 4 ∉ S) := by decide
  have hc := finite_cases B.activePrivate h
  simpa only [B.notMem_activePrivate_iff 1 (by decide),
    B.notMem_activePrivate_iff 2 (by decide),
    B.notMem_activePrivate_iff 3 (by decide),
    B.notMem_activePrivate_iff 4 (by decide)] using hc

/-- Low private activity supplies an actual pair of inactive labels. -/
theorem exists_inactive_pair (h : B.activity ≤ 2) :
    ∃ I : Finset (Fin 5), #I = 2 ∧ 0 ∉ I ∧ ∀ i ∈ I, B.row i = ∅ := by
  have hsub : B.activePrivate ⊆ Finset.univ.erase 0 := by
    intro i hi
    have hi0 := (Finset.mem_filter.mp hi).2.1
    exact Finset.mem_erase.mpr ⟨hi0, Finset.mem_univ _⟩
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hp : #(Finset.univ.erase (0 : Fin 5)) = 4 := by decide
  change #B.activePrivate ≤ 2 at h
  rw [hp] at hc
  obtain ⟨I, hIS, hI⟩ := Finset.exists_subset_card_eq
    (show 2 ≤ #(Finset.univ.erase 0 \ B.activePrivate) by omega)
  refine ⟨I, hI, ?_, ?_⟩
  · intro h0
    exact Finset.notMem_erase 0 Finset.univ (Finset.mem_sdiff.mp (hIS h0)).1
  · intro i hi
    obtain ⟨hpI, haI⟩ := Finset.mem_sdiff.mp (hIS hi)
    exact (B.notMem_activePrivate_iff i (Finset.mem_erase.mp hpI).1).mp haI

end Gallai.WholeBowtie
