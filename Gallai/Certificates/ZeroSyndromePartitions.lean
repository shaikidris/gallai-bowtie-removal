/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Data.Finset.Max
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod

/-! # Complete four-anchor component and carrier partitions

A block is labelled by its least anchor index, not by an arbitrary component
number. Normalization preserves exactly equality of original labels. Carrier
blocks have size at most two and refine the component partition.
-/

namespace Gallai.Certificate.ZeroSyndrome

open scoped Finset

/-- Four boundary positions labeled by their component or carrier blocks. -/
abbrev Labels := Fin 4 → Fin 4

/-- Least-member labels canonically represent partitions of the four anchors. -/
def Normalized (c : Labels) : Prop := ∀ i, c i ≤ i ∧ c (c i) = c i

instance (c : Labels) : Decidable (Normalized c) := by
  unfold Normalized
  infer_instance

/-- Canonicalize actual component or carrier identifiers without assuming
their codomain is finite or ordered. -/
noncomputable def normalize {α : Type*} (f : Fin 4 → α) (i : Fin 4) : Fin 4 := by
  classical
  exact (Finset.univ.filter (fun j => f j = f i)).min' ⟨i, by simp⟩

/-- The least representative has the same original label. -/
theorem normalize_spec {α : Type*} (f : Fin 4 → α) (i : Fin 4) :
    f (normalize f i) = f i := by
  classical
  exact (Finset.mem_filter.mp (Finset.min'_mem
    (Finset.univ.filter (fun j : Fin 4 => f j = f i)) ⟨i, by simp⟩)).2

/-- Normalization neither merges nor separates original blocks. -/
theorem normalize_eq_iff {α : Type*} (f : Fin 4 → α) (i j : Fin 4) :
    normalize f i = normalize f j ↔ f i = f j := by
  classical
  constructor
  · intro h
    exact (normalize_spec f i).symm.trans ((congrArg f h).trans (normalize_spec f j))
  · intro h
    simp only [normalize, h]

/-- Every actual assignment yields a canonical finite partition. -/
theorem normalize_normalized {α : Type*} (f : Fin 4 → α) : Normalized (normalize f) := by
  classical
  intro i
  constructor
  · exact Finset.min'_le _ _ (by simp)
  · exact (normalize_eq_iff f _ _).mpr (normalize_spec f i)

/-- Literal legal carrier refinement for a two-credit record. -/
def Compatible (components carriers : Labels) : Prop :=
  (∀ i, #{j | carriers j = i} ≤ 2) ∧
    ∀ i j, carriers i = carriers j → components i = components j

instance (c k : Labels) : Decidable (Compatible c k) := by
  unfold Compatible
  infer_instance

/-- All canonical component partitions, enumerated without a supplied list. -/
def partitions : Finset Labels := Finset.univ.filter Normalized

/-- The entire two-credit interface universe, with no graph-order parameter. -/
def interfaces : Finset (Labels × Labels) :=
  partitions.biUnion fun c => (partitions.filter (Compatible c)).image (fun k => (c, k))

/-- The one-credit universe consists of component partitions with at least
three blocks; one nonempty tail per block is checked in the record itself. -/
def separatedPartitions : Finset Labels :=
  partitions.filter (fun c => 3 ≤ #(Finset.univ.image c))

/-- Finite interface membership is exactly normalization and carrier legality. -/
theorem mem_interfaces (c k : Labels) :
    (c, k) ∈ interfaces ↔ Normalized c ∧ Normalized k ∧ Compatible c k := by
  simp [interfaces, partitions]

end Gallai.Certificate.ZeroSyndrome
