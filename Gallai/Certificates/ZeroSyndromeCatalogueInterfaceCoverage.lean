/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeCatalogueInterfaces

/-! # Exhaustive catalogue coverage of the independently defined interfaces

These equalities compare literal catalogue indices against the full finite
function-space definitions, not against another list supplied by Python.
-/

namespace Gallai.Certificate.ZeroSyndrome.Catalogue

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All actual legal component/carrier pairs appear in the catalogue. -/
theorem two_image :
    (Finset.univ.image (fun i : Fin 51 => (twoComponents i, twoCarriers i))) = interfaces := by
  decide

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- All actual separated component partitions appear in the catalogue. -/
theorem one_image :
    (Finset.univ.image (fun i : Fin 7 => oneComponents i)) = separatedPartitions := by
  decide

/-- Index selection for an arbitrary actual two-credit interface. -/
theorem two_surjective (c k : Labels) (h : (c, k) ∈ interfaces) :
    ∃ i : Fin 51, twoComponents i = c ∧ twoCarriers i = k := by
  rw [← two_image] at h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact ⟨i, Prod.mk.inj hi⟩

/-- Index selection for an arbitrary actual one-credit interface. -/
theorem one_surjective (c : Labels) (h : c ∈ separatedPartitions) :
    ∃ i : Fin 7, oneComponents i = c := by
  rw [← one_image] at h
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
  exact ⟨i, hi⟩

end Gallai.Certificate.ZeroSyndrome.Catalogue
