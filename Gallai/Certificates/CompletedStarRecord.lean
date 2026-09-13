/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarRoles

/-! # Indexed consequences of one accepted completed-star record

Replacement occurrences retain their role indices inside the complete
word list. Added occurrences occupy the remaining indices. No existence
or universe coverage is asserted by this adapter.
-/

namespace Gallai.Certificate.CompletedStar

variable {state : State} {profile : Fin 10}
variable {replacements added : List (List Star.Vertex)}

theorem AcceptedRecord.replacements_length
    (h : AcceptedRecord state profile replacements added) :
    replacements.length = (boundaries profile).length := by
  simpa only [roles, List.length_map] using h.2.1.length_eq.symm

/-- Replacement role i occupies occurrence i of the complete accepted family. -/
def AcceptedRecord.wordIndex (h : AcceptedRecord state profile replacements added)
    (i : Fin (boundaries profile).length) : Fin (replacements ++ added).length :=
  ⟨i.val, by rw [List.length_append, h.replacements_length]; omega⟩

/-- Added occurrence i follows every replacement occurrence. -/
def addedWordIndex (replacements added : List (List Star.Vertex))
    (i : Fin added.length) : Fin (replacements ++ added).length :=
  ⟨replacements.length + i.val, by simp only [List.length_append]; omega⟩

theorem AcceptedRecord.wordIndex_get (h : AcceptedRecord state profile replacements added)
    (i : Fin (boundaries profile).length) :
    (replacements ++ added)[h.wordIndex i] =
      replacements[i.val]'(by rw [h.replacements_length]; exact i.isLt) := by
  apply List.getElem_append_left

theorem addedWordIndex_get (replacements added : List (List Star.Vertex))
    (i : Fin added.length) :
    (replacements ++ added)[addedWordIndex replacements added i] = added[i] := by
  change (replacements ++ added)[replacements.length + i.val] = added[i.val]
  simp only [List.getElem_append_right (Nat.le_add_right _ _), Nat.add_sub_cancel_left]

/-- Each replacement has the exact ordered role assigned by the record. -/
theorem AcceptedRecord.wordIndex_compatible
    (h : AcceptedRecord state profile replacements added)
    (i : Fin (boundaries profile).length) :
    Compatible (boundaries profile)[i] Star.fresh.toFinset
      (replacements ++ added)[h.wordIndex i] := by
  have hi : i.val < (roles profile).length := by
    simpa only [roles, List.length_map] using i.isLt
  have hj : i.val < replacements.length := by rw [h.replacements_length]; exact i.isLt
  have hc := h.2.1.get hi hj
  rw [h.wordIndex_get]
  change Compatible (boundaries profile)[i.val] Star.fresh.toFinset replacements[i.val]
  simpa only [List.get_eq_getElem, roles, List.getElem_map] using hc

/-- Replacing role indices by word indices does not merge distinct roles. -/
theorem AcceptedRecord.wordIndex_injective
    (h : AcceptedRecord state profile replacements added) : Function.Injective h.wordIndex := by
  intro i j he
  have he' := congrArg (fun k : Fin (replacements ++ added).length => k.val) he
  exact Fin.ext he'

end Gallai.Certificate.CompletedStar
