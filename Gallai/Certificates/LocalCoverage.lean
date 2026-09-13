/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.Profiles
import Mathlib.Data.Fintype.Sum

/-!
# Occurrence-indexed local edge ownership

An index distinguishes terminal, through, and added occurrences, even if two
words were equal. The finite checks establish unique edge ownership for these
occurrences, not merely equality of the sets of words.
-/

namespace Gallai.Star

/-- Occurrences of all replacement connectors and the two added paths. -/
abbrev Profile.LocalIndex (p : Profile) :=
  (Fin p.terminals ⊕ Fin p.throughs) ⊕ Fin 2

/-- The checked word at a particular local occurrence. -/
def Profile.localWord (p : Profile) : p.LocalIndex → List Vertex
  | .inl (.inl i) => p.terminalWord i
  | .inl (.inr i) => p.throughWord i
  | .inr i => p.added[i.val]'(by rw [p.valid.2.1]; exact i.isLt)

/-- Every indexed occurrence belongs to the checked certificate. -/
theorem Profile.localWord_mem (p : Profile) (i : p.LocalIndex) :
    p.localWord i ∈ p.replacements ++ p.added := by
  rcases i with (i | i) | i
  · exact p.terminalWord_mem i
  · exact p.throughWord_mem i
  · exact List.mem_append_right _ (List.getElem_mem _)

/-- Every local edge has exactly one occurrence-indexed owner in every profile. -/
theorem Profile.localEdge_unique (p : Profile) :
    ∀ e ∈ activeEdges, ∃! i : p.LocalIndex, e ∈ wordEdges (p.localWord i) := by
  unfold ExistsUnique
  cases p <;> decide

/-- Indexed words introduce no edge outside the active local graph. -/
theorem Profile.localEdge_active (p : Profile) (i : p.LocalIndex)
    (e : Sym2 Vertex) (he : e ∈ wordEdges (p.localWord i)) : e ∈ activeEdges := by
  apply p.valid.2.2.2.2.2.1.mem_iff.mp
  exact List.mem_flatMap.mpr ⟨p.localWord i, p.localWord_mem i, he⟩

end Gallai.Star
