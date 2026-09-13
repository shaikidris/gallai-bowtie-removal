/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.Transport

/-! # Locate a used unordered edge as an oriented run -/

namespace Gallai

universe u
variable {V : Type u} {G : SimpleGraph V} {a b : V}

/-- A used edge has an actual oriented one-edge run. Both outer pieces may
be empty; the unordered equality records the orientation instead of assuming it. -/
theorem exists_edge_run (P : G.Walk a b) (e : Sym2 V) (he : e ∈ P.edges) :
    ∃ (x y : V) (L : G.Walk a x) (R : G.Walk y b) (hxy : G.Adj x y),
      e = s(x, y) ∧ P = L.append (.cons hxy R) := by
  induction P with
  | nil => simp at he
  | @cons a c b hac P ih =>
    rcases List.mem_cons.mp he with he | he
    · exact ⟨a, c, .nil, P, hac, he, rfl⟩
    · obtain ⟨x, y, L, R, hxy, he, hP⟩ := ih he
      refine ⟨x, y, .cons hac L, R, hxy, he, ?_⟩
      simp only [SimpleGraph.Walk.cons_append, hP]

end Gallai
