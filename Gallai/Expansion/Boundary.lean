/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Graph
import Mathlib.Tactic.FinCases

/-!
# The exact boundary between retained and active edges

The 26 local edges consist of all new edges and the four old spokes. Every
other old edge is retained separately. This partition is independent of
any path decomposition or carrier choice.
-/

namespace Gallai.Star

universe u

variable {V : Type u} (H : SimpleGraph V) (x : V) (A : Fin 4 ≃ H.neighborSet x)

/-- The four anchor labels exhaust the old neighbourhood. -/
theorem adj_iff_anchors (v : V) :
    H.Adj x v ↔ v = (A 0).val ∨ v = (A 1).val ∨ v = (A 2).val ∨ v = (A 3).val := by
  constructor
  · intro hv
    obtain ⟨i, hi⟩ := A.surjective ⟨v, hv⟩
    have he := (congrArg Subtype.val hi).symm
    fin_cases i <;> simp_all
  · rintro (rfl | rfl | rfl | rfl) <;> exact (A _).property

/-- The only old-old edges in the active list are hub spokes. -/
theorem active_old_old (v w : V) :
    s(Sum.inl v, Sum.inl w) ∈ activeEdges.map (Sym2.map (label H x A)) ↔
      (v = x ∧ H.Adj x w) ∨ (w = x ∧ H.Adj x v) := by
  simp [activeEdges, fresh, anchors, label, adj_iff_anchors H x A]
  tauto

/-- All mixed edges of the expansion belong to the active list. -/
theorem active_old_private (v : V) (i : Fin 4) :
    s(Sum.inl v, Sum.inr i) ∈ activeEdges.map (Sym2.map (label H x A)) ↔
      v = x ∨ H.Adj x v := by
  fin_cases i <;>
    simp [activeEdges, fresh, anchors, label, adj_iff_anchors H x A]

/-- The active list has exactly the two private-private edges. -/
theorem active_private_private (i j : Fin 4) :
    s(Sum.inr i, Sum.inr j) ∈ activeEdges.map (Sym2.map (label H x A)) ↔
      privateAdj i j := by
  fin_cases i <;> fin_cases j <;>
    simp [activeEdges, fresh, anchors, label, privateAdj]

/-- Every expanded edge is either a retained old nonspoke or an active edge. -/
theorem expansion_edge_partition (e : Sym2 (V ⊕ Fin 4)) :
    e ∈ (expansion H x).edgeSet ↔
      (∃ f ∈ H.edgeSet, x ∉ f ∧ Sym2.map (oldHom H x) f = e) ∨
        e ∈ activeEdges.map (Sym2.map (label H x A)) := by
  constructor
  · induction e using Sym2.ind with | _ v w =>
      intro he
      cases v with
      | inl v =>
        cases w with
        | inl w =>
          have hvw : H.Adj v w := he
          by_cases hv : v = x
          · exact Or.inr ((active_old_old H x A v w).mpr (Or.inl ⟨hv, hv ▸ hvw⟩))
          by_cases hw : w = x
          · exact Or.inr ((active_old_old H x A v w).mpr
              (Or.inr ⟨hw, hw ▸ hvw.symm⟩))
          · exact Or.inl ⟨s(v, w), hvw,
              by
                simp only [Sym2.mem_iff, not_or]
                exact ⟨fun h => hv h.symm, fun h => hw h.symm⟩, rfl⟩
        | inr i => exact Or.inr ((active_old_private H x A v i).mpr he)
      | inr i =>
        cases w with
        | inl w =>
          rw [Sym2.eq_swap]
          exact Or.inr ((active_old_private H x A w i).mpr he)
        | inr j => exact Or.inr ((active_private_private H x A i j).mpr he)
  · rintro (⟨f, hf, _, rfl⟩ | he)
    · induction f using Sym2.ind with | _ v w => exact hf
    · obtain ⟨a, ha, rfl⟩ := List.mem_map.mp he
      exact active_edge_mem H x A a ha

/-- No retained old nonspoke is counted again in the active list. -/
theorem retained_not_active (f : Sym2 V) (hx : x ∉ f) :
    Sym2.map (oldHom H x) f ∉ activeEdges.map (Sym2.map (label H x A)) := by
  induction f using Sym2.ind with | _ v w =>
    change s(Sum.inl v, Sum.inl w) ∉ _
    rw [active_old_old H x A]
    simp only [Sym2.mem_iff, not_or] at hx
    intro he
    exact he.elim (fun h => hx.1 h.1.symm) (fun h => hx.2 h.1.symm)

end Gallai.Star
