/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Family
import Gallai.Certificates.LocalCoverage

/-!
# Local edge ownership at actual ambient carrier indices

The carrier numbering is a bijection, and its embedding into the full family
is injective. Unaffected old carriers contribute no local word. This transports
the finite unique-cover certificates without identifying equal word occurrences.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]
variable [Fintype V] [DecidableRel H.Adj]

/-- Terminal numbering is an equivalence, including the empty profile. -/
noncomputable def terminalNumberEquiv (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : D.TerminalIndex x ≃ Fin (profileOf D x).terminals :=
  (D.terminalIndexEquivFin x).trans (finCongr (profileOf_counts D x hd).1)

/-- Through numbering is an equivalence, including the empty profile. -/
noncomputable def throughNumberEquiv (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : D.ThroughIndex x ≃ Fin (profileOf D x).throughs :=
  (D.throughIndexEquivFin x).trans (finCongr (profileOf_counts D x hd).2)

/-- Actual old hub carriers together with the two added occurrences. -/
abbrev UsedCarrier (D : Decomposition H) (x : V) :=
  (D.TerminalIndex x ⊕ D.ThroughIndex x) ⊕ Fin 2

/-- The finite interface numbers every actual used occurrence exactly once. -/
noncomputable def usedNumber (D : Decomposition H) (x : V) (hd : H.degree x = 4) :
    UsedCarrier D x ≃ (profileOf D x).LocalIndex :=
  Equiv.sumCongr
    (Equiv.sumCongr (terminalNumberEquiv D x hd) (throughNumberEquiv D x hd))
    (Equiv.refl _)

/-- Embed a used occurrence at its original or added family index. -/
def usedCarrier (D : Decomposition H) (x : V) :
    UsedCarrier D x → Fin D.size ⊕ Fin 2
  | .inl (.inl i) => .inl i.val
  | .inl (.inr i) => .inl i.val
  | .inr i => .inr i

omit [Fintype V] [DecidableRel H.Adj] in
/-- Terminal and through carriers are disjoint, so no occurrences collide. -/
theorem usedCarrier_injective (D : Decomposition H) (x : V) :
    Function.Injective (usedCarrier D x) := by
  intro i j hij
  rcases i with (i | i) | i <;> rcases j with (j | j) | j
  all_goals simp only [usedCarrier] at hij
  · exact congrArg (fun k => Sum.inl (Sum.inl k))
      (Subtype.ext (Sum.inl.inj hij))
  · have hv := Sum.inl.inj hij
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through x))
      (hv ▸ i.property) j.property)
  · cases hij
  · have hv := Sum.inl.inj hij
    exact False.elim ((Finset.disjoint_left.mp (D.disjoint_terminal_through x))
      j.property (hv ▸ i.property))
  · exact congrArg (fun k => Sum.inl (Sum.inr k))
      (Subtype.ext (Sum.inl.inj hij))
  · cases hij
  · cases hij
  · cases hij
  · exact congrArg Sum.inr (Sum.inr.inj hij)

/-- Local contribution of each index of the full candidate family. -/
noncomputable def candidateWord (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) : Fin D.size ⊕ Fin 2 → List Vertex
  | .inl i => assignedWord D x hd i
  | .inr i => (profileOf D x).localWord (.inr i)

/-- The numerical occurrence and actual carrier carry the very same checked word. -/
theorem candidateWord_used (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : UsedCarrier D x) :
    candidateWord D x hd (usedCarrier D x i) =
      (profileOf D x).localWord (usedNumber D x hd i) := by
  rcases i with (i | i) | i
  · simp only [candidateWord, usedCarrier, assignedWord, dif_pos i.property]
    rfl
  · have ht : i.val ∉ D.terminalCarriers x := fun ht =>
      (Finset.disjoint_left.mp (D.disjoint_terminal_through x)) ht i.property
    simp only [candidateWord, usedCarrier, assignedWord, dif_neg ht, dif_pos i.property]
    rfl
  · rfl

/-- A local edge can only belong to a used occurrence, never an unaffected carrier. -/
theorem candidateWord_owner (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (j : Fin D.size ⊕ Fin 2) (e : Sym2 Vertex)
    (he : e ∈ wordEdges (candidateWord D x hd j)) :
    ∃ i : UsedCarrier D x, usedCarrier D x i = j := by
  rcases j with j | j
  · by_cases ht : j ∈ D.terminalCarriers x
    · exact ⟨.inl (.inl ⟨j, ht⟩), rfl⟩
    by_cases hp : j ∈ D.throughCarriers x
    · exact ⟨.inl (.inr ⟨j, hp⟩), rfl⟩
    · change e ∈ wordEdges (assignedWord D x hd j) at he
      rw [assignedWord_of_unaffected D x hd j ht hp] at he
      simp [wordEdges] at he
  · exact ⟨.inr j, rfl⟩

/-- Each active edge is assigned to exactly one actual old or added carrier index. -/
theorem candidateWord_unique (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (e : Sym2 Vertex) (he : e ∈ activeEdges) :
    ∃! j : Fin D.size ⊕ Fin 2, e ∈ wordEdges (candidateWord D x hd j) := by
  obtain ⟨i, hi, hu⟩ := (profileOf D x).localEdge_unique e he
  let k := (usedNumber D x hd).symm i
  refine ⟨usedCarrier D x k, ?_, ?_⟩
  · change e ∈ wordEdges (candidateWord D x hd (usedCarrier D x k))
    rw [candidateWord_used]
    simpa only [k, Equiv.apply_symm_apply] using hi
  · intro j hj
    obtain ⟨l, rfl⟩ := candidateWord_owner D x hd j e hj
    rw [candidateWord_used] at hj
    have hl : l = k := (usedNumber D x hd).injective
      ((hu _ hj).trans (Equiv.apply_symm_apply _ i).symm)
    exact congrArg (usedCarrier D x) hl

/-- No candidate local contribution contains an edge outside the active graph. -/
theorem candidateWord_active (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (j : Fin D.size ⊕ Fin 2) (e : Sym2 Vertex)
    (he : e ∈ wordEdges (candidateWord D x hd j)) : e ∈ activeEdges := by
  obtain ⟨i, rfl⟩ := candidateWord_owner D x hd j e he
  rw [candidateWord_used] at he
  exact (profileOf D x).localEdge_active _ e he

end Gallai.Star
