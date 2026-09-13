/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoAuxiliaryPassingProfile
import Gallai.Structure.SyndromeStarParity
import Gallai.Foundations.EndpointBounds

/-! # Additional endpoint carriers forced by the all-coincident through profile

The hub carrier has endpoints r,s. Odd p,q therefore have endpoint carriers
elsewhere. Those two carriers are allowed to coincide with one another.
-/
namespace Gallai.WholeBowtie

open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual through carrier cannot also supply the additional p,q endpoints.
No disjointness or distinctness between their two selected carriers is assumed. -/
theorem sizeTwo_forced_endpoint_carriers (A : B.AnchorNumbering)
    (D : Decomposition B.syndromeStar) (k : Fin D.size)
    (hr : (D.path k).start = B.sizeTwoRemoteMarks A 0 ∨
      (D.path k).finish = B.sizeTwoRemoteMarks A 0)
    (hs : (D.path k).start = B.sizeTwoRemoteMarks A 1 ∨
      (D.path k).finish = B.sizeTwoRemoteMarks A 1) :
    ∃ f : Fin 2 → Fin D.size, ∀ j : Fin 2,
      f j ≠ k ∧
      ((D.path (f j)).start.val = (A ⟨j.val,by omega⟩).val ∨
       (D.path (f j)).finish.val = (A ⟨j.val,by omega⟩).val) := by
  classical
  have hneq (i j : Fin 4) (h : i ≠ j) : (A i).val ≠ (A j).val := by
    intro he
    exact h (A.injective (Subtype.ext he))
  have hrs : B.sizeTwoRemoteMarks A 0 ≠ B.sizeTwoRemoteMarks A 1 := by
    intro he
    have hv := congrArg Subtype.val he
    exact hneq 2 3 (by decide) hv
  have hends :
      ((D.path k).start = B.sizeTwoRemoteMarks A 0 ∧
       (D.path k).finish = B.sizeTwoRemoteMarks A 1) ∨
      ((D.path k).start = B.sizeTwoRemoteMarks A 1 ∧
       (D.path k).finish = B.sizeTwoRemoteMarks A 0) := by
    rcases hr with hr | hr <;> rcases hs with hs | hs
    · exact (hrs (hr.symm.trans hs)).elim
    · exact Or.inl ⟨hr,hs⟩
    · exact Or.inr ⟨hs,hr⟩
    · exact (hrs (hr.symm.trans hs)).elim
  have select (j : Fin 2) : ∃ t : Fin D.size, t ≠ k ∧
      ((D.path t).start.val = (A ⟨j.val,by omega⟩).val ∨
       (D.path t).finish.val = (A ⟨j.val,by omega⟩).val) := by
    let a : Fin 4 := ⟨j.val,by omega⟩
    let w : B.StarSurvivor := ⟨(A a).val,B.anchor_survives (A a).property⟩
    have ho : Odd (B.syndromeStar.degree w) := by
      apply Nat.not_even_iff_odd.mp
      intro he
      exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (A a).property)
        ((B.syndromeStar_even_iff w).mp he)
    have hp := D.endpointCount_pos_of_odd_degree w ho
    have hc : 0 < #(D.terminalCarriers w) := by rwa [D.card_terminalCarriers]
    obtain ⟨t,ht⟩ := Finset.card_pos.mp hc
    have ht' := (Finset.mem_filter.mp ht).2
    have hend : (D.path t).start.val = (A a).val ∨
        (D.path t).finish.val = (A a).val := by
      rcases ht' with hh | hh
      · exact Or.inl (congrArg Subtype.val hh)
      · exact Or.inr (congrArg Subtype.val hh)
    refine ⟨t,?_,hend⟩
    intro htk
    subst t
    have ha2 : (A a).val ≠ (A 2).val := hneq a 2 (by
      intro he; have hv := congrArg Fin.val he; dsimp [a] at hv; omega)
    have ha3 : (A a).val ≠ (A 3).val := hneq a 3 (by
      intro he; have hv := congrArg Fin.val he; dsimp [a] at hv; omega)
    rcases hends with ⟨hstart,hfinish⟩ | ⟨hstart,hfinish⟩
    · rcases hend with hh | hh
      · exact ha2 (hh.symm.trans (congrArg Subtype.val hstart))
      · exact ha3 (hh.symm.trans (congrArg Subtype.val hfinish))
    · rcases hend with hh | hh
      · exact ha3 (hh.symm.trans (congrArg Subtype.val hstart))
      · exact ha2 (hh.symm.trans (congrArg Subtype.val hfinish))
  exact ⟨fun j => Classical.choose (select j),fun j => Classical.choose_spec (select j)⟩

end Gallai.WholeBowtie
