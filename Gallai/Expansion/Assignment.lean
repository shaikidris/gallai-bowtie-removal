/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Restore
import Gallai.Certificates.Profiles

/-!
# Assign checked words to the actual hub carriers

The input decomposition selects its own profile and anchor ordering. Every
actual terminal or through carrier then has a prescribed replacement; no
compatible-family or favourable-labelling premise is supplied by the caller.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]

omit [DecidableEq V] in
/-- The numerical anchor order agrees with the nine-symbol interpretation. -/
theorem label_anchor (x : V) (A : Fin 4 ≃ H.neighborSet x) (i : Fin 4) :
    label H x A (anchor i) = Sum.inl (A i).val := by
  fin_cases i <;> rfl

/-- Select the interface from the input endpoint count. -/
def profileOf (D : Decomposition H) (x : V) : Profile :=
  if D.endpointCount x = 0 then .zero else if D.endpointCount x = 2 then .two else .four

variable [Fintype V] [DecidableRel H.Adj]

/-- At degree four, the selected profile has exactly the actual two carrier counts. -/
theorem profileOf_counts (D : Decomposition H) (x : V) (hd : H.degree x = 4) :
    D.endpointCount x = (profileOf D x).terminals ∧
      D.throughCount x = (profileOf D x).throughs := by
  rcases D.degree_four_carrier_profiles x hd with h | h | h
  all_goals simp [profileOf, h.1, h.2, Profile.terminals, Profile.throughs]

/-- Position of an actual terminal carrier in its checked profile. -/
noncomputable def terminalNumber (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.TerminalIndex x) : Fin (profileOf D x).terminals :=
  Fin.cast (profileOf_counts D x hd).1 (D.terminalIndexEquivFin x i)

/-- Position of an actual through carrier in its checked profile. -/
noncomputable def throughNumber (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.ThroughIndex x) : Fin (profileOf D x).throughs :=
  Fin.cast (profileOf_counts D x hd).2 (D.throughIndexEquivFin x i)

/-- The terminal connector's anchor equals the actual released attachment. -/
theorem terminal_attachment (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.TerminalIndex x) :
    label H x (D.fourNeighborEquiv x hd)
      (anchor ((profileOf D x).terminalAnchor (terminalNumber D x hd i))) =
      Sum.inl ((D.path i.val).toward x).walk.reverse.snd := by
  rw [label_anchor]
  have h := D.fourNeighborEquiv_terminal x hd (D.terminalIndexEquivFin x i)
  simp only [Equiv.symm_apply_apply] at h
  exact congrArg Sum.inl h

/-- Each through connector side equals the actual run-slot attachment. -/
theorem through_attachment (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.ThroughIndex x) (b : Fin 2) :
    label H x (D.fourNeighborEquiv x hd)
      (anchor ((profileOf D x).throughAnchor (throughNumber D x hd i) b)) =
      Sum.inl (D.runNeighbor x (.inr (i, finTwoEquiv b))) := by
  rw [label_anchor]
  have h := D.fourNeighborEquiv_through x hd (D.throughIndexEquivFin x i) b
  simp only [Equiv.symm_apply_apply] at h
  have he : (profileOf D x).throughAnchor (throughNumber D x hd i) b =
      ⟨D.endpointCount x + (2 * (D.throughIndexEquivFin x i).val + b.val), by
        have hc := D.degree_eq_endpoint_add_twice_through x
        have hi := (D.throughIndexEquivFin x i).isLt
        omega⟩ := by
    apply Fin.ext
    dsimp [Profile.throughAnchor, throughNumber]
    rw [← (profileOf_counts D x hd).1]
  rw [he]
  exact congrArg Sum.inl h

/-- Restore an actual terminal carrier using its automatically assigned checked tail. -/
noncomputable def assignedTerminal (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.TerminalIndex x) : NonemptyPath (expansion H x) := by
  let p := profileOf D x
  let n := terminalNumber D x hd i
  have hm := p.terminalWord_mem n
  have hc := p.valid.2.2.1 _ hm
  exact restoreTerminal (D.path i.val) x (Finset.mem_filter.mp i.property).2
    (D.fourNeighborEquiv x hd) (p.terminalWord n) hc.1 hc.2
    (p.valid.word_edges _ hm) (anchor (p.terminalAnchor n))
    (terminal_attachment D x hd i) (p.terminalWord_compatible n)

/-- Restore an actual through carrier using its automatically assigned checked connector. -/
noncomputable def assignedThrough (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.ThroughIndex x) : NonemptyPath (expansion H x) := by
  let p := profileOf D x
  let n := throughNumber D x hd i
  have hm := p.throughWord_mem n
  have hc := p.valid.2.2.1 _ hm
  have hi := (Finset.mem_filter.mp i.property).2
  exact restoreThrough (D.path i.val) x hi.1 hi.2.1 hi.2.2.symm
    (D.fourNeighborEquiv x hd) (p.throughWord n) hc.1 hc.2
    (p.valid.word_edges _ hm) (anchor (p.throughAnchor n 0)) (anchor (p.throughAnchor n 1))
    (through_attachment D x hd i 0) (through_attachment D x hd i 1)
    (p.throughWord_compatible n)

/-- Automatic through assignment preserves both outside endpoints. -/
theorem assignedThrough_endpoints (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.ThroughIndex x) :
    (assignedThrough D x hd i).start = Sum.inl (D.path i.val).start ∧
      (assignedThrough D x hd i).finish = Sum.inl (D.path i.val).finish := ⟨rfl, rfl⟩

/-- Automatic terminal assignment preserves the old outside endpoint. -/
theorem assignedTerminal_start (D : Decomposition H) (x : V) (hd : H.degree x = 4)
    (i : D.TerminalIndex x) :
    (assignedTerminal D x hd i).start = Sum.inl ((D.path i.val).toward x).start := rfl

end Gallai.Star
