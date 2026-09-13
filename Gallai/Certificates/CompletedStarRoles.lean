/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStar
import Gallai.Certificates.Profiles

/-! # Completed-star interfaces in carrier-selected anchor order

Terminals come first and the two sides of each through carrier are consecutive.
This chooses interfaces 0, 3 or 9 from the ten-interface catalogue; it does not
assert that a record exists, or that a fixed anchor order has these interfaces.
-/

namespace Gallai.Certificate.CompletedStar

/-- Canonical interface after numbering anchors by actual carrier slots. -/
def profileInterface : Star.Profile → Fin 10
  | .zero => 0
  | .two => 3
  | .four => 9

/-- Both finite anchor-symbol conventions agree. -/
theorem anchor_eq_star (j : Fin 4) : anchor j = Star.anchor j := by
  fin_cases j <;> rfl

/-- One ordered role is needed for each terminal or through carrier. -/
theorem profile_boundary_length (p : Star.Profile) :
    (boundaries (profileInterface p)).length = p.terminals + p.throughs := by
  cases p <;> rfl

/-- Position of a terminal in the completed-star replacement list. -/
def terminalRole (p : Star.Profile) (i : Fin p.terminals) :
    Fin (boundaries (profileInterface p)).length :=
  ⟨i.val, by rw [profile_boundary_length]; omega⟩

/-- Position of a through carrier, after all terminal carriers. -/
def throughRole (p : Star.Profile) (i : Fin p.throughs) :
    Fin (boundaries (profileInterface p)).length :=
  ⟨p.terminals + i.val, by rw [profile_boundary_length]; omega⟩

/-- The terminal role asks for exactly its actual numbered attachment. -/
theorem terminalRole_boundary (p : Star.Profile) (i : Fin p.terminals) :
    (boundaries (profileInterface p))[terminalRole p i] =
      [anchor (p.terminalAnchor i)] := by
  cases p <;> dsimp [Star.Profile.terminals] at i
  · exact Fin.elim0 i
  · fin_cases i <;> rfl
  · fin_cases i <;> rfl

/-- Each through role keeps its two slots on one carrier, in side order. -/
theorem throughRole_boundary (p : Star.Profile) (i : Fin p.throughs) :
    (boundaries (profileInterface p))[throughRole p i] =
      [anchor (p.throughAnchor i 0), anchor (p.throughAnchor i 1)] := by
  cases p <;> dsimp [Star.Profile.throughs] at i
  · fin_cases i <;> rfl
  · fin_cases i; rfl
  · exact Fin.elim0 i

/-- Every role occurs exactly once in the terminal/through enumeration. -/
def roleEquiv (p : Star.Profile) :
    Fin p.terminals ⊕ Fin p.throughs ≃ Fin (boundaries (profileInterface p)).length :=
  finSumFinEquiv.trans (finCongr (profile_boundary_length p).symm)

theorem roleEquiv_terminal (p : Star.Profile) (i : Fin p.terminals) :
    roleEquiv p (.inl i) = terminalRole p i := by
  apply Fin.ext
  rfl

theorem roleEquiv_through (p : Star.Profile) (i : Fin p.throughs) :
    roleEquiv p (.inr i) = throughRole p i := by
  apply Fin.ext
  rfl

end Gallai.Certificate.CompletedStar
