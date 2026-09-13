/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.Star
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.FinCases

/-!
# Indexed connectors for the three star interfaces

Terminals precede through carriers, and the two sides of a through carrier
receive consecutive anchor labels. This is the finite interface consumed by
the actual run-slot ordering, not an assumption about ambient paths.
-/

namespace Gallai.Star

/-- The possible endpoint counts of a degree-four hub. -/
inductive Profile
  /-- Two through carriers. -/
  | zero
  /-- Two terminal carriers and one through carrier. -/
  | two
  /-- Four terminal carriers. -/
  | four
  deriving DecidableEq

/-- Number of terminal carriers in an interface. -/
def Profile.terminals : Profile → ℕ
  | .zero => 0
  | .two => 2
  | .four => 4

/-- Number of through carriers in an interface. -/
def Profile.throughs : Profile → ℕ
  | .zero => 2
  | .two => 1
  | .four => 0

/-- Every interface accounts for exactly four spokes. -/
theorem Profile.degree (p : Profile) : p.terminals + 2 * p.throughs = 4 := by
  cases p <;> decide

/-- Interpret the numeric anchor order as its certificate symbol. -/
def anchor (i : Fin 4) : Vertex :=
  [Vertex.p, .q, .r, .s][i.val]'(by simp)

/-- The terminal-first list of all old runs. -/
def Profile.old : Profile → List (List Vertex)
  | .zero => oldZero
  | .two => oldTwo
  | .four => oldFour

/-- The replacement connector of each old run, in the same order. -/
def Profile.replacements : Profile → List (List Vertex)
  | .zero => replaceZero
  | .two => replaceTwo
  | .four => replaceFour

/-- The two additional paths belonging to an interface. -/
def Profile.added : Profile → List (List Vertex)
  | .zero => addZero
  | .two => addTwo
  | .four => addFour

/-- The number of endpoints at the released hub after reconstruction. -/
def Profile.output : Profile → ℕ
  | .zero => 0
  | .two => 2
  | .four => 0

/-- Each indexed interface is exactly one of the checked finite certificates. -/
theorem Profile.valid (p : Profile) : Valid p.old p.replacements p.added p.output := by
  cases p
  · exact zero_valid
  · exact two_valid
  · exact four_valid

/-- The replacement list has one entry for every old carrier at the hub. -/
theorem Profile.replacements_length (p : Profile) :
    p.replacements.length = p.terminals + p.throughs := by
  cases p <;> decide

/-- Anchor occupied by a terminal carrier. -/
def Profile.terminalAnchor (p : Profile) (i : Fin p.terminals) : Fin 4 :=
  ⟨i.val, by have h := p.degree; omega⟩

/-- Consecutive anchors occupied by the two sides of a through carrier. -/
def Profile.throughAnchor (p : Profile) (i : Fin p.throughs) (b : Fin 2) : Fin 4 :=
  ⟨p.terminals + (2 * i.val + b.val), by have h := p.degree; omega⟩

/-- Connector replacing the numbered terminal run. -/
def Profile.terminalWord (p : Profile) (i : Fin p.terminals) : List Vertex :=
  p.replacements[i.val]'(by rw [p.replacements_length]; omega)

/-- Connector replacing the numbered through run. -/
def Profile.throughWord (p : Profile) (i : Fin p.throughs) : List Vertex :=
  p.replacements[p.terminals + i.val]'(by rw [p.replacements_length]; omega)

/-- Terminal connectors belong to the checked replacement list. -/
theorem Profile.terminalWord_mem (p : Profile) (i : Fin p.terminals) :
    p.terminalWord i ∈ p.replacements ++ p.added :=
  List.mem_append_left _ (List.getElem_mem _)

/-- Through connectors belong to the checked replacement list. -/
theorem Profile.throughWord_mem (p : Profile) (i : Fin p.throughs) :
    p.throughWord i ∈ p.replacements ++ p.added :=
  List.mem_append_left _ (List.getElem_mem _)

/-- Each terminal word avoids every other old anchor. -/
theorem Profile.terminalWord_compatible (p : Profile) (i : Fin p.terminals) :
    compatible [anchor (p.terminalAnchor i), .x] (p.terminalWord i) := by
  cases p <;> dsimp [Profile.terminals] at i
  · exact Fin.elim0 i
  · fin_cases i <;> unfold compatible <;> decide
  · fin_cases i <;> unfold compatible <;> decide

/-- Each through word has exactly the prescribed two old attachments. -/
theorem Profile.throughWord_compatible (p : Profile) (i : Fin p.throughs) :
    compatible [anchor (p.throughAnchor i 0), .x, anchor (p.throughAnchor i 1)]
      (p.throughWord i) := by
  cases p <;> dsimp [Profile.throughs] at i
  · fin_cases i <;> unfold compatible <;> decide
  · fin_cases i; unfold compatible; decide
  · exact Fin.elim0 i

end Gallai.Star
