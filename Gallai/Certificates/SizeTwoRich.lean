/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoOrdinary

/-! # One-credit rich-reserve local contracts

Interfaces 0/1 are through profiles with reserve r/s; 2/3 are terminal
profiles with reserve r/s. Every role occupies a distinct resulting carrier.
Thus no cross-role fresh-disjointness condition is imposed. Actual carrier
selection, merging and global path-count accounting are separate consumers.
-/
namespace Gallai.Certificate.SizeTwo.Rich
open Star.Vertex

/-- Whether the original hub carrier passes through the hub. -/
def isThrough (i : Fin 4) : Bool := decide (i.val < 2)

/-- The remote reserve is outside the normalized syndrome pq. -/
def reserve (i : Fin 4) : Star.Vertex := if i.val % 2 = 0 then r else s

/-- Two merged arms and a reserve tail, or one merged arm and three tails. -/
def boundary (i : Fin 4) : Fin 4 → List Star.Vertex :=
  if isThrough i then ![[p,reserve i],[q,reserve i],[reserve i],[]]
  else ![[p,reserve i],[q],[reserve i],[reserve i]]

/-- A connector cannot be omitted. All single-attachment tails are optional. -/
def mandatory (i : Fin 4) (j : Fin 4) : Prop := j = 0 ∨ (isThrough i = true ∧ j = 1)

instance (i j : Fin 4) : Decidable (mandatory i j) := by
  unfold mandatory; infer_instance

/-- Literal role compatibility; unused slots must be empty. -/
def roleAccepted (i j : Fin 4) (word : List Star.Vertex) : Prop :=
  if boundary i j = [] then word = []
  else (word = [] ∧ ¬ mandatory i j) ∨ Compatible (boundary i j) Star.fresh.toFinset word

instance (i j : Fin 4) (word : List Star.Vertex) : Decidable (roleAccepted i j word) := by
  unfold roleAccepted; infer_instance

/-- Ordinary rich merging saves one old carrier and adds at most two paths. -/
def AcceptedRecord (state : State) (i : Fin 4) (words : Fin 4 → List Star.Vertex)
    (added : List (List Star.Vertex)) : Prop :=
  (∀ j, roleAccepted i j (words j)) ∧
  Accepted (CompletedStar.targetEdges state) (activeWords words ++ added) ∧
  added.length ≤ 2

instance (state : State) (i : Fin 4) (words : Fin 4 → List Star.Vertex)
    (added : List (List Star.Vertex)) : Decidable (AcceptedRecord state i words added) := by
  unfold AcceptedRecord; infer_instance

/-- Two special through records split the hub carrier, merge one arm with a
reserve, and put a nonempty tail on the other arm. Only one new path is used. -/
def SeparatedAccepted (state : State) (i : Fin 4)
    (connector tail : List Star.Vertex) (added : List (List Star.Vertex)) : Prop :=
  isThrough i = true ∧
  Compatible [p,reserve i] Star.fresh.toFinset connector ∧
  Compatible [q] Star.fresh.toFinset tail ∧
  Accepted (CompletedStar.targetEdges state) ([connector,tail] ++ added) ∧
  added.length ≤ 1

instance (state : State) (i : Fin 4) (connector tail : List Star.Vertex)
    (added : List (List Star.Vertex)) : Decidable (SeparatedAccepted state i connector tail added) := by
  unfold SeparatedAccepted; infer_instance

/-- The first stored through interface, including the omitted reserve tail. -/
theorem first_through : AcceptedRecord ![0,0,3,12,12] 0
    ![[p,b,x,c,r],[q,b,a,x,d,r],[],[]] [[c,d],[c,s,d]] := by decide

/-- The first stored terminal interface permits all three optional tails empty. -/
theorem first_terminal : AcceptedRecord ![0,0,3,12,12] 2
    ![[p,b,x,c,r],[],[],[]] [[c,d,x,a,b,q],[c,s,d,r]] := by decide

/-- The exceptional r-reserve through interface. -/
theorem separated_r : SeparatedAccepted ![3,3,3,12,12] 0
    [p,a,b,x,c,d,r] [q,x,a] [[a,q,b,p,x,d,s,c,r]] := by decide

/-- The exceptional s-reserve through interface. -/
theorem separated_s : SeparatedAccepted ![3,3,3,12,12] 1
    [p,a,b,x,c,d,s] [q,x,a] [[a,q,b,p,x,d,r,c,s]] := by decide

/-- An empty mandatory connector fails before any edge-partition check. -/
theorem mandatory_nonempty (i j : Fin 4) (h : mandatory i j) : ¬ roleAccepted i j [] := by
  revert i j
  decide

/-- Every nonempty accepted role has the literal declared boundary. -/
theorem role_compatible {i j : Fin 4} {word : List Star.Vertex}
    (h : roleAccepted i j word) (hne : word ≠ []) :
    Compatible (boundary i j) Star.fresh.toFinset word := by
  unfold roleAccepted at h
  split at h
  · exact (hne h).elim
  · exact h.resolve_left (fun he => hne he.1)

end Gallai.Certificate.SizeTwo.Rich
