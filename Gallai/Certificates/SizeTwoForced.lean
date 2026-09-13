/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoOrdinary

/-! # One-extra-endpoint schema for the forced size-two records

The actual 34 records have no r-tail and exactly one nonempty p/q-tail.
The extra tail belongs to a carrier distinct from the X,r,s carrier, so it
need not have disjoint fresh support from the connector or s-tail. Only the
connector and s-tail can be inserted on the same old carrier.
-/
namespace Gallai.Certificate.SizeTwo.Forced

open Star.Vertex

def extraAnchor (j : Fin 2) : Star.Vertex := ![p,q] j

def localWords (connector extra tail : List Star.Vertex)
    (added : List (List Star.Vertex)) : List (List Star.Vertex) :=
  [connector,extra] ++ (if tail = [] then [] else [tail]) ++ added

/-- A forced record is an exact partition with a single extra endpoint role.
It does not assert that its actual extra carrier has already been selected. -/
def AcceptedRecord (state : State) (j : Fin 2)
    (connector extra tail : List Star.Vertex) (added : List (List Star.Vertex)) : Prop :=
  Compatible [p,q] Star.fresh.toFinset connector ∧
  Compatible [extraAnchor j] Star.fresh.toFinset extra ∧
  (tail = [] ∨ Compatible [s] Star.fresh.toFinset tail) ∧
  Disjoint (internal connector) (internal tail) ∧
  Accepted (CompletedStar.targetEdges state) (localWords connector extra tail added) ∧
  added.length ≤ 2

instance (state : State) (j : Fin 2) (connector extra tail : List Star.Vertex)
    (added : List (List Star.Vertex)) :
    Decidable (AcceptedRecord state j connector extra tail added) := by
  unfold AcceptedRecord
  infer_instance

/-- A literal stored forced record: the q-tail may share fresh vertices with
the connector because the forced-selection lemma places it on another carrier. -/
theorem first_record : AcceptedRecord ![3,15,15,15,15] 1
    [p,a,q] [q,b,a] [s,c,d,x,b]
    [[a,r,b,p,c,x,q,d,s],[b,s,a,x,p,d,r,c,q]] := by decide

/-- Both mandatory pieces are nonempty, even when the optional s-tail is absent. -/
theorem required_nonempty {state : State} {j : Fin 2}
    {connector extra tail : List Star.Vertex} {added : List (List Star.Vertex)}
    (h : AcceptedRecord state j connector extra tail added) :
    connector ≠ [] ∧ extra ≠ [] := by
  constructor
  · intro he
    have hh := h.1.1
    simp [he] at hh
  · intro he
    have hh := h.2.1.1
    simp [he] at hh

end Gallai.Certificate.SizeTwo.Forced
