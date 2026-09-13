/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStar

/-! # Ordinary size-two carrier-aware local interfaces

The normalized syndrome is pq. Slots are X,r,s,unused in through mode and
X0,X1,r,s in terminal mode. Empty optional words leave their old endpoint
unchanged; they are not zero-edge members of the local path decomposition.
This schema does not assert catalogue coverage or arbitrary-order transport.
-/
namespace Gallai.Certificate.SizeTwo
open Star.Vertex
abbrev Vertex := Star.Vertex
abbrev State := CompletedStar.State

/-- The first five partitions are through, the final eight terminal. -/
def through (i : Fin 13) : Bool := decide (i.val < 5)

def boundary (i : Fin 13) (j : Fin 4) : List Vertex :=
  if through i then ![[p,q],[r],[s],[]] j else ![[p],[q],[r],[s]] j

/-- Equal owner labels mean pieces are inserted in the same old carrier. -/
def owner (i : Fin 13) : Fin 4 → Fin 4 :=
  ![![0,0,0,3], ![0,0,1,3], ![0,1,0,3], ![0,1,1,3], ![0,1,2,3],
    ![0,1,0,1], ![0,1,0,2], ![0,1,1,0], ![0,1,1,2],
    ![0,1,2,0], ![0,1,2,1], ![0,1,2,2], ![0,1,2,3]] i

def mandatory (i : Fin 13) (j : Fin 4) : Prop :=
  j = 0 ∨ (through i = false ∧ j = 1)

instance (i : Fin 13) (j : Fin 4) : Decidable (mandatory i j) := by
  unfold mandatory; infer_instance

/-- Released/private support only; all old anchors are excluded. -/
def internal (word : List Vertex) : Finset Vertex :=
  word.toFinset ∩ Star.fresh.toFinset

def roleAccepted (i : Fin 13) (j : Fin 4) (word : List Vertex) : Prop :=
  if boundary i j = [] then word = []
  else (word = [] ∧ ¬ mandatory i j) ∨
    Compatible (boundary i j) Star.fresh.toFinset word

instance (i : Fin 13) (j : Fin 4) (w : List Vertex) : Decidable (roleAccepted i j w) := by
  unfold roleAccepted; infer_instance

def activeWords (words : Fin 4 → List Vertex) : List (List Vertex) :=
  (List.ofFn words).filter (fun w => !w.isEmpty)

/-- Ordinary two-credit records check coincidences of old carriers, not
merely compatibility of each role in isolation. Words are stored oriented. -/
def OrdinaryAccepted (state : State) (i : Fin 13)
    (words : Fin 4 → List Vertex) (added : List (List Vertex)) : Prop :=
  (∀ j, roleAccepted i j (words j)) ∧
  (∀ j k, j ≠ k → owner i j = owner i k →
    Disjoint (internal (words j)) (internal (words k))) ∧
  Accepted (CompletedStar.targetEdges state) (activeWords words ++ added) ∧
  added.length ≤ 2

instance (s : State) (i : Fin 13) (w : Fin 4 → List Vertex) (a : List (List Vertex)) :
    Decidable (OrdinaryAccepted s i w a) := by
  unfold OrdinaryAccepted; infer_instance

/-- Both terminal hub carriers are distinct in every terminal interface. -/
theorem terminal_owners_distinct : ∀ i : Fin 13, through i = false →
    owner i 0 ≠ owner i 1 := by decide

/-- A literal basic catalogue record, including the two optional empty tails. -/
theorem basic_empty_tails : OrdinaryAccepted ![0,0,0,0,3] 0
    ![[p,d,q],[],[],[]] [[a,b,x,c],[a,x,d,c]] := by decide

/-- A missing required connector is rejected, even before coverage checks. -/
theorem required_connector_nonempty (i : Fin 13) : ¬ roleAccepted i 0 [] := by
  revert i
  decide

end Gallai.Certificate.SizeTwo
