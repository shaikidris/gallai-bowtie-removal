/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorRetained

/-! # One-credit retained interfaces

These records consume separation of the r component from p, q and the hub.
They certify local edge partitions, not the ambient separation hypothesis.
-/

namespace Gallai.Certificate.ThreeAnchor.Retained

/-- A passing carrier is replaced and one remote endpoint carrier is extended.
The connector may visit r; the remote tail must not revisit its own anchor. -/
def CheapPassingAccepted (s : State) (repair : Bool)
    (connector remote : List Vertex) (added : List (List Vertex)) : Prop :=
  s 0 = 1 ∧ privateSyndrome s = (if repair then {1, 2} else ∅) ∧
  connector.head? = some (anchor 0) ∧ connector.getLast? = some (anchor 1) ∧
  remote.head? = some (anchor 2) ∧
  (∀ v ∈ remote.tail, v ≠ anchor 2) ∧
  Accepted (targetEdges s ∪ retainedRepair repair) (connector :: remote :: added) ∧
  added.length ≤ 1

/-- Up to two distinct hub-ending carriers and one remote carrier are extended.
Hub tails avoid both old hub neighbours; remote tails avoid their old anchor. -/
def CheapEndingAccepted (s : State) (repair : Bool)
    (tails : List (List Vertex)) (remote : List Vertex)
    (added : List (List Vertex)) : Prop :=
  s 0 = 1 ∧ privateSyndrome s = (if repair then {1, 2} else ∅) ∧
  tails.length ≤ 2 ∧
  (∀ w ∈ tails, w.head? = some 0 ∧
    ∀ v ∈ w.tail, (0 < v.val ∧ v.val < 5) ∨ v = anchor 2) ∧
  remote.head? = some (anchor 2) ∧
  (∀ v ∈ remote.tail, v ≠ anchor 2) ∧
  Accepted ((targetEdges s \ {s(0, anchor 0), s(0, anchor 1)}) ∪ retainedRepair repair)
    (tails ++ remote :: added) ∧ added.length ≤ 1

instance (s : State) (r : Bool) (c t : List Vertex) (a : List (List Vertex)) :
    Decidable (CheapPassingAccepted s r c t a) := by
  unfold CheapPassingAccepted; infer_instance

instance (s : State) (r : Bool) (t : List (List Vertex)) (c : List Vertex)
    (a : List (List Vertex)) : Decidable (CheapEndingAccepted s r t c a) := by
  unfold CheapEndingAccepted; infer_instance

/-- State zero has only two used anchors; the five others have remote records. -/
def cheapIndex (i : Fin 5) : Fin 6 := ⟨i.val + 1, by omega⟩

/-- Passing connectors in catalogue order C22, C23, C25, C27, C30. -/
def cheapPassing (i : Fin 5) : List Vertex :=
  ![[5,1,2,0,4,3,6], [5,3,4,0,1,2,6], [5,1,2,0,4,3,6],
    [5,1,2,7,3,4,0,6], [5,1,2,7,3,4,0,6]] i

/-- Remote tails paired with the passing connectors. -/
def cheapPassingRemote (i : Fin 5) : List Vertex :=
  ![[7,4,5,3,0,1,6,2], [7,4,5,2,0,6,1], [7,2,5,3,0,6,1],
    [7,6,1,0,3,5,2], [7,1,0,3,5,2]] i

/-- The sole new path for each passing interface. -/
def cheapPassingAdded (i : Fin 5) : List Vertex :=
  ![[2,5,0,6,7], [1,5,0,3,7], [1,0,5,4,7],
    [2,0,5,4,7], [2,0,5,4,7]] i

/-- Two hub tails for each ending interface. -/
def cheapEnding (i : Fin 5) : List (List Vertex) :=
  ![[[0,3,4,7],[0,2,1]], [[0,4,3,7],[0,2,1]],
    [[0,1,2,7],[0,4,3]], [[0,4,3,7,2,1],[0,1]],
    [[0,4,3,7,2,1],[0,1,7]]] i

/-- Remote tails paired with the two hub tails. -/
def cheapEndingRemote (i : Fin 5) : List Vertex :=
  ![[7,6,1,0,4,5,2], [7,4,5,3,0,1,6,2], [7,4,5,2,0,3,6,1],
    [7,6,1,5,3,0,2], [7,4,5,3,0,2]] i

/-- The sole new path for each ending interface. -/
def cheapEndingAdded (i : Fin 5) : List Vertex :=
  ![[1,5,3,6,2], [1,5,2], [1,5,3], [2,5,4,7], [1,5,2]] i

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- All five exact one-credit passing partitions. -/
theorem cheapPassing_checked : ∀ i : Fin 5,
    CheapPassingAccepted (state (cheapIndex i)) (repair (cheapIndex i))
      (cheapPassing i) (cheapPassingRemote i) [cheapPassingAdded i] := by decide

/-- All five exact one-credit ending partitions and their freshness restrictions. -/
theorem cheapEnding_checked : ∀ i : Fin 5,
    CheapEndingAccepted (state (cheapIndex i)) (repair (cheapIndex i))
      (cheapEnding i) (cheapEndingRemote i) [cheapEndingAdded i] := by decide

end Gallai.Certificate.ThreeAnchor.Retained
