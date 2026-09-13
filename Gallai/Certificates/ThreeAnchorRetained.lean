/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorSynthetic

/-! # Ordinary retained-hub interfaces for the six three-anchor representatives -/

namespace Gallai.Certificate.ThreeAnchor

/-- Private deletion toggles precisely the odd private column counts. -/
def privateSyndrome (s : State) : Finset (Fin 3) :=
  Finset.univ.filter fun j => Odd ((Finset.univ.filter fun i : Fin 5 =>
    i ≠ 0 ∧ (rowMask (s i)).val.testBit j.val = true).card)

/-- In the normalized representatives the optional original repair edge is qr. -/
def retainedRepair (repair : Bool) : Finset (Sym2 Vertex) :=
  if repair then {s(anchor 1, anchor 2)} else ∅

/-- A through-hub carrier releases both spokes; its replacement can reuse x. -/
def RetainedPassingAccepted (s : State) (repair : Bool)
    (connector : List Vertex) (added : List (List Vertex)) : Prop :=
  s 0 = 1 ∧ privateSyndrome s = (if repair then {1, 2} else ∅) ∧
  connector.head? = some (anchor 0) ∧ connector.getLast? = some (anchor 1) ∧
  (∀ v ∈ connector, v = anchor 0 ∨ v = anchor 1 ∨ v.val < 5) ∧
  Accepted (targetEdges s ∪ retainedRepair repair) (connector :: added) ∧ added.length ≤ 2

/-- Terminal carriers keep their spokes and extend only into deleted private vertices. -/
def RetainedEndingAccepted (s : State) (repair : Bool)
    (tails added : List (List Vertex)) : Prop :=
  s 0 = 1 ∧ privateSyndrome s = (if repair then {1, 2} else ∅) ∧
  tails.length ≤ 2 ∧
  (∀ w ∈ tails, w.head? = some 0 ∧ ∀ v ∈ w.tail, 0 < v.val ∧ v.val < 5) ∧
  Accepted ((targetEdges s \ {s(0, anchor 0), s(0, anchor 1)}) ∪ retainedRepair repair)
    (tails ++ added) ∧ added.length ≤ 2

instance (s : State) (r : Bool) (c : List Vertex) (a : List (List Vertex)) :
    Decidable (RetainedPassingAccepted s r c a) := by
  unfold RetainedPassingAccepted; infer_instance

instance (s : State) (r : Bool) (t a : List (List Vertex)) :
    Decidable (RetainedEndingAccepted s r t a) := by
  unfold RetainedEndingAccepted; infer_instance

namespace Retained

def state (i : Fin 6) : State :=
  ![![1,1,1,1,1], ![1,1,1,1,2], ![1,1,1,2,2],
    ![1,1,2,1,2], ![1,1,2,2,2], ![1,2,2,2,2]] i

def repair (i : Fin 6) : Bool := decide (i = 1 ∨ i = 4)

def passing (i : Fin 6) : List Vertex :=
  ![[5,1,2,0,3,4,6], [5,1,2,0,4,3,6], [5,3,4,0,1,2,6],
    [5,1,2,0,4,3,6], [5,3,4,0,2,1,6], [5,1,2,0,6]] i

def passingAdded (i : Fin 6) : List (List Vertex) :=
  ![[[1,0,4,5,2,6,3],[1,6,0,5,3]],
    [[1,0,3,5,2,6,7,4],[1,6,0,5,4]],
    [[1,6,0,2,5,4,7,3],[1,5,0,3]],
    [[1,6,0,3,5,2,7,4],[1,0,5,4]],
    [[1,5,2,7,3,0,6],[1,0,5,4,7,6]],
    [[1,7,3,4,0,5,2],[1,0,3,5,4,7,2]]] i

def endingAdded (i : Fin 6) : List (List Vertex) :=
  ![[[1,5,3,0,4,6,2],[2,5,4,3,6,1,0]],
    [[1,5,3,0,4,7,6,2],[2,5,4,3,6,1,0]],
    [[1,6,2,5,3,0,4,7],[7,3,4,5,1,0]],
    [[1,6,3,0,4,5,2,7],[7,4,3,5,1,0]],
    [[1,6,7,3,0,4,5,2],[2,7,4,3,5,1,0]],
    [[1,5,3,0,4,7,2],[2,5,4,3,7,1,0]]] i

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- Six ordinary passing identities, including the correct original-edge repair status. -/
theorem passing_checked : ∀ i : Fin 6,
    RetainedPassingAccepted (state i) (repair i) (passing i) (passingAdded i) := by decide

/-- Six ordinary ending identities; one x-terminal carrier suffices in each representative. -/
theorem ending_checked : ∀ i : Fin 6,
    RetainedEndingAccepted (state i) (repair i) [[0,2,1]] (endingAdded i) := by decide

/-- A synthetic qr edge is replaced without releasing either retained spoke.
Its connector must avoid the retained hub, even if its old carrier traverses x. -/
def SyntheticAccepted (s : State) (connector : List Vertex)
    (added : List (List Vertex)) : Prop :=
  s 0 = 1 ∧ privateSyndrome s = {1, 2} ∧
  connector.head? = some (anchor 1) ∧ connector.getLast? = some (anchor 2) ∧
  (∀ v ∈ connector, v = anchor 1 ∨ v = anchor 2 ∨ (0 < v.val ∧ v.val < 5)) ∧
  Accepted (targetEdges s \ {s(0, anchor 0), s(0, anchor 1)}) (connector :: added) ∧
  added.length ≤ 2

instance (s : State) (c : List Vertex) (a : List (List Vertex)) :
    Decidable (SyntheticAccepted s c a) := by
  unfold SyntheticAccepted; infer_instance

/-- First retained synthetic repair identity. -/
theorem synthetic_one : SyntheticAccepted (state 1) [6,3,4,7]
    [[3,5,1,6,2,0,4],[3,0,1,2,5,4]] := by decide

/-- Second retained synthetic repair identity. -/
theorem synthetic_four : SyntheticAccepted (state 4) [6,1,2,7]
    [[1,5,2,0,3,4,7],[1,0,4,5,3,7]] := by decide

end Retained
end Gallai.Certificate.ThreeAnchor
