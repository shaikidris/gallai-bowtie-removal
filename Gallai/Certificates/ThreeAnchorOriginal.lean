/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorSyntheticCatalogue

/-! # Original-edge one-tail certificates for the three-anchor representatives

Literal records from the pinned complete-three-anchor certificate. This module
checks the seventeen representatives, not their orbit coverage or ambient lift.
-/

namespace Gallai.Certificate.ThreeAnchor

/-- Original repair deletion exposes one anchor endpoint. A core-only tail and
at most two new paths partition the local edges including that repair edge. -/
def OriginalAccepted (s : State) (p q a : Fin 3)
    (tail : List Vertex) (added : List (List Vertex)) : Prop :=
  syndrome s = {p, q} ∧ p ≠ q ∧
    (∃ i : Fin 5, (rowMask (s i)).val.testBit a.val = true) ∧
    tail.head? = some (anchor a) ∧
    (∀ v ∈ tail.tail, v.val < 5) ∧
    Accepted (targetEdges s ∪ {s(anchor p, anchor q)}) (tail :: added) ∧
    added.length ≤ 2

instance (s : State) (p q a : Fin 3) (tail : List Vertex)
    (added : List (List Vertex)) : Decidable (OriginalAccepted s p q a tail added) := by
  unfold OriginalAccepted
  infer_instance

/-- Exact finite count consumed by the original-edge reconstruction. -/
theorem OriginalAccepted.edge_count {s : State} {p q a : Fin 3}
    {tail : List Vertex} {added : List (List Vertex)}
    (h : OriginalAccepted s p q a tail added) (e : Sym2 Vertex) :
    (wordEdges tail).count e +
      (∑ j : Fin added.length, (wordEdges added[j]).count e) =
      if e ∈ targetEdges s ∪ {s(anchor p, anchor q)} then 1 else 0 := by
  have hc := h.2.2.2.2.2.1.edge_count e
  simpa [Fin.sum_univ_succ] using hc

namespace Original

/-- Representative states in the same order as the pinned synthetic catalogue. -/
def state (i : Fin 17) : State :=
  ![Catalogue.state00, Catalogue.state01, Catalogue.state02, Catalogue.state03,
    Catalogue.state04, Catalogue.state05, Catalogue.state06, Catalogue.state07,
    Catalogue.state08, Catalogue.state09, Catalogue.state10, Catalogue.state11,
    Catalogue.state12, Catalogue.state13, Catalogue.state14, Catalogue.state15,
    Catalogue.state16] i

/-- First repair endpoint. -/
def left (i : Fin 17) : Fin 3 := ![0,0,0,1,0,0,1,0,1,0,1,0,1,1,0,0,0] i

/-- Second repair endpoint. -/
def right (i : Fin 17) : Fin 3 := ![1,2,1,2,1,1,2,1,2,1,2,2,2,2,2,1,1] i

/-- Endpoint source for the single tail. -/
def attachment (i : Fin 17) : Fin 3 := ![0,0,0,0,1,1,0,1,0,1,0,1,1,1,1,1,1] i

/-- Every representative uses the same core order after its attachment. -/
def tail (i : Fin 17) : List Vertex := [anchor (attachment i),4,3,0,2,1]

/-- Two added paths per original-edge representative. -/
def added (i : Fin 17) : List (List Vertex) :=
  ![[[1,0,4,6,2,5,3],[3,6,5]],
    [[1,0,4,7,5,2,6,3],[3,5]],
    [[1,0,4,7,3,5,2,6],[5,6]],
    [[1,0,4,7,6,2,5,3],[3,6,1,5]],
    [[1,6,2,5,3,7,4,0],[6,5,1,0]],
    [[1,6,3,5,2,7,4,0],[6,5,1,0]],
    [[1,0,4,7,6,2,5,3],[3,6,0,5]],
    [[1,0,4,7,3,5,6,2],[2,5,0,6]],
    [[1,0,4,6,3,5,2,7],[5,0,6,7]],
    [[1,0,4,7,2,5,6,3],[3,5,0,6]],
    [[1,0,4,7,2,5,3],[3,7,6,0,5]],
    [[1,0,4,7,2,5,3],[3,7,5,0,6]],
    [[1,0,5,2,7,6,3],[3,7,4,0,6]],
    [[2,5,3,7,4,0,1,6],[1,5,0,6,7,2]],
    [[1,5,2,7,3,6,0,4],[4,7,5,0,1,6]],
    [[1,5,2,7,3,6,0,4],[4,7,1,0,5,6]],
    [[1,5,3,7,2,6,0,4],[4,7,1,0,5,6]]] i

set_option maxRecDepth 4096 in
set_option maxHeartbeats 800000 in
/-- All seventeen literal original-edge one-tail identities pass the finite contract. -/
theorem checked : ∀ i : Fin 17,
    OriginalAccepted (state i) (left i) (right i) (attachment i) (tail i) (added i) := by
  decide

end Original
end Gallai.Certificate.ThreeAnchor
