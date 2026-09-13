/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Mathlib.Tactic.FinCases

/-! # Exact zero-syndrome three-anchor records

Literal records C04,C05,C07,C09,C11,C13,C16,C24,C26,C31 from the
pinned complete-three-anchor source (SHA-256
2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda).
No original or synthetic repair edge belongs to the target.
-/
namespace Gallai.Certificate.ThreeAnchor

def ZeroTwoAccepted (s : State) (a : Fin 3)
    (tail : List Vertex) (added : List (List Vertex)) : Prop :=
  syndrome s = ∅ ∧
    (∃ i : Fin 5, (rowMask (s i)).val.testBit a.val = true) ∧
    tail.head? = some (anchor a) ∧ (∀ v ∈ tail.tail, v.val < 5) ∧
    Accepted (targetEdges s) (tail :: added) ∧ added.length ≤ 2

instance (s : State) (a : Fin 3) (tail : List Vertex) (added : List (List Vertex)) :
    Decidable (ZeroTwoAccepted s a tail added) := by
  unfold ZeroTwoAccepted
  infer_instance

def ZeroOneAccepted (s : State) (tails added : List (List Vertex))
    (a : Fin tails.length → Fin 3) : Prop :=
  syndrome s = ∅ ∧
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (s i)).val.testBit j.val = true) ∧
    Function.Injective a ∧
    (∀ i : Fin tails.length, tails[i].head? = some (anchor (a i))) ∧
    Accepted (targetEdges s) (tails ++ added) ∧ added.length ≤ 1

instance (s : State) (tails added : List (List Vertex)) (a : Fin tails.length → Fin 3) :
    Decidable (ZeroOneAccepted s tails added a) := by
  unfold ZeroOneAccepted Function.Injective
  infer_instance

namespace ZeroCatalogue

def state (i : Fin 10) : State :=
  ![![0,0,1,2,3],
    ![0,1,1,1,1],
    ![0,1,1,2,2],
    ![0,1,2,1,2],
    ![1,0,1,1,1],
    ![1,0,1,2,2],
    ![1,0,2,1,2],
    ![1,1,1,2,3],
    ![1,1,2,1,3],
    ![1,2,2,2,3]] i

def attachment (i : Fin 10) : Fin 3 := ![1,0,0,0,0,0,0,1,1,1] i
def tail (i : Fin 10) : List Vertex := ![[6,4,3,0,2,1],
    [5,4,3,0,2,1],
    [5,4,3,0,2,1],
    [5,4,3,0,2,1],
    [5,4,3,0,2,1],
    [5,4,3,0,2,1],
    [5,4,3,0,2,1],
    [6,4,3,0,2,1],
    [6,4,3,0,2,1],
    [6,4,3,0,2,1]] i
def added (i : Fin 10) : List (List Vertex) := ![[[1,0,4,7,3,5,2,6]],
    [[1,0,4,6,2,5,3],[3,6,1,5]],
    [[1,6,2,5,3,7,4,0],[5,1,0]],
    [[1,6,3,5,2,7,4,0],[5,1,0]],
    [[1,0,4,6,2,5,3],[3,6,0,5]],
    [[1,0,4,7,3,5,2,6],[5,0,6]],
    [[1,0,4,7,2,5,3,6],[5,0,6]],
    [[1,5,2,6,0,4,7,3],[3,5,0,1,6]],
    [[1,5,2,7,4,0,6,3],[3,5,0,1,6]],
    [[1,0,4,7,2,5,3],[3,7,1,5,0,6]]] i

theorem two_checked : ∀ i : Fin 10,
    ZeroTwoAccepted (state i) (attachment i) (tail i) (added i) := by decide

/-- Exactly the eight representatives using all three anchors. -/
def fullIndex (i : Fin 8) : Fin 10 := ![0,2,3,5,6,7,8,9] i
def tails (i : Fin 8) : List (List Vertex) := ![[[5,2,1,0,3,7,4,6],[6,2,0,4,3,5]],
    [[5,3,7,4,0,1,2,6],[6,1,5,4,3,0,2]],
    [[5,1,2,7,4,0,3,6],[6,1,0,2,5,4,3]],
    [[5,3,7,4,0,1,2,6],[6,0,3,4,5,2]],
    [[5,3,4,7,2,1,0,6],[6,3,0,4,5,2]],
    [[5,0,3,7,4,6,2,1],[6,0,4,3,5,1]],
    [[5,0,6,3,4,7,2,1],[6,4,0,2,5,1]],
    [[5,1,2,7,3,4,0,6],[6,4,7,1,0,3,5,2]]] i
def oneAdded (i : Fin 8) : List (List Vertex) := ![[],
    [[2,5]],
    [[3,5]],
    [[2,0,5]],
    [[2,0,5]],
    [[5,2,0,1,6]],
    [[5,3,0,1,6]],
    [[2,0,5]]] i
def sources (i : Fin 8) : Fin (tails i).length → Fin 3 :=
  fun j => ⟨j.val, by
    have h : (tails i).length = 2 := by fin_cases i <;> rfl
    have hj := j.isLt
    omega⟩

theorem one_checked : ∀ i : Fin 8,
    ZeroOneAccepted (state (fullIndex i)) (tails i) (oneAdded i) (sources i) := by decide

end ZeroCatalogue
end Gallai.Certificate.ThreeAnchor
