/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorOriginal

/-! # One-credit separated original-edge certificate contract -/

namespace Gallai.Certificate.ThreeAnchor

/-- All three anchors are present, attachments are distinct, and the tails
together with at most one new path partition the augmented local target.
Tail interiors may visit other anchors because ambient components separate them. -/
def CheapOriginalAccepted (s : State) (p q : Fin 3)
    (tails added : List (List Vertex)) (a : Fin tails.length → Fin 3) : Prop :=
  syndrome s = {p, q} ∧ p ≠ q ∧
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (s i)).val.testBit j.val = true) ∧
    Function.Injective a ∧
    (∀ i : Fin tails.length, tails[i].head? = some (anchor (a i))) ∧
    Accepted (targetEdges s ∪ {s(anchor p, anchor q)}) (tails ++ added) ∧
    added.length ≤ 1

instance (s : State) (p q : Fin 3) (tails added : List (List Vertex))
    (a : Fin tails.length → Fin 3) : Decidable (CheapOriginalAccepted s p q tails added a) := by
  unfold CheapOriginalAccepted Function.Injective
  infer_instance

/-- Exact two-family count, retaining tail occurrence multiplicities. -/
theorem CheapOriginalAccepted.edge_count {s : State} {p q : Fin 3}
    {tails added : List (List Vertex)} {a : Fin tails.length → Fin 3}
    (h : CheapOriginalAccepted s p q tails added a) (e : Sym2 Vertex) :
    (∑ i : Fin tails.length, (wordEdges tails[i]).count e) +
      (∑ i : Fin added.length, (wordEdges added[i]).count e) =
      if e ∈ targetEdges s ∪ {s(anchor p, anchor q)} then 1 else 0 := by
  have hsum (ws : List (List Vertex)) : (familyEdges ws).count e =
      ∑ i : Fin ws.length, (wordEdges ws[i]).count e := by
    rw [familyEdges, List.count_flatMap, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  have hc := congrArg (Multiset.count e) h.2.2.2.2.2.1.2
  simp only [Multiset.coe_count, familyEdges, List.flatMap_append, List.count_append] at hc
  rw [← hsum tails, ← hsum added]
  change (familyEdges tails).count e + (familyEdges added).count e = _
  rw [show (familyEdges tails).count e + (familyEdges added).count e = _ from hc]
  split_ifs with he
  · exact Multiset.count_eq_one_of_mem (Finset.nodup _) he
  · exact Multiset.count_eq_zero_of_notMem he

/-- First three-anchor original one-credit record, from the pinned catalogue. -/
theorem cheap_original_control :
    CheapOriginalAccepted Catalogue.state01 0 2
      [[5,7,4,3,0,1,2,6], [6,3,5,4,0,2]] [[2,5]] ![0,1] := by decide

end Gallai.Certificate.ThreeAnchor
