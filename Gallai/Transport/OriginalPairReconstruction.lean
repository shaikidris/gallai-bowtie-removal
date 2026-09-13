/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.OriginalPairFamily

/-! # Reconstruct an original repair edge using a terminal extension -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A tail and additional paths covering exactly the deleted local edges and
the original repair edge reconstruct the graph. Only the tail attachment can
spend an old endpoint reserve; the number of added paths is exact. -/
theorem originalPair_reconstruction (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (D : Decomposition (B.pairRepairedPuncture p q))
    (a : {v : V // v ∉ B.vertices}) (hpos : 0 < D.endpointCount a)
    (T : NonemptyPath G) (ht : T.start = a.val)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    {t : ℕ} (N : Fin t → NonemptyPath G)
    (hlocal : ∀ e ∈ G.edgeSet,
      T.walk.edges.count e + (∑ j, (N j).walk.edges.count e) =
        if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s(p.val,q.val) then 1 else 0) :
    ∃ E : Decomposition G, E.size = D.size + t ∧
      ∀ w : {v // v ∉ B.vertices}, w ≠ a →
        D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  obtain ⟨F, hcount, hends⟩ := B.originalPairSelectedFamily p q hpq D a hpos T ht hf
  let family : Fin D.size ⊕ Fin t → NonemptyPath G := Sum.elim F N
  have hcover (e : Sym2 V) (he : e ∈ G.edgeSet) :
      (∑ i, (family i).walk.edges.count e) = 1 := by
    rw [Fintype.sum_sum_type]
    change (∑ i, (F i).walk.edges.count e) + (∑ j, (N j).walk.edges.count e) = 1
    rw [hcount e he, Nat.add_assoc, hlocal e he]
    split <;> simp
  let E : Decomposition G := Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + t) => family (finSumFinEquiv.symm i)) (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
        (fun i => (family i).walk.edges.count e)).trans (hcover e he))
  refine ⟨E, rfl, ?_⟩
  intro w hw
  change D.endpointCount w ≤ ∑ i : Fin (D.size + t),
    ((if (family (finSumFinEquiv.symm i)).start = w.val then 1 else 0) +
      (if (family (finSumFinEquiv.symm i)).finish = w.val then 1 else 0))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin t ≃ Fin (D.size + t)).symm.sum_comp
      (fun i => (if (family i).start = w.val then 1 else 0) +
        (if (family i).finish = w.val then 1 else 0)),
    Fintype.sum_sum_type]
  change D.endpointCount w ≤
    (∑ i, ((if (F i).start = w.val then 1 else 0) +
      (if (F i).finish = w.val then 1 else 0))) + _
  rw [hends w hw]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
