/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SeparatedCarrierSelection
import Gallai.Operations.FamilyReplace

/-! # Simultaneous separated tails preserve family size and endpoint reserves -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- All selected tails can be attached at once, with exact added edges and no
loss of endpoint reserves at even retained vertices. -/
theorem separatedOriginalFamily (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (hne : p ≠ q)
    (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
    (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3)
    (D : Decomposition (B.pairRepairedPuncture p q)) {k : ℕ}
    (a : Fin k ↪ {v : V // v ∉ B.vertices}) (ha : ∀ i, (a i).val ∈ B.anchors)
    (T : Fin k → NonemptyPath G) (ht : ∀ i, (T i).start = (a i).val)
    (hf : ∀ i v, v ∈ (T i).walk.support → v ∈ B.vertices ∨ v ∈ B.anchors) :
    ∃ F : Fin D.size → NonemptyPath G,
      (∀ e ∈ G.edgeSet, (∑ i, (F i).walk.edges.count e) =
        (if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s(p.val,q.val) then 0 else 1) +
          ∑ l, (T l).walk.edges.count e) ∧
      ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        (∑ i, ((if (F i).start = w.val then 1 else 0) +
          (if (F i).finish = w.val then 1 else 0) : ℕ)) = D.endpointCount w := by
  classical
  obtain ⟨j, hj⟩ := B.separatedCarrier_selection p q hne hs hc hA hC D a ha
  let P := fun l => (D.path (j l)).toward (a l)
  have hfinish (l) : (P l).finish.val = (a l).val := congrArg Subtype.val (hj l).2
  have hanchor (l) : (P l).finish.val ∈ B.anchors := (hfinish l).symm ▸ ha l
  have hjoin (l) : (P l).finish.val = (T l).start := (hfinish l).trans (ht l).symm
  let old := fun i => B.originalPairCarrier p q hpq (D.path i)
  let R := fun l => B.separatedOriginalExtension p q hpq hs hc hA hC
    (P l) (hanchor l) (T l) (hjoin l) (hf l)
  refine ⟨replaceFamily old j R, ?_, ?_⟩
  · intro e he
    have hR (l) : (R l).walk.edges.count e = (old (j l)).walk.edges.count e +
        (T l).walk.edges.count e := by
      change (B.separatedOriginalExtension p q hpq hs hc hA hC _ _ _ _ _).walk.edges.count e = _
      rw [B.separatedOriginalExtension_edges, List.count_append]
      change _ = (B.originalPairCarrier p q hpq (D.path (j l))).walk.edges.count e + _
      rw [B.originalPairCarrier_edges]
      congr 1
      dsimp only [P]
      by_cases hs' : (D.path (j l)).start = a l
      · rw [(D.path (j l)).toward_of_start_eq (a l) hs',
          NonemptyPath.reverse_edges, List.map_reverse, List.count_reverse]
      · rw [(D.path (j l)).toward_of_start_ne (a l) hs']
    have hsum := sum_replaceFamily old j R (fun Q => Q.walk.edges.count e)
      (fun l => (T l).walk.edges.count e) hR
    exact hsum.trans (congrArg (· + ∑ l, (T l).walk.edges.count e)
      (B.originalPair_edge_count p q hpq D e he))
  · intro w hw
    let measure := fun Q : NonemptyPath G =>
      (if Q.start = w.val then 1 else 0) + (if Q.finish = w.val then 1 else 0 : ℕ)
    have hR (l) : measure (R l) = measure (old (j l)) + 0 := by
      have he := B.separatedOriginalExtension_even_endpoints p q hpq hs hc hA hC
        (P l) (hanchor l) (T l) (hjoin l) (hf l) w hw
      have ho := (D.path (j l)).toward_endpoint_contribution (a l) w
      have ho' :
          ((if (P l).start.val = w.val then 1 else 0) +
            (if (P l).finish.val = w.val then 1 else 0 : ℕ)) =
          ((if (D.path (j l)).start.val = w.val then 1 else 0) +
            (if (D.path (j l)).finish.val = w.val then 1 else 0)) := by
        simpa only [P, Subtype.ext_iff] using ho
      change measure (R l) =
        ((if (D.path (j l)).start.val = w.val then 1 else 0) +
          (if (D.path (j l)).finish.val = w.val then 1 else 0)) + 0
      exact (he.trans ho').trans (Nat.add_zero _).symm
    have hsum := sum_replaceFamily old j R measure (fun _ => 0) hR
    have hold : (∑ i, measure (old i)) = D.endpointCount w := by
      unfold Decomposition.endpointCount
      apply Finset.sum_congr rfl
      intro i _
      change ((if (D.path i).start.val = w.val then 1 else 0) +
        (if (D.path i).finish.val = w.val then 1 else 0)) = _
      simp only [Subtype.ext_iff]
    simpa only [Finset.sum_const_zero, Nat.add_zero, hold] using hsum

end Gallai.WholeBowtie
