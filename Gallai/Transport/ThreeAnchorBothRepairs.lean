/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorPairFrontier
import Gallai.Transport.ThreeAnchorOriginalTransport
import Gallai.Certificates.ThreeAnchorOriginalSelection

/-! # Both repair statuses close every two-credit whole-deletion pair case -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

private theorem adjacency_of_pair_eq {u v r t : V} (hrt : r ≠ t)
    (he : ({u,v} : Finset V) = {r,t}) (huv : G.Adj u v) : G.Adj r t := by
  have hr : r = u ∨ r = v := by
    have hm : r ∈ ({u,v} : Finset V) := he.symm ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  have ht : t = u ∨ t = v := by
    have hm : t ∈ ({u,v} : Finset V) := he.symm ▸ (by simp)
    simpa only [Finset.mem_insert, Finset.mem_singleton] using hm
  rcases hr with rfl | rfl <;> rcases ht with rfl | rfl
  · exact False.elim (hrt rfl)
  · exact huv
  · exact huv.symm
  · exact False.elim (hrt rfl)

/-- Actual high pair-syndrome graphs reduce only to retained-hub codes or three
odd repaired components. Original repair edges are no longer an exception. -/
theorem threeAnchor_both_repairs_frontier (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (ha : 3 ≤ B.activity) (hs : B.syndrome.card = 2)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State),
      (∀ v ∈ B.anchors, ∃ j, (A j).val = v) ∧
      (∀ i v, v ∈ B.row i ↔
        ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v) ∧
      ((∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
          2 ≤ E.endpointCount y.val) ∨
        encode s ∈ retainedCodes ∨
        ∃ p q : {v : V // v ∉ B.vertices}, p ≠ q ∧
          B.syndrome = {p.val, q.val} ∧
          Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 ∧
          (∑ C : (B.pairRepairedPuncture p q).ConnectedComponent,
            Fintype.card C.supp % 2) = 3) := by
  classical
  obtain ⟨A, s, hcover, hrows, hroute⟩ := B.threeAnchor_pair_domain hc hA y hy ha hs
  refine ⟨A, s, hcover, hrows, ?_⟩
  rcases hroute with hcode | hret
  · have hw := OriginalOrbits.original_witness (encode s) hcode
    rw [decode_encode] at hw
    obtain ⟨p, q, a, tail, added, hrecord⟩ := hw
    have hne : A p ≠ A q := fun he => hrecord.2.1 (A.injective he)
    have hpair := B.threeAnchor_syndrome_pair A hcover s hrows p q hrecord.1
    by_cases he : G.Adj (A p).val (A q).val
    · obtain ⟨D, hyD, hbudget⟩ :=
        B.pairRepaired_three_anchor_credit (A p) (A q) hne hpair hc hA y hy hcap
      rcases hbudget with htwo | hthree
      · obtain ⟨E, _, hsize, hends⟩ := B.originalThree_reconstruction_of_parity
          A s hrows hcover p q a tail added hrecord he D
        exact Or.inl ⟨E, hsize.trans htwo, hyD.trans (hends y hy)⟩
      · exact Or.inr (Or.inr ⟨A p, A q, hne, hpair, hthree.2⟩)
    · have hw := synthetic_witness (encode s) hcode
      rw [decode_encode] at hw
      obtain ⟨r, t, connector, newPaths, hsyn⟩ := hw
      have hrt : A r ≠ A t := fun he => hsyn.2.1 (A.injective he)
      have hpair' := B.threeAnchor_syndrome_pair A hcover s hrows r t hsyn.1
      have hmissing : ¬ G.Adj (A r).val (A t).val := by
        intro hrtAdj
        apply he
        exact adjacency_of_pair_eq (fun h => hne (Subtype.ext h))
          (hpair'.symm.trans hpair) hrtAdj
      obtain ⟨D, hyD, hbudget⟩ :=
        B.pairRepaired_three_anchor_credit (A r) (A t) hrt hpair' hc hA y hy hcap
      rcases hbudget with htwo | hthree
      · obtain ⟨E, _, hsize, hends⟩ := B.syntheticThree_reconstruction
          A s hrows r t connector newPaths hsyn hmissing D
        exact Or.inl ⟨E, hsize.trans htwo, hyD.trans (hends y)⟩
      · exact Or.inr (Or.inr ⟨A r, A t, hrt, hpair', hthree.2⟩)
  · exact Or.inr (Or.inl hret)

end Gallai.WholeBowtie
