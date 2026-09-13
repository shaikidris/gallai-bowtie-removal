/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ThreeAnchorPairDomain
import Gallai.Certificates.ThreeAnchorSyntheticSelection
import Gallai.Transport.ThreeAnchorSyntheticTransport
import Gallai.Inputs.PairRepairedCredit

/-! # Selected synthetic interfaces close their actual graph budget cases -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Actual high pair-syndrome graphs are reconstructed unless they enter one
of the explicitly remaining interfaces. In particular, no certificate or
auxiliary decomposition is a hypothesis of this reduction. -/
theorem threeAnchor_pair_frontier (hc : G.Connected) (hA : B.anchors.card ≤ 3)
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
          (G.Adj p.val q.val ∨
            (Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 ∧
              (∑ C : (B.pairRepairedPuncture p q).ConnectedComponent,
                Fintype.card C.supp % 2) = 3))) := by
  classical
  obtain ⟨A, s, hcover, hrows, hroute⟩ := B.threeAnchor_pair_domain hc hA y hy ha hs
  refine ⟨A, s, hcover, hrows, ?_⟩
  rcases hroute with hsyn | hret
  · have hw := synthetic_witness (encode s) hsyn
    rw [decode_encode] at hw
    obtain ⟨p, q, connector, added, hrecord⟩ := hw
    have hne : A p ≠ A q := fun he => hrecord.2.1 (A.injective he)
    have hpair := B.threeAnchor_syndrome_pair A hcover s hrows p q hrecord.1
    by_cases he : G.Adj (A p).val (A q).val
    · exact Or.inr (Or.inr ⟨A p, A q, hne, hpair, Or.inl he⟩)
    · obtain ⟨D, hyD, hbudget⟩ :=
        B.pairRepaired_three_anchor_credit (A p) (A q) hne hpair hc hA y hy hcap
      rcases hbudget with htwo | hthree
      · obtain ⟨E, _, hsize, hends⟩ :=
          B.syntheticThree_reconstruction A s hrows p q connector added hrecord he D
        exact Or.inl ⟨E, hsize.trans htwo, hyD.trans (hends y)⟩
      · exact Or.inr (Or.inr ⟨A p, A q, hne, hpair, Or.inr hthree.2⟩)
  · exact Or.inr (Or.inl hret)

end Gallai.WholeBowtie
