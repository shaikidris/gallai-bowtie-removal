/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PairInductionCredit
import Gallai.Certificates.ThreeAnchorCheapSelection
import Gallai.Transport.ThreeAnchorCheapTransport
import Gallai.Structure.ThreeAnchorUsed
import Gallai.Structure.PairRepairAlignment
import Gallai.Certificates.ThreeAnchorStateCode

/-! # Sharp three-anchor lifting without a single-exception budget

The input decomposition can come from smaller-family induction. All original
even endpoint reserves are retained on the resulting common witness.
-/
namespace Gallai.Composition
open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Three repaired components admit a one-path lift for every whole-deletion code. -/
theorem three_pair_sharp_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcode : encode s ∈ syntheticCodes)
    (p q : {v : V // v ∉ B.vertices}) (hs : B.syndrome = {p.val, q.val})
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3) :
    ∀ D : Decomposition (B.pairRepairedPuncture p q),
      ∃ E : Decomposition G, E.size ≤ D.size + 1 ∧
        ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
          D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  have hcard : B.anchors.card = 3 := by
    have hle := B.pairRepaired_components_le_anchors p q hs hc
    omega
  have hused := B.threeAnchor_all_used A hcover s hrows hcard
  have hused' : ∀ j : Fin 3, ∃ i : Fin 5,
      (rowMask (decode (encode s) i)).val.testBit j.val = true := by
    simpa only [decode_encode] using hused
  have hw := CheapOrbits.cheap_witness (encode s)
    (CheapOrbits.cheap_coverage (encode s) hcode hused')
  rw [decode_encode] at hw
  obtain ⟨r, t, tails, added, a, hrecord⟩ := hw
  have hs' := B.threeAnchor_syndrome_pair A hcover s hrows r t hrecord.1
  have heq := B.pairRepaired_eq_of_pair_eq p q (A r) (A t) (hs.symm.trans hs')
  have hC' : Fintype.card (B.pairRepairedPuncture (A r) (A t)).ConnectedComponent = 3 := by
    have hn := congrArg (fun K : SimpleGraph {v : V // v ∉ B.vertices} =>
      Nat.card K.ConnectedComponent) heq
    simpa only [Nat.card_eq_fintype_card] using hn.symm.trans
      (show Nat.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 by
        simpa only [Nat.card_eq_fintype_card] using hC)
  have lift : ∀ D : Decomposition (B.pairRepairedPuncture (A r) (A t)),
      ∃ E : Decomposition G, E.size ≤ D.size + 1 ∧
        ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
          D.endpointCount w ≤ E.endpointCount w.val := by
    intro D
    obtain ⟨E, _, hb, he⟩ := B.cheapThree_reconstruction A s hrows hcover
      r t tails added a hrecord hc hA hC' D
    exact ⟨E, hb, he⟩
  rw [← heq] at lift
  exact lift

end Gallai.Composition
