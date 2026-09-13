/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorCheapSelection
import Gallai.Transport.ThreeAnchorCheapTransport
import Gallai.Structure.ThreeAnchorUsed
import Gallai.Structure.PairRepairAlignment
import Gallai.Certificates.ThreeAnchorStateCode
import Gallai.Transport.ThreeAnchorBothRepairs

/-! # Exhaustive one-credit witnesses close sharp whole-deletion pair repairs -/

namespace Gallai.WholeBowtie

open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A whole-deletion code with three repaired components has the Gallai budget,
with the designated even retained vertex exposed. No finite witness is assumed. -/
theorem threeAnchor_sharp_whole_removal
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcode : encode s ∈ syntheticCodes)
    (p q : {v : V // v ∉ B.vertices}) (hs : B.syndrome = {p.val,q.val})
    (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ E.endpointCount y.val := by
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
  have hrt : A r ≠ A t := fun he => hrecord.2.1 (A.injective he)
  have hs' := B.threeAnchor_syndrome_pair A hcover s hrows r t hrecord.1
  have heq := B.pairRepaired_eq_of_pair_eq p q (A r) (A t) (hs.symm.trans hs')
  have hC' : Fintype.card (B.pairRepairedPuncture (A r) (A t)).ConnectedComponent = 3 := by
    have hn := congrArg (fun K : SimpleGraph {v : V // v ∉ B.vertices} =>
      Nat.card K.ConnectedComponent) heq
    simpa only [Nat.card_eq_fintype_card] using hn.symm.trans
      (show Nat.card (B.pairRepairedPuncture p q).ConnectedComponent = 3 by
        simpa only [Nat.card_eq_fintype_card] using hC)
  obtain ⟨D, hyD, hb⟩ :=
    B.pairRepaired_three_anchor_credit (A r) (A t) hrt hs' hc hA y hy hcap
  have hcredit : D.size + 1 ≤ (Fintype.card V + 1) / 2 := by
    rcases hb with htwo | hone
    · omega
    · exact hone.1
  obtain ⟨E, _, hsize, hends⟩ := B.cheapThree_reconstruction A s hrows hcover
    r t tails added a hrecord hc hA hC' D
  exact ⟨E, hsize.trans hcredit, hyD.trans (hends y hy)⟩

/-- After both repair statuses and sharp credits are handled, only the retained
hub route remains in the actual high pair-syndrome domain. -/
theorem threeAnchor_retained_frontier (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (ha : 3 ≤ B.activity) (hs : B.syndrome.card = 2)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State),
      (∀ v ∈ B.anchors, ∃ j, (A j).val = v) ∧
      (∀ i v, v ∈ B.row i ↔
        ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v) ∧
      ((∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
          2 ≤ E.endpointCount y.val) ∨ encode s ∈ retainedCodes) := by
  classical
  obtain ⟨A, s, hcover, hrows, hroute⟩ := B.threeAnchor_both_repairs_frontier hc hA y hy ha hs hcap
  refine ⟨A, s, hcover, hrows, ?_⟩
  rcases hroute with hdone | hret | ⟨p, q, _, hpair, hC, _⟩
  · exact Or.inl hdone
  · exact Or.inr hret
  · have hcard := Finset.card_image_of_injective (Certificate.ThreeAnchor.syndrome s)
      (Subtype.val_injective.comp A.injective)
    change ((Certificate.ThreeAnchor.syndrome s).image (fun j => (A j).val)).card =
      (Certificate.ThreeAnchor.syndrome s).card at hcard
    rw [B.threeAnchor_syndrome_image A hcover s hrows, hs] at hcard
    have hactivity : 3 ≤ (Finset.univ.filter fun i : Fin 5 => i ≠ 0 ∧ s i ≠ 0).card := by
      rw [B.threeAnchor_activity A s hrows]
      exact ha
    rcases state_pair_partition s hactivity hcard.symm with hcode | hret
    · exact Or.inl (B.threeAnchor_sharp_whole_removal A s hcover hrows hcode p q
        hpair hC hc hA y hy hcap)
    · exact Or.inr hret

end Gallai.WholeBowtie
