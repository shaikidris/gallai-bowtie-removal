/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompositionThreeAnchorSharp
import Gallai.Certificates.ThreeAnchorOriginalSelection
import Gallai.Certificates.ThreeAnchorSyntheticSelection
import Gallai.Transport.ThreeAnchorOriginalTransport
import Gallai.Transport.ThreeAnchorSyntheticTransport

/-! # Whole-deletion three-anchor pair lifts for composable families

Both repair-edge statuses and the sharp one-credit case consume the same
arbitrary input decomposition. No single-exception budget is required.
-/
namespace Gallai.Composition
open Certificate.ThreeAnchor Certificate.ThreeAnchor.Orbits
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

omit [Fintype V] [DecidableRel G.Adj] in
private theorem pair_adjacency (u v r t : V)
    (he : ({u, v} : Finset V) = {r, t}) : G.Adj u v ↔ G.Adj r t := by
  have hset : ({u, v} : Set V) = {r, t} := by
    simpa using congrArg (fun s : Finset V => (s : Set V)) he
  rcases Set.pair_eq_pair_iff.mp hset with ⟨hu, hv⟩ | ⟨hu, hv⟩
  · rw [hu, hv]
  · rw [hu, hv, SimpleGraph.adj_comm]

/-- Every whole-deletion code has a two-path lift in either repair-edge status. -/
theorem three_pair_two_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcode : encode s ∈ syntheticCodes)
    (p q : {v : V // v ∉ B.vertices}) (hs : B.syndrome = {p.val, q.val}) :
    ∀ D : Decomposition (B.pairRepairedPuncture p q),
      ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
        ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
          D.endpointCount w ≤ E.endpointCount w.val := by
  classical
  by_cases he : G.Adj p.val q.val
  · have hw := OriginalOrbits.original_witness (encode s) hcode
    rw [decode_encode] at hw
    obtain ⟨r, t, a, tail, added, hrecord⟩ := hw
    have hs' := B.threeAnchor_syndrome_pair A hcover s hrows r t hrecord.1
    have hpair := hs.symm.trans hs'
    have he' := (pair_adjacency p.val q.val (A r).val (A t).val hpair).mp he
    have heq := B.pairRepaired_eq_of_pair_eq p q (A r) (A t) hpair
    have lift : ∀ D : Decomposition (B.pairRepairedPuncture (A r) (A t)),
        ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
          ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
            D.endpointCount w ≤ E.endpointCount w.val := by
      intro D
      obtain ⟨E, _, hb, hends⟩ := B.originalThree_reconstruction_of_parity
        A s hrows hcover r t a tail added hrecord he' D
      exact ⟨E, hb, hends⟩
    rw [← heq] at lift
    exact lift
  · have hw := synthetic_witness (encode s) hcode
    rw [decode_encode] at hw
    obtain ⟨r, t, connector, added, hrecord⟩ := hw
    have hs' := B.threeAnchor_syndrome_pair A hcover s hrows r t hrecord.1
    have hpair := hs.symm.trans hs'
    have he' : ¬ G.Adj (A r).val (A t).val :=
      fun h => he ((pair_adjacency p.val q.val (A r).val (A t).val hpair).mpr h)
    have heq := B.pairRepaired_eq_of_pair_eq p q (A r) (A t) hpair
    have lift : ∀ D : Decomposition (B.pairRepairedPuncture (A r) (A t)),
        ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
          ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
            D.endpointCount w ≤ E.endpointCount w.val := by
      intro D
      obtain ⟨E, _, hb, hends⟩ := B.syntheticThree_reconstruction
        A s hrows r t connector added hrecord he' D
      exact ⟨E, hb, fun w _ => hends w⟩
    rw [← heq] at lift
    exact lift

/-- The actual component-sum budget closes ordinary and sharp whole-deletion cases. -/
theorem three_pair_encoded_lift (B : WholeBowtie G)
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcode : encode s ∈ syntheticCodes)
    (p q : {v : V // v ∉ B.vertices}) (hs : B.syndrome = {p.val, q.val})
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (D : Decomposition (B.pairRepairedPuncture p q))
    (hb : D.size ≤ ∑ K : (B.pairRepairedPuncture p q).ConnectedComponent,
      (Fintype.card K.supp + 1) / 2) :
    ∃ E : Decomposition G, E.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  rcases pair_three_credit_of_sum B p q hs hc hA D hb with htwo | ⟨hone, hC, _⟩
  · obtain ⟨E, hsize, hends⟩ := three_pair_two_lift B A s hcover hrows hcode p q hs D
    exact ⟨E, hsize.trans htwo, hends⟩
  · obtain ⟨E, hsize, hends⟩ :=
      three_pair_sharp_lift B A s hcover hrows hcode p q hs hC hc hA D
    exact ⟨E, hsize.trans hone, hends⟩

/-- Close the encoded whole-deletion pair branch for both designation choices. -/
theorem three_pair_encoded_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hA : (Bs 0).anchors.card ≤ 3)
    (A : Fin 3 ↪ {v : V // v ∉ (Bs 0).vertices}) (s : State)
    (hcover : ∀ v ∈ (Bs 0).anchors, ∃ j, (A j).val = v)
    (hrows : ∀ i v, v ∈ (Bs 0).row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (hcode : encode s ∈ syntheticCodes)
    (p q : {v : V // v ∉ (Bs 0).vertices}) (hpq : p ≠ q)
    (hs : (Bs 0).syndrome = {p.val, q.val}) (ih : PairComponentIH Bs p q) :
    Conclusion G d := by
  cases d with
  | none =>
    obtain ⟨D, hD⟩ := pair_induction_sum Bs h.1 p q hpq hs h ih
    obtain ⟨E, hE, _⟩ :=
      three_pair_encoded_lift (Bs 0) A s hcover hrows hcode p q hs hc hA D hD
    exact ⟨E, hE, by simp⟩
  | some y =>
    have hy := h.2.2.1 y (by simp)
    let y' : {v : V // v ∉ (Bs 0).vertices} := ⟨y, hy.2.2 0⟩
    obtain ⟨D, hD, hends⟩ := pair_induction_endpoint_sum Bs h.1 p q hpq hs y' h ih
    obtain ⟨E, hE, hr⟩ :=
      three_pair_encoded_lift (Bs 0) A s hcover hrows hcode p q hs hc hA D hD
    refine ⟨E, hE, ?_⟩
    intro z hz
    have heq : z = y := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    subst z
    exact hends.trans (hr y' hy.1)

end Gallai.Composition
