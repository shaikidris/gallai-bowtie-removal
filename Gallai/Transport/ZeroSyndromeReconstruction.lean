/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeTotalCounts
import Gallai.Transport.ZeroSyndromeBoundary

/-! # Accepted zero-syndrome records yield actual global decompositions -/

namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : B.AnchorNumbering) (D : Decomposition B.puncture)
variable (f : B.anchors → Fin D.size)
variable (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
  (D.path (f a)).finish = B.anchorPunctureVertex a)
variable (tails : Tails) (added : List (List Star.Vertex))
variable (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
  (B.zeroCarrierLabels A D f) tails added)

/-- Every original graph edge has multiplicity exactly one in the candidate. -/
theorem zeroCandidateFamily_edge_count (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i : Fin D.size ⊕ Fin added.length,
      (B.zeroCandidateFamily A D f hf tails added h i).walk.edges.count e) = 1 := by
  rw [B.zeroCandidateFamily_total_count A D f hf tails added h]
  rcases B.zero_original_edge_cases A e he with ⟨q, hq, rfl⟩ | ⟨q, hq, rfl⟩
  · rw [B.zero_puncture_count D q hq, B.zero_local_count_puncture A q]
  · rw [B.zero_puncture_count_target A D q hq, B.zero_local_count_target A q hq]

/-- Restore the entire original graph, with no assumed global coverage premise. -/
noncomputable def zeroReconstruction : Decomposition G :=
  Decomposition.ofEdgeCounts
    (fun i : Fin (D.size + added.length) =>
      B.zeroCandidateFamily A D f hf tails added h (finSumFinEquiv.symm i))
    (by
      intro e he
      exact ((finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
        Fin (D.size + added.length)).symm.sum_comp
        (fun i => (B.zeroCandidateFamily A D f hf tails added h i).walk.edges.count e)).trans
        (B.zeroCandidateFamily_edge_count A D f hf tails added h e he))

/-- The actual decomposition, not just the candidate index set, has exact cost. -/
theorem zeroReconstruction_size :
    (B.zeroReconstruction A D f hf tails added h).size = D.size + added.length := rfl

theorem zeroReconstruction_budget :
    (B.zeroReconstruction A D f hf tails added h).size ≤ D.size + 2 :=
  Nat.add_le_add_left h.2.2.1 _

/-- The actual reconstruction retains every designated even outside reserve. -/
theorem zeroReconstruction_endpoint_reserve (w : {v // v ∉ B.vertices})
    (hw : Even (G.degree w.val)) :
    D.endpointCount w ≤ (B.zeroReconstruction A D f hf tails added h).endpointCount w.val := by
  change D.endpointCount w ≤ ∑ i : Fin (D.size + added.length),
    ((if (B.zeroCandidateFamily A D f hf tails added h (finSumFinEquiv.symm i)).start = w.val
      then 1 else 0) +
    (if (B.zeroCandidateFamily A D f hf tails added h (finSumFinEquiv.symm i)).finish = w.val
      then 1 else 0 : ℕ))
  rw [(finSumFinEquiv : Fin D.size ⊕ Fin added.length ≃
    Fin (D.size + added.length)).symm.sum_comp
    (fun i => (if (B.zeroCandidateFamily A D f hf tails added h i).start = w.val
      then 1 else 0) +
      (if (B.zeroCandidateFamily A D f hf tails added h i).finish = w.val then 1 else 0 : ℕ))]
  exact B.zeroCandidateFamily_endpoint_reserve A D f hf tails added h w hw

include hf in
/-- One-credit acceptance uses the same actual reconstruction but retains the
stronger original count bound; it does not spend an unnecessary second path. -/
theorem zeroOneCredit_reconstruction
    (hOne : OneCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (w : {v // v ∉ B.vertices}) (hw : Even (G.degree w.val)) :
    ∃ P : Decomposition G, P.size ≤ D.size + 1 ∧ D.endpointCount w ≤ P.endpointCount w.val := by
  let ht := hOne.toTwo (B.zero_interface_mem A D f hf)
  refine ⟨B.zeroReconstruction A D f hf tails added ht, ?_,
    B.zeroReconstruction_endpoint_reserve A D f hf tails added ht w hw⟩
  rw [B.zeroReconstruction_size]
  exact Nat.add_le_add_left hOne.2.2.1 _

end Gallai.WholeBowtie
