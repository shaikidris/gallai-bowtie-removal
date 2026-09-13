/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeFamily

/-! # Exact candidate edge counts and preserved outside endpoints -/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem zeroAddedPath_edges (A : B.AnchorNumbering) (tails : Tails)
    (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (i : Fin added.length) :
    (B.zeroAddedPath A tails added h i).walk.edges =
      (wordEdges added[i]).map (Sym2.map (B.completedLabel A)) :=
  B.realizeOriginalMember_edges A _ h.1 _ _

/-- Each old path contributes its unchanged puncture edges and both assigned
tail words exactly once. Reversal of the start tail does not change counts. -/
theorem zeroRestoredOld_edge_count (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added) (k : Fin D.size) (e : Sym2 V) :
    (B.zeroRestoredOld A D f hf tails added h k).walk.edges.count e =
      (B.punctureCarrier (D.path k)).walk.edges.count e +
      ((wordEdges (B.zeroAssignedWord A D f tails k (D.path k).start.val)).map
        (Sym2.map (B.completedLabel A))).count e +
      ((wordEdges (B.zeroAssignedWord A D f tails k (D.path k).finish.val)).map
        (Sym2.map (B.completedLabel A))).count e := by
  unfold zeroRestoredOld
  rw [NonemptyPath.endpointTails_edges, SimpleGraph.Walk.edges_reverse]
  simp only [List.count_append, List.count_reverse, B.zeroAssignedTail_edges]
  simp only [show (B.punctureCarrier (D.path k)).start = (D.path k).start.val from rfl,
    show (B.punctureCarrier (D.path k)).finish = (D.path k).finish.val from rfl]
  omega

/-- Endpoints outside the nine local labels are unchanged by an assigned tail. -/
theorem zeroAssignedTail_endpoint_iff (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (k : Fin D.size) (u w : V) (hw : ∀ t, B.completedLabel A t ≠ w) :
    (B.zeroAssignedTail A D f tails added h k u).1 = w ↔ u = w := by
  classical
  by_cases he : ∃ j, B.ZeroTailAt A D f tails k u j
  · have hj := Classical.choose_spec he
    have hu : u ≠ w := by
      rw [← hj.2.1, ← B.completedLabel_anchor A (Classical.choose he)]
      exact hw _
    rw [B.zeroAssignedTail_pos A D f tails added h k u he]
    have hn : (B.realizeZeroTail A (B.zeroComponentLabels A) tails added h
        (Classical.choose he) hj.2.2).finish ≠ w := by
      intro heq
      have hm := (B.realizeZeroTail A (B.zeroComponentLabels A) tails added h
        (Classical.choose he) hj.2.2).walk.end_mem_support
      change _ ∈ (B.realizeOriginalMember A _ h.1 _ _).walk.support at hm
      rw [B.realizeOriginalMember_support] at hm
      obtain ⟨t, _, ht⟩ := List.mem_map.mp hm
      exact hw t (ht.trans heq)
    exact iff_of_false hn hu
  · rw [B.zeroAssignedTail_neg A D f tails added h k u he]

/-- Outside the local labels, each reconstructed old path retains exactly
its original endpoint contribution. -/
theorem zeroRestoredOld_endpoint_contribution (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added)
    (k : Fin D.size) (w : {v // v ∉ B.vertices})
    (hw : ∀ t, B.completedLabel A t ≠ w.val) :
    (if (B.zeroRestoredOld A D f hf tails added h k).start = w.val then 1 else 0) +
      (if (B.zeroRestoredOld A D f hf tails added h k).finish = w.val then 1 else 0) =
    (if (D.path k).start = w then 1 else 0) +
      (if (D.path k).finish = w then 1 else 0 : ℕ) := by
  unfold zeroRestoredOld
  rw [NonemptyPath.endpointTails_endpoint_contribution _ _ _ _ _ _ _ _ _
    (B.zeroAssignedTail_endpoint_iff A D f tails added h.2.1 k _ w.val hw)
    (B.zeroAssignedTail_endpoint_iff A D f tails added h.2.1 k _ w.val hw)]
  change (if (D.path k).start.val = w.val then 1 else 0) +
    (if (D.path k).finish.val = w.val then 1 else 0) = _
  simp only [Subtype.val_inj]

/-- An even retained vertex cannot be one of the odd external anchors, so
the designated endpoint theorem's actual vertex meets the local exclusion. -/
theorem zero_even_outside_labels (A : B.AnchorNumbering)
    (w : {v // v ∉ B.vertices}) (hw : Even (G.degree w.val)) :
    ∀ t, B.completedLabel A t ≠ w.val := by
  have hc (i : Fin 5) : B.label i ≠ w.val := by
    intro hi
    apply w.property
    exact hi ▸ Finset.mem_map.mpr ⟨i, Finset.mem_univ i, rfl⟩
  have ha (j : Fin 4) : (A j).val ≠ w.val := by
    intro hj
    have ho := B.odd_degree_anchor (A j).property
    rw [hj] at ho
    exact Nat.not_even_iff_odd.mpr ho hw
  intro t
  cases t <;> first | exact hc _ | exact ha _

/-- The candidate family retains the actual even vertex's endpoint reserve.
Added paths cannot reduce it; no endpoint-selection assumption is hidden. -/
theorem zeroCandidateFamily_endpoint_reserve (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added)
    (w : {v // v ∉ B.vertices}) (hw : Even (G.degree w.val)) :
    D.endpointCount w ≤ ∑ i : Fin D.size ⊕ Fin added.length,
      ((if (B.zeroCandidateFamily A D f hf tails added h i).start = w.val then 1 else 0) +
        (if (B.zeroCandidateFamily A D f hf tails added h i).finish = w.val then 1 else 0 : ℕ)) := by
  rw [Fintype.sum_sum_type]
  have he : (∑ i : Fin D.size,
      ((if (B.zeroRestoredOld A D f hf tails added h i).start = w.val then 1 else 0) +
        (if (B.zeroRestoredOld A D f hf tails added h i).finish = w.val then 1 else 0 : ℕ))) =
      D.endpointCount w := Finset.sum_congr rfl (fun i _ =>
        B.zeroRestoredOld_endpoint_contribution A D f hf tails added h i w
          (B.zero_even_outside_labels A w hw))
  change D.endpointCount w ≤ (∑ i : Fin D.size,
      ((if (B.zeroRestoredOld A D f hf tails added h i).start = w.val then 1 else 0) +
        (if (B.zeroRestoredOld A D f hf tails added h i).finish = w.val then 1 else 0 : ℕ))) + _
  rw [he]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
