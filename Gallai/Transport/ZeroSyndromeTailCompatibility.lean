/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeWords

/-! # Accepted tail rules imply actual carrier compatibility

This discharges support-avoidance and same-carrier disjointness in the
original graph, with the actual normalized component and carrier labels.
-/

namespace Gallai.WholeBowtie

open Certificate Certificate.CompletedStar Certificate.ZeroSyndrome
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Every interpreted post-attachment symbol meets the actual freshness rule. -/
theorem zero_tail_vertices_allowed (A : B.AnchorNumbering) (tails : Tails)
    (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (i : Fin 4) (hi : tails i ≠ []) :
    ∀ v ∈ (tails i).tail.map (B.completedLabel A), v ∈ B.vertices ∨
      ∃ b : B.anchors, B.anchorComponent (A i) ≠ B.anchorComponent b ∧ v = b.val := by
  intro v hv
  obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hv
  rcases ((h.2 i).resolve_left hi).2 w hw with hf | ⟨j, hj, rfl⟩
  · exact Or.inl (B.completedLabel_fresh A w (List.mem_toFinset.mpr hf))
  · refine Or.inr ⟨A j, ?_, B.completedLabel_anchor A j⟩
    intro he
    exact hj ((normalize_eq_iff (fun j => B.anchorComponent (A j)) j i).mpr he.symm)

/-- A realized nonempty tail avoids its chosen old carrier after attachment. -/
theorem realizeZeroTail_avoids (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a)
    (tails : Tails) (added : List (List Star.Vertex))
    (h : RecordCore (B.completedStarState A) (B.zeroComponentLabels A) tails added)
    (i : Fin 4) (hi : tails i ≠ []) :
    (B.realizeZeroTail A (B.zeroComponentLabels A) tails added h i hi).walk.support.tail.Disjoint
      (B.punctureCarrier (D.path (f (A i)))).walk.support := by
  change (B.realizeOriginalMember A (localWords tails added) h.1 (tails i)
    (zero_tail_mem tails added i hi)).walk.support.tail.Disjoint _
  rw [B.realizeOriginalMember_support, ← List.map_tail]
  exact B.allowed_tail_avoids_puncture_carrier D f hf (A i) _
    (B.zero_tail_vertices_allowed A tails added h i hi)

/-- Distinct tails assigned to the same actual carrier remain mutually
disjoint after their attachment points, as the two-credit record requires. -/
theorem two_credit_tail_disjoint (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size) (tails : Tails) (added : List (List Star.Vertex))
    (h : TwoCreditAccepted (B.completedStarState A) (B.zeroComponentLabels A)
      (B.zeroCarrierLabels A D f) tails added)
    (i j : Fin 4) (hij : i ≠ j) (howner : f (A i) = f (A j)) :
    ((tails i).tail.map (B.completedLabel A)).Disjoint
      ((tails j).tail.map (B.completedLabel A)) := by
  apply List.disjoint_map (B.completedLabel_injective A)
  exact h.2.2.2 i j hij ((normalize_eq_iff (fun j => f (A j)) i j).mpr howner)

end Gallai.WholeBowtie
