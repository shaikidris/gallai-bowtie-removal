/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromePartitions
import Gallai.Structure.CompletedStarRows
import Gallai.Transport.ZeroSyndromeInterface

/-! # Actual zero-syndrome decompositions realize legal finite interfaces

The finite component labels are obtained from actual connected components;
the carrier labels come from actual endpoint choices. No enumeration of
small ambient graphs or favorable interface assumption is involved.
-/

namespace Gallai.WholeBowtie

open Certificate.ZeroSyndrome
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Finite labels for the actual components meeting the four anchors. -/
noncomputable def zeroComponentLabels (A : B.AnchorNumbering) : Labels :=
  normalize (fun j => B.anchorComponent (A j))

/-- Finite labels for the actual chosen carrier indices. -/
noncomputable def zeroCarrierLabels (A : B.AnchorNumbering)
    (D : Decomposition B.puncture) (f : B.anchors → Fin D.size) : Labels :=
  normalize (fun j => f (A j))

/-- Actual endpoint carriers satisfy precisely the finite pair/refinement rule. -/
theorem zero_labels_compatible (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a) :
    Compatible (B.zeroComponentLabels A) (B.zeroCarrierLabels A D f) := by
  classical
  constructor
  · intro i
    have hs : (Finset.univ.filter (fun j => B.zeroCarrierLabels A D f j = i)).map
        A.toEmbedding ⊆ Finset.univ.filter (fun a => f a = f (A i)) := by
      intro a ha
      obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp ha
      have hi := (Finset.mem_filter.mp hj).2
      have he := normalize_spec (fun j => f (A j)) j
      change f (A (B.zeroCarrierLabels A D f j)) = f (A j) at he
      rw [hi] at he
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, he.symm⟩
    have hc := Finset.card_le_card hs
    simp only [Finset.card_map] at hc
    exact hc.trans (B.anchor_carrier_fiber_le_two D f hf _)
  · intro i j hij
    apply (normalize_eq_iff (fun j => B.anchorComponent (A j)) i j).mpr
    exact B.same_carrier_same_component D f hf _ _
      ((normalize_eq_iff (fun j => f (A j)) i j).mp hij)

/-- The actual two-credit interface belongs to the complete finite universe. -/
theorem zero_interface_mem (A : B.AnchorNumbering) (D : Decomposition B.puncture)
    (f : B.anchors → Fin D.size)
    (hf : ∀ a, (D.path (f a)).start = B.anchorPunctureVertex a ∨
      (D.path (f a)).finish = B.anchorPunctureVertex a) :
    (B.zeroComponentLabels A, B.zeroCarrierLabels A D f) ∈ interfaces :=
  (mem_interfaces _ _).mpr ⟨normalize_normalized _, normalize_normalized _,
    B.zero_labels_compatible A D f hf⟩

/-- Normalized component labels still represent every actual puncture component. -/
theorem zero_component_count_le_labels (A : B.AnchorNumbering) (hc : G.Connected) :
    Fintype.card B.puncture.ConnectedComponent ≤
      #(Finset.univ.image (B.zeroComponentLabels A)) := by
  classical
  let labels := Finset.univ.image (B.zeroComponentLabels A)
  let g : labels → B.puncture.ConnectedComponent := fun j => B.anchorComponent (A j.val)
  have hg : Function.Surjective g := by
    intro C
    obtain ⟨a, ha⟩ := B.anchorComponent_surjective hc C
    obtain ⟨j, rfl⟩ := A.surjective a
    refine ⟨⟨B.zeroComponentLabels A j, Finset.mem_image.mpr ⟨j, by simp, rfl⟩⟩, ?_⟩
    exact (normalize_spec (fun j => B.anchorComponent (A j)) j).trans ha
  simpa only [Fintype.card_coe] using Fintype.card_le_of_surjective g hg

/-- The actual one-credit separation resource enters the cheaper finite universe. -/
theorem zero_separated_mem (A : B.AnchorNumbering) (hc : G.Connected)
    (hthree : 3 ≤ Fintype.card B.puncture.ConnectedComponent) :
    B.zeroComponentLabels A ∈ separatedPartitions := by
  classical
  exact Finset.mem_filter.mpr ⟨Finset.mem_filter.mpr
    ⟨Finset.mem_univ _, normalize_normalized _⟩,
    hthree.trans (B.zero_component_count_le_labels A hc)⟩

end Gallai.WholeBowtie
