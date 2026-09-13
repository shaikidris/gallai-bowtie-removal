/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedRelabeling
import Gallai.Certificates.SizeTwoUniverse
import Gallai.Certificates.CompletedStarSymmetry

/-! # Actual graph normalization for size-two representatives

Relabel the existing bowtie and anchors before selecting its decomposition.
This preserves the graph itself and avoids imposing a symmetry choice on an
already selected carrier profile.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Translate inverse completed-star row actions to retained-core indices. -/
def sizeTwoCoreIndex : Fin 8 → Fin 8 := ![0,2,1,3,4,6,5,7]

/-- The reused relabelling cancels the coverage action on core rows. -/
theorem sizeTwoCoreIndex_cancel (k : Fin 8) (i : Fin 5) :
    coreRowMap k (ThreeAnchor.RetainedOrbits.coreOrder (sizeTwoCoreIndex k) i) = i := by
  revert k i
  decide

/-- Core relabelling preserves the actual incidence multiplicity at every vertex. -/
theorem retainedRelabel_columnCount (c : Fin 8) (v : V) :
    (B.retainedRelabel c).columnCount v = B.columnCount v := by
  unfold columnCount
  apply Finset.card_bij (fun i _ => ThreeAnchor.RetainedOrbits.coreOrder c i)
  · intro i hi
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,B.retainedRelabel_row] using hi
  · intro i hi j hj hij
    exact (ThreeAnchor.RetainedOrbits.coreOrder_bijective c).1 hij
  · intro j hj
    obtain ⟨i,rfl⟩ := (ThreeAnchor.RetainedOrbits.coreOrder_bijective c).2 j
    refine ⟨i,?_,rfl⟩
    simpa only [Finset.mem_filter,Finset.mem_univ,true_and,B.retainedRelabel_row] using hj

/-- The parity syndrome is independent of the core's internal naming. -/
theorem retainedRelabel_syndrome (c : Fin 8) :
    (B.retainedRelabel c).syndrome = B.syndrome := by
  ext v
  rw [(B.retainedRelabel c).mem_syndrome_iff_odd_column,
    B.retainedRelabel_columnCount, B.mem_syndrome_iff_odd_column]

/-- Anchor numbering on the same bowtie component after a coverage action. -/
noncomputable def sizeTwoRelabelNumbering (A : B.AnchorNumbering) (k : Fin 8)
    (σ : Equiv.Perm (Fin 4)) : (B.retainedRelabel (sizeTwoCoreIndex k)).AnchorNumbering :=
  Equiv.ofBijective
    (fun j => ⟨(A (σ j)).val, by
      rw [B.retainedRelabel_anchors]
      exact (A (σ j)).property⟩)
    ⟨by
      intro i j h
      have hv : (A (σ i)).val = (A (σ j)).val :=
        congrArg (fun v : {v // v ∈ (B.retainedRelabel (sizeTwoCoreIndex k)).anchors} => v.val) h
      exact σ.injective (A.injective (Subtype.ext hv)), by
      intro v
      have hv : v.val ∈ B.anchors := by
        simpa only [B.retainedRelabel_anchors] using v.property
      obtain ⟨j,hj⟩ := A.surjective ⟨v.val,hv⟩
      refine ⟨σ.symm j,Subtype.ext ?_⟩
      simpa only [Equiv.apply_symm_apply] using congrArg Subtype.val hj⟩

/-- Numbered anchor values are exactly the old values under the permutation. -/
theorem sizeTwoRelabelNumbering_val (A : B.AnchorNumbering) (k : Fin 8)
    (σ : Equiv.Perm (Fin 4)) (j : Fin 4) :
    (B.sizeTwoRelabelNumbering A k σ j).val = (A (σ j)).val := rfl

/-- Pair-preserving anchor actions retain the normalized auxiliary-star contract. -/
theorem sizeTwoRelabel_syndrome (A : B.AnchorNumbering) (k : Fin 8)
    (σ : Equiv.Perm (Fin 4)) (hσ : ∀ j : Fin 4, (σ j).val < 2 ↔ j.val < 2)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) :
    (B.retainedRelabel (sizeTwoCoreIndex k)).syndrome =
      {(B.sizeTwoRelabelNumbering A k σ 0).val,
       (B.sizeTwoRelabelNumbering A k σ 1).val} := by
  have hp : (σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0) := by
    have hall : ∀ σ : Equiv.Perm (Fin 4),
        (∀ j : Fin 4, (σ j).val < 2 ↔ j.val < 2) →
        ((σ 0 = 0 ∧ σ 1 = 1) ∨ (σ 0 = 1 ∧ σ 1 = 0)) := by decide
    exact hall σ hσ
  rw [B.retainedRelabel_syndrome,hSigma]
  simp only [B.sizeTwoRelabelNumbering_val]
  rcases hp with ⟨h0,h1⟩ | ⟨h0,h1⟩
  · rw [h0,h1]
  · ext v
    simp [h0,h1,or_comm]

private theorem mask_ext (a b : Fin 16)
    (h : ∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) : a = b := by
  have hh : ∀ a b : Fin 16,
      (∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) → a = b := by decide
  exact hh a b h

/-- A row-symmetry witness is realized as an exact representative state on G. -/
theorem sizeTwoRelabel_state (A : B.AnchorNumbering) (k : Fin 8)
    (σ : Equiv.Perm (Fin 4)) (s : State)
    (hs : transformedState k σ s = B.completedStarState A) :
    (B.retainedRelabel (sizeTwoCoreIndex k)).completedStarState
      (B.sizeTwoRelabelNumbering A k σ) = s := by
  funext i
  apply mask_ext
  intro j
  apply Bool.eq_iff_iff.mpr
  rw [(B.retainedRelabel (sizeTwoCoreIndex k)).completedStarState_bit,
    B.sizeTwoRelabelNumbering_val]
  change G.Adj (B.label (ThreeAnchor.RetainedOrbits.coreOrder (sizeTwoCoreIndex k) i))
    (A (σ j)).val ↔ _
  rw [← B.completedStarState_bit A _ (σ j), ← hs]
  simp only [transformedState, anchorState, coreState, permuteMask_bit,
    Equiv.symm_apply_apply, sizeTwoCoreIndex_cancel]

end Gallai.WholeBowtie
