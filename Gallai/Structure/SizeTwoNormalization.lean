/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SizeTwoRelabeling
import Gallai.Certificates.SizeTwoCoverage
import Gallai.Certificates.SizeTwoCatalogueStateAgreement

/-! # An arbitrary four-anchor size-two bowtie has an actual representative

First place the two syndrome anchors in positions zero and one. Then use the
exhaustive row coverage to relabel the existing bowtie, preserving G itself,
the hub and all five core vertices. No auxiliary decomposition is selected yet.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The normalized pair numbering exists for the actual syndrome, not merely
for row states already presented in normalized form. -/
theorem sizeTwo_pair_numbering (hA : B.anchors.card = 4) (hs : B.syndrome.card = 2) :
    ∃ A : B.AnchorNumbering, B.syndrome = {(A 0).val,(A 1).val} := by
  classical
  obtain ⟨u,v,huv,hS⟩ := Finset.card_eq_two.mp hs
  have hu : u ∈ B.anchors := B.syndrome_subset_anchors (by rw [hS]; simp)
  have hv : v ∈ B.anchors := B.syndrome_subset_anchors (by rw [hS]; simp)
  let A₀ := B.anchorNumbering hA
  let i := A₀.symm ⟨u,hu⟩
  let j := A₀.symm ⟨v,hv⟩
  have hij : i ≠ j := by
    intro he
    have he' := congrArg (fun k => (A₀ k).val) he
    apply huv
    simpa only [i,j,Equiv.apply_symm_apply] using he'
  have choosePair : ∀ i j : Fin 4, i ≠ j →
      ∃ σ : Equiv.Perm (Fin 4), σ 0 = i ∧ σ 1 = j := by decide
  obtain ⟨σ,hσ0,hσ1⟩ := choosePair i j hij
  let A : B.AnchorNumbering := σ.trans A₀
  have h0 : (A 0).val = u := by simp only [A,Equiv.trans_apply,hσ0,i,Equiv.apply_symm_apply]
  have h1 : (A 1).val = v := by simp only [A,Equiv.trans_apply,hσ1,j,Equiv.apply_symm_apply]
  exact ⟨A,by rw [h0,h1]; exact hS⟩

/-- Every actual four-anchor size-two state is represented on the SAME graph
by a whole bowtie with the same hub and vertex set. -/
theorem sizeTwo_normalized_representative (hA : B.anchors.card = 4)
    (hs : B.syndrome.card = 2) :
    ∃ R : WholeBowtie G, R.label 0 = B.label 0 ∧ R.vertices = B.vertices ∧
      ∃ A : R.AnchorNumbering, ∃ o : Fin 234,
        R.syndrome = {(A 0).val,(A 1).val} ∧ R.completedStarState A = Catalogue.state o := by
  obtain ⟨A,hSigma⟩ := B.sizeTwo_pair_numbering hA hs
  obtain ⟨o,k,σ,hσ,hrows⟩ := Coverage.pairState_covered _ (B.completedStarState_pair A hSigma)
  refine ⟨B.retainedRelabel (sizeTwoCoreIndex k),B.retainedRelabel_hub _,
    B.retainedRelabel_vertices _,B.sizeTwoRelabelNumbering A k σ,o,
    B.sizeTwoRelabel_syndrome A k σ hσ hSigma,?_⟩
  rw [Catalogue.state_eq_rows]
  exact B.sizeTwoRelabel_state A k σ (Catalogue.Rows.state o) hrows

end Gallai.WholeBowtie
