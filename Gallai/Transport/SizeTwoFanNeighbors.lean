/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFanInitial

/-! # Actual core neighbourhoods before the three Fan restorations -/
namespace Gallai.WholeBowtie

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Only the retained hub can be a core endpoint of an auxiliary edge. -/
theorem sizeTwoFan_aux_core_adj (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) (i : Fin 5) (v : V) :
    B.sizeTwoFanAux.Adj (B.label i) v ↔
      i = 0 ∧ (v = (A 0).val ∨ v = (A 1).val) := by
  rw [sizeTwoFanAux, SimpleGraph.map_adj]
  constructor
  · rintro ⟨u,w,ha,hu,hw⟩
    change u.val = B.label i at hu
    change w.val = v at hw
    have huB : u.val ∈ B.vertices := by
      rw [hu]
      exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,rfl⟩
    have hi : i = 0 := B.label.injective
      (hu.symm.trans (B.survivor_mem_vertices u huB))
    subst i
    have hu' : u = B.completedHub := Subtype.ext hu
    subst u
    have hs := (B.syndromeStar_hub_adj w).mp ha
    simpa [hSigma,hw] using And.intro (rfl : (0 : Fin 5) = 0) hs
  · rintro ⟨rfl,hv⟩
    let w : B.StarSurvivor := ⟨v, B.anchor_survives (by
      rcases hv with rfl | rfl
      · exact (A 0).property
      · exact (A 1).property)⟩
    refine ⟨B.completedHub,w,?_,rfl,rfl⟩
    apply (B.syndromeStar_hub_adj w).mpr
    simpa [hSigma,w] using hv

/-- The initial union has exactly its finite local neighbours at every core
vertex, despite unrestricted edges between old external vertices. -/
theorem sizeTwoFan_initial_core_adj (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) (i : Fin 5) (v : V) :
    (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj (B.label i) v ↔
      ∃ t : Star.Vertex,
        s(CompletedStar.core i,t) ∈ SizeTwo.Fan.retainedEdges ∪ SizeTwo.Fan.initialEdges ∧
        B.completedLabel A t = v := by
  have hret (t : Star.Vertex) :
      s(CompletedStar.core i,t) ∈ SizeTwo.Fan.retainedEdges ↔
        i = 0 ∧ (t = .p ∨ t = .q) := by
    fin_cases i <;> cases t <;> decide
  constructor
  · intro ha
    rcases ha with ha | ha
    · obtain ⟨rfl,hv⟩ := (B.sizeTwoFan_aux_core_adj A hSigma i v).mp ha
      rcases hv with rfl | rfl
      · exact ⟨.p,Finset.mem_union_left _ (by decide),rfl⟩
      · exact ⟨.q,Finset.mem_union_left _ (by decide),rfl⟩
    · rw [sizeTwoFanAdded, SimpleGraph.map_adj] at ha
      obtain ⟨u,t,ha,hu,ht⟩ := ha
      have hu' : u = CompletedStar.core i := B.completedLabel_injective A
        (hu.trans (B.completedLabel_core A i).symm)
      subst u
      have he := (SizeTwo.Fan.initialGraph_edges s(CompletedStar.core i,t)).mpr ha
      exact ⟨t,Finset.mem_union_right _ he,ht⟩
  · rintro ⟨t,ht,rfl⟩
    rcases Finset.mem_union.mp ht with ht | ht
    · obtain ⟨hi,hpair⟩ := (hret t).mp ht
      rw [hi]
      apply Or.inl
      apply (B.sizeTwoFan_aux_core_adj A hSigma 0 _).mpr
      rcases hpair with hp | hq
      · exact ⟨rfl,Or.inl (congrArg (B.completedLabel A) hp)⟩
      · exact ⟨rfl,Or.inr (congrArg (B.completedLabel A) hq)⟩
    · apply Or.inr
      rw [sizeTwoFanAdded, SimpleGraph.map_adj]
      exact ⟨CompletedStar.core i,t,(SizeTwo.Fan.initialGraph_edges _).mp ht,
        B.completedLabel_core A i,rfl⟩

theorem sizeTwoFan_initial_hub_adj (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) (v : V) :
    (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj (B.label 0) v ↔
      ∃ t ∈ ({.a,.c,.d,.p,.q,.r} : Finset Star.Vertex), B.completedLabel A t = v := by
  rw [B.sizeTwoFan_initial_core_adj A hSigma]
  simp only [CompletedStar.core, Matrix.cons_val_zero, SizeTwo.Fan.initial_hub_neighbors]

theorem sizeTwoFan_initial_b_adj (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) (v : V) :
    (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj (B.label 2) v ↔
      ∃ t ∈ ({.a,.r} : Finset Star.Vertex), B.completedLabel A t = v := by
  rw [B.sizeTwoFan_initial_core_adj A hSigma]
  change (∃ t, s(Star.Vertex.b,t) ∈ _ ∧ _) ↔ _
  simp only [SizeTwo.Fan.initial_b_neighbors]

end Gallai.WholeBowtie
