/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFanGraph
import Gallai.Certificates.SizeTwoExceptionClassification

/-! # Complete graph-level consumer for the size-two Fan exception -/
namespace Gallai.WholeBowtie

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Even outside vertices occur on neither initial added path. -/
theorem sizeTwoFan_added_even_outside (A : B.AnchorNumbering)
    (w : B.StarSurvivor) (hw : w.val ∉ B.vertices) (hEven : Even (G.degree w.val)) :
    (B.sizeTwoFanAddedDecomposition A).endpointCount w.val = 0 := by
  have hcore (i : Fin 5) : B.label i ≠ w.val := by
    intro hh
    apply hw
    exact Finset.mem_map.mpr ⟨i,Finset.mem_univ _,hh⟩
  have hanchor (j : Fin 4) : (A j).val ≠ w.val := by
    intro hh
    have he : Even (G.degree (A j).val) := hh ▸ hEven
    exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (A j).property) he
  have hlabel (t : Star.Vertex) : B.completedLabel A t ≠ w.val := by
    cases t
    · exact hcore 0
    · exact hcore 1
    · exact hcore 2
    · exact hcore 3
    · exact hcore 4
    · exact hanchor 0
    · exact hanchor 1
    · exact hanchor 2
    · exact hanchor 3
  apply SizeTwo.Fan.initialDecomposition.map_endpointCount_of_notMem_range
    (B.sizeTwoFanLabel A) w.val
  rintro ⟨t,ht⟩
  exact hlabel t ht

/-- The Fan state reconstructs G from every auxiliary decomposition with
exactly two extra paths and preserves all even outside endpoint counts. -/
theorem sizeTwoFan_reconstruction (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) :
    ∃ P : Decomposition G, P.size = D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        P.endpointCount w.val = D.endpointCount w := by
  classical
  obtain ⟨P,hsize,hbalance⟩ := B.sizeTwoFan_restored_decomposition A hstate hSigma D
  have hresult : ∃ P : Decomposition (B.sizeTwoFanRestored A), P.size = D.size + 2 ∧
      ∀ w : B.StarSurvivor, w.val ∉ B.vertices → Even (G.degree w.val) →
        P.endpointCount w.val = D.endpointCount w := by
    refine ⟨P,hsize,?_⟩
    intro w hw hEven
    have hb : B.label 2 ≠ w.val := fun hh => hw
      (Finset.mem_map.mpr ⟨2,Finset.mem_univ _,hh⟩)
    have hs : (A 3).val ≠ w.val := by
      intro hh
      have he : Even (G.degree (A 3).val) := hh ▸ hEven
      exact Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (A 3).property) he
    have hz := B.sizeTwoFan_added_even_outside A w hw hEven
    have he := hbalance w.val
    simp only [hb,hs,if_false,Nat.add_zero,hz] at he
    exact he.trans (D.map_endpointCount (Function.Embedding.subtype _) w)
  rw [B.sizeTwoFan_restored_eq_original A hstate hSigma] at hresult
  exact hresult

/-- The finite exceptional tag supplies its exact state, and two available
credits discharge the designated endpoint conclusion on the original graph. -/
theorem sizeTwo_catalogue_fan_endpoint (A : B.AnchorNumbering)
    (o : Fin 234) (i : Fin 13)
    (hstate : B.completedStarState A = SizeTwo.Catalogue.state o)
    (hkind : SizeTwo.Catalogue.kind o i = .fan)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (budget : ℕ) (hbudget : D.size + 2 ≤ budget)
    (y : B.StarSurvivor) (hyout : y.val ∉ B.vertices) (hy : Even (G.degree y.val))
    (hyD : 2 ≤ D.endpointCount y) :
    ∃ P : Decomposition G, P.size ≤ budget ∧ 2 ≤ P.endpointCount y.val := by
  have hrow : B.completedStarState A = SizeTwo.Fan.state :=
    hstate.trans (SizeTwo.Catalogue.fan_state o i hkind)
  obtain ⟨P,hsize,hend⟩ := B.sizeTwoFan_reconstruction A hrow hSigma D
  exact ⟨P,hsize ▸ hbudget,(hend y hyout hy).symm ▸ hyD⟩

end Gallai.WholeBowtie
