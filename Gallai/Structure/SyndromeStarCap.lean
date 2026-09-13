/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SyndromeStarParity

/-! # The syndrome-star auxiliary has only the designated E-degree exception -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem syndromeStar_hub_eDegree : eDegree B.syndromeStar B.completedHub = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨ha,he⟩ := (mem_evenNeighbors _ _).mp hv
  have hs := (B.syndromeStar_hub_adj v).mp ha
  exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor (B.syndrome_subset_anchors hs)))
    ((B.syndromeStar_even_iff v).mp he)

theorem syndromeStar_eDegree_le (v : B.StarSurvivor)
    (hv : v.val ≠ B.label 0) (he : Even (G.degree v.val)) :
    eDegree B.syndromeStar v ≤ eDegree G v.val := by
  have hs : (evenNeighbors B.syndromeStar v).map (Function.Embedding.subtype _) ⊆
      evenNeighbors G v.val := by
    intro w hw
    obtain ⟨q,hq,rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha,hqe⟩ := (mem_evenNeighbors _ _).mp hq
    apply (mem_evenNeighbors _ _).mpr
    refine ⟨?_, (B.syndromeStar_even_iff q).mp hqe⟩
    change (_ ∧ _ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) at ha
    rcases ha with ⟨ha,_,_⟩ | ⟨hx,_⟩ | ⟨_,hS⟩
    · exact ha
    · exact (hv hx).elim
    · exact ((Nat.not_even_iff_odd.mpr
        (B.odd_degree_anchor (B.syndrome_subset_anchors hS))) he).elim
  simpa only [Finset.card_map, eDegree] using Finset.card_le_card hs

theorem syndromeStar_cap (y : B.StarSurvivor)
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∀ v, Even (B.syndromeStar.degree v) → v ≠ y → eDegree B.syndromeStar v ≤ 3 := by
  intro v he hny
  by_cases hx : v.val = B.label 0
  · have hv : v = B.completedHub := Subtype.ext hx
    subst v
    rw [B.syndromeStar_hub_eDegree]
    omega
  · have heG := (B.syndromeStar_even_iff v).mp he
    exact (B.syndromeStar_eDegree_le v hx heG).trans
      (hcap v.val heG hx (fun h => hny (Subtype.ext h)))

end Gallai.WholeBowtie
