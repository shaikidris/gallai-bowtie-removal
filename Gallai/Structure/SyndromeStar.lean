/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarAuxiliary
import Gallai.Structure.Syndrome

/-! # Retain exactly the syndrome spokes after private deletion -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem hub_not_mem_syndrome : B.label 0 ∉ B.syndrome :=
  fun h => B.hub_not_mem_anchors (B.syndrome_subset_anchors h)

/-- Original edges away from the hub are untouched; its neighbours become
exactly the actual syndrome. This adds or removes spokes as required. -/
def syndromeStar : SimpleGraph B.StarSurvivor where
  Adj u v :=
    (G.Adj u.val v.val ∧ u.val ≠ B.label 0 ∧ v.val ≠ B.label 0) ∨
    (u.val = B.label 0 ∧ v.val ∈ B.syndrome) ∨
    (v.val = B.label 0 ∧ u.val ∈ B.syndrome)
  symm.symm u v h := by
    rcases h with ⟨h,hu,hv⟩ | h | h
    · exact Or.inl ⟨h.symm,hv,hu⟩
    · exact Or.inr (Or.inr h)
    · exact Or.inr (Or.inl h)
  loopless.irrefl v := by
    rintro (⟨h,_,_⟩ | ⟨h,hs⟩ | ⟨h,hs⟩)
    · exact h.ne rfl
    · exact B.hub_not_mem_syndrome (h ▸ hs)
    · exact B.hub_not_mem_syndrome (h ▸ hs)

instance : DecidableRel B.syndromeStar.Adj := fun u v =>
  inferInstanceAs (Decidable (
    (G.Adj u.val v.val ∧ u.val ≠ B.label 0 ∧ v.val ≠ B.label 0) ∨
    (u.val = B.label 0 ∧ v.val ∈ B.syndrome) ∨
    (v.val = B.label 0 ∧ u.val ∈ B.syndrome)))

theorem syndromeStar_hub_adj (v : B.StarSurvivor) :
    B.syndromeStar.Adj B.completedHub v ↔ v.val ∈ B.syndrome := by
  change (_ ∧ B.label 0 ≠ B.label 0 ∧ _) ∨
    (B.label 0 = B.label 0 ∧ _) ∨ (_ ∧ B.label 0 ∈ B.syndrome) ↔ _
  simp [B.hub_not_mem_syndrome]

theorem syndromeStar_away_adj (u v : B.StarSurvivor)
    (hu : u.val ≠ B.label 0) (hv : v.val ≠ B.label 0) :
    B.syndromeStar.Adj u v ↔ G.Adj u.val v.val := by
  change (_ ∧ _ ∧ _) ∨ (_ ∧ _) ∨ (_ ∧ _) ↔ _
  simp [hu,hv]

/-- Neighbourhood equivalence gives the literal two-spoke degree, rather than
assuming an abstract carrier profile. -/
def syndromeStarNeighborEquiv : B.syndromeStar.neighborSet B.completedHub ≃ B.syndrome where
  toFun v := ⟨v.val.val, (B.syndromeStar_hub_adj v.val).mp v.property⟩
  invFun v := ⟨⟨v.val, B.anchor_survives (B.syndrome_subset_anchors v.property)⟩,
    (B.syndromeStar_hub_adj _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem syndromeStar_hub_degree :
    B.syndromeStar.degree B.completedHub = B.syndrome.card := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr B.syndromeStarNeighborEquiv).trans (Fintype.card_coe _)

theorem syndromeStar_hub_degree_two (hs : B.syndrome.card = 2) :
    B.syndromeStar.degree B.completedHub = 2 :=
  B.syndromeStar_hub_degree.trans hs

end Gallai.WholeBowtie
