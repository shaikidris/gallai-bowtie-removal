/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.OptionalFamilyBudget

/-! # Append new paths after an optional carrier reconstruction

One absent old slot gives the one-unit credit. The exact endpoint formula
includes the old reconstructed family and the added paths on the same result.
-/
namespace Gallai.Decomposition
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V] {n r : ℕ}

/-- Append paths without assuming that any old slot disappeared. This is the
budget needed when a split/merge replaces two old carriers by two new ones. -/
theorem optional_append (F : Fin n → Option (NonemptyPath G))
    (R : Fin r → NonemptyPath G)
    (hc : ∀ e ∈ G.edgeSet,
      (∑ i, ((F i).map (fun P => P.walk.edges.count e)).getD 0) +
        (∑ i, (R i).walk.edges.count e) = 1) :
    ∃ D : Decomposition G, D.size ≤ n + r ∧
      ∀ v : V, D.endpointCount v =
        (∑ i, ((F i).map (fun P => (if P.start = v then 1 else 0) +
          (if P.finish = v then 1 else 0 : ℕ))).getD 0) +
        ∑ i, ((if (R i).start = v then 1 else 0) +
          (if (R i).finish = v then 1 else 0 : ℕ)) := by
  let U : Fin (n+r) → Option (NonemptyPath G) := fun i =>
    Sum.elim F (fun l => some (R l)) (finSumFinEquiv.symm i)
  have hsum (measure : NonemptyPath G → ℕ) :
      (∑ i, ((U i).map measure).getD 0) =
        (∑ i, ((F i).map measure).getD 0) + ∑ i, measure (R i) := by
    rw [(finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n+r)).symm.sum_comp
      (fun i => ((Sum.elim F (fun l => some (R l)) i).map measure).getD 0)]
    rw [Fintype.sum_sum_type]
    rfl
  have hcover : ∀ e ∈ G.edgeSet,
      (∑ i, ((U i).map (fun P => P.walk.edges.count e)).getD 0) = 1 := by
    intro e he
    rw [hsum]
    exact hc e he
  obtain ⟨D,_,hs,hend⟩ := of_optional_edge_counts U hcover
  refine ⟨D,hs,?_⟩
  intro v
  rw [hend,hsum]

/-- Complete an optional old family by adding checked nonempty paths. -/
theorem optional_append_one_credit (F : Fin n → Option (NonemptyPath G))
    (R : Fin r → NonemptyPath G) (k : Fin n) (hk : F k = none)
    (hc : ∀ e ∈ G.edgeSet,
      (∑ i, ((F i).map (fun P => P.walk.edges.count e)).getD 0) +
        (∑ i, (R i).walk.edges.count e) = 1) :
    ∃ D : Decomposition G, D.size + 1 ≤ n + r ∧
      ∀ v : V, D.endpointCount v =
        (∑ i, ((F i).map (fun P => (if P.start = v then 1 else 0) +
          (if P.finish = v then 1 else 0 : ℕ))).getD 0) +
        ∑ i, ((if (R i).start = v then 1 else 0) +
          (if (R i).finish = v then 1 else 0 : ℕ)) := by
  let U : Fin (n+r) → Option (NonemptyPath G) := fun i =>
    Sum.elim F (fun l => some (R l)) (finSumFinEquiv.symm i)
  have hu : U (finSumFinEquiv (Sum.inl k)) = none := by
    simp only [U,Equiv.symm_apply_apply,Sum.elim_inl,hk]
  have hsum (measure : NonemptyPath G → ℕ) :
      (∑ i, ((U i).map measure).getD 0) =
        (∑ i, ((F i).map measure).getD 0) + ∑ i, measure (R i) := by
    rw [(finSumFinEquiv : Fin n ⊕ Fin r ≃ Fin (n+r)).symm.sum_comp
      (fun i => ((Sum.elim F (fun l => some (R l)) i).map measure).getD 0)]
    rw [Fintype.sum_sum_type]
    rfl
  have hcover : ∀ e ∈ G.edgeSet,
      (∑ i, ((U i).map (fun P => P.walk.edges.count e)).getD 0) = 1 := by
    intro e he
    rw [hsum]
    exact hc e he
  obtain ⟨D,hs,hend⟩ := of_optional_edge_counts_one_credit U
    (finSumFinEquiv (Sum.inl k)) hu hcover
  refine ⟨D,hs,?_⟩
  intro v
  rw [hend,hsum]

end Gallai.Decomposition
