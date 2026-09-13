/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.OptionalFamily

/-! # The path-count credit supplied by a merged-away slot

Rich reconstruction retains an old index set, assigns none to a merged-away
carrier and appends at most two new paths. One known absent slot supplies the
required one-unit improvement over the naive index-set cardinality.
-/
namespace Gallai
variable {α : Type*} {n : ℕ}

/-- A specified absent slot saves at least one entry. Other absent slots
may improve the bound further and do not require separate treatment. -/
theorem presentEntries_one_credit (F : Fin n → Option α) (k : Fin n) (hk : F k = none) :
    (presentEntries F).length + 1 ≤ n := by
  classical
  let w : Fin n → ℕ := fun i => ((F i).map (fun _ => (1 : ℕ))).getD 0
  have hw (i : Fin n) : w i + (if i = k then 1 else 0) ≤ 1 := by
    by_cases hi : i = k
    · subst i
      simp [w,hk]
    · cases he : F i <;> simp [w,hi,he]
  calc
    (presentEntries F).length + 1 = ∑ i, (w i + if i = k then 1 else 0) := by
      rw [presentEntries_length,Finset.sum_add_distrib]
      simp only [Finset.sum_ite_eq',Finset.mem_univ,if_true]
      rfl
    _ ≤ ∑ _i : Fin n, (1 : ℕ) := Finset.sum_le_sum (fun i _ => hw i)
    _ = n := by simp

namespace Decomposition
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- Build a decomposition with the merged-carrier credit and the same exact
endpoint vector, once the reconstructed optional family covers the edges. -/
theorem of_optional_edge_counts_one_credit (F : Fin n → Option (NonemptyPath G))
    (k : Fin n) (hk : F k = none)
    (hc : ∀ e ∈ G.edgeSet,
      (∑ i, ((F i).map (fun P => P.walk.edges.count e)).getD 0) = 1) :
    ∃ D : Decomposition G, D.size + 1 ≤ n ∧
      ∀ v : V, D.endpointCount v =
        ∑ i, ((F i).map (fun P => (if P.start = v then 1 else 0) +
          (if P.finish = v then 1 else 0 : ℕ))).getD 0 := by
  obtain ⟨D,hs,_,hend⟩ := of_optional_edge_counts F hc
  refine ⟨D,?_,hend⟩
  rw [← presentEntries_length] at hs
  rw [hs]
  exact presentEntries_one_credit F k hk

end Decomposition
end Gallai
