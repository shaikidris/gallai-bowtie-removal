/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.EdgeCounts
import Mathlib.Data.List.OfFn
import Mathlib.Algebra.BigOperators.Group.List.Basic
import Mathlib.Algebra.BigOperators.Fin

/-! # Assemble a finite family of optional nonempty paths

Absent slots are discarded. Exact sums transfer for edge multiplicities,
endpoints and the number of present carriers. This is the assembly interface
for merging schemes that also allow an empty trimmed prefix to disappear.
-/
namespace Gallai
variable {α : Type*} {n : ℕ}

/-- Enumerate present entries only, keeping their original order. -/
def presentEntries (F : Fin n → Option α) : List α := (List.ofFn F).filterMap id

/-- Filtering absent entries preserves any natural-valued measure with zero
contribution assigned to an absent slot. -/
theorem sum_presentEntries (F : Fin n → Option α) (measure : α → ℕ) :
    (∑ i : Fin (presentEntries F).length, measure ((presentEntries F)[i.val])) =
      ∑ i, ((F i).map measure).getD 0 := by
  have hf (l : List (Option α)) : ((l.filterMap id).map measure).sum =
      (l.map (fun o => (o.map measure).getD 0)).sum := by
    induction l with
    | nil => rfl
    | cons o l ih =>
      cases o <;> simp only [List.filterMap_cons,id_eq,List.map_cons,
        Option.map_none,Option.map_some,Option.getD_none,Option.getD_some,
        List.sum_cons,Nat.zero_add,Nat.add_right_inj] <;> simpa only [id_eq] using ih
  rw [← List.sum_ofFn,List.ofFn_getElem_eq_map]
  rw [presentEntries,hf,List.map_ofFn,List.sum_ofFn]
  rfl

/-- The exact count of retained entries is the sum of their presence weights. -/
theorem presentEntries_length (F : Fin n → Option α) :
    (presentEntries F).length = ∑ i, ((F i).map (fun _ => (1 : ℕ))).getD 0 := by
  simpa using sum_presentEntries F (fun _ => (1 : ℕ))

/-- Dropping absent slots never increases the size of the family. -/
theorem presentEntries_length_le (F : Fin n → Option α) :
    (presentEntries F).length ≤ n := by
  simpa only [presentEntries,List.length_ofFn] using List.length_filterMap_le id (List.ofFn F)

namespace Decomposition
variable {V : Type*} {G : SimpleGraph V} [DecidableEq V]

/-- An optional family with exact edge coverage supplies a genuine decomposition,
with exact cardinality and endpoint sums on that same decomposition. -/
theorem of_optional_edge_counts (F : Fin n → Option (NonemptyPath G))
    (hc : ∀ e ∈ G.edgeSet,
      (∑ i, ((F i).map (fun P => P.walk.edges.count e)).getD 0) = 1) :
    ∃ D : Decomposition G,
      D.size = ∑ i, ((F i).map (fun _ => (1 : ℕ))).getD 0 ∧ D.size ≤ n ∧
      ∀ v : V, D.endpointCount v =
        ∑ i, ((F i).map (fun P => (if P.start = v then 1 else 0) +
          (if P.finish = v then 1 else 0 : ℕ))).getD 0 := by
  let paths : Fin (presentEntries F).length → NonemptyPath G := fun i => (presentEntries F)[i.val]
  have hcount : ∀ e ∈ G.edgeSet, (∑ i, (paths i).walk.edges.count e) = 1 := by
    intro e he
    rw [show (∑ i, (paths i).walk.edges.count e) =
      ∑ i, ((F i).map (fun P => P.walk.edges.count e)).getD 0 from
        sum_presentEntries F (fun P => P.walk.edges.count e)]
    exact hc e he
  refine ⟨ofEdgeCounts paths hcount,presentEntries_length F,presentEntries_length_le F,?_⟩
  intro v
  exact sum_presentEntries F (fun P => (if P.start = v then 1 else 0) +
    (if P.finish = v then 1 else 0 : ℕ))

end Decomposition
end Gallai
