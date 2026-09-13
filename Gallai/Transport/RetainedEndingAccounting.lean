/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedEndingWords

/-! # The ending certificate plus the retained spokes is the full local target -/
namespace Gallai.Certificate.ThreeAnchor

/-- Keeping the spokes on old carriers leaves a disjoint local partition. -/
theorem retainedEnding_partition (s : State) (repair : Bool) (hs : s 0 = 1) :
    ((targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪ retainedRepair repair).val +
      ([s(0,anchor 0),s(0,anchor 1)] : List (Sym2 Vertex)) =
        (targetEdges s ∪ retainedRepair repair).val := by
  classical
  let S : Finset (Sym2 Vertex) := {s(0,anchor 0),s(0,anchor 1)}
  let U := (targetEdges s \ S) ∪ retainedRepair repair
  have hsub : S ⊆ targetEdges s := by
    have hsp (j : Fin 3) (hj : j = 0 ∨ j = 1) : s(0,anchor j) ∈ targetEdges s := by
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨(0,j), Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩, rfl⟩
      rw [hs]
      rcases hj with rfl | rfl <;> decide
    intro e he
    have he' : e = s(0,anchor 0) ∨ e = s(0,anchor 1) := by simpa [S] using he
    rcases he' with rfl | rfl
    · exact hsp 0 (Or.inl rfl)
    · exact hsp 1 (Or.inr rfl)
  have hr : Disjoint (retainedRepair repair) S := by cases repair <;> decide
  have hdis : Disjoint U S := by
    apply Finset.disjoint_left.mpr
    intro e he hS
    rcases Finset.mem_union.mp he with hd | hre
    · exact (Finset.mem_sdiff.mp hd).2 hS
    · exact Finset.disjoint_left.mp hr hre hS
  have hunion : U ∪ S = targetEdges s ∪ retainedRepair repair := by
    dsimp only [U]
    rw [Finset.union_right_comm, Finset.sdiff_union_of_subset hsub]
  have hv := congrArg Finset.val ((Finset.disjUnion_eq_union U S hdis).trans hunion)
  have hS : S.val = ([s(0,anchor 0),s(0,anchor 1)] : List (Sym2 Vertex)) := by decide
  change U.val + S.val = _ at hv
  rw [hS] at hv
  exact hv

end Gallai.Certificate.ThreeAnchor

namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A one-tail ending record adds back exactly the target not already covered
by the two retained spokes. This interface covers all six ordinary records. -/
theorem retainedWords_local_count (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (repair : Bool) (tail : List Vertex) (added : List (List Vertex))
    (hs : s 0 = 1)
    (h : Accepted ((targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪ retainedRepair repair)
      (tail :: added)) (e : Sym2 V) :
    ((wordEdges tail).map (Sym2.map (B.threeLabel A))).count e +
      (∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) +
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e := by
  have hc := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) h.2
  simp only [Multiset.map_coe, Multiset.coe_count] at hc
  rw [familyEdges, List.map_flatMap, List.count_flatMap] at hc
  change ((wordEdges tail).map (Sym2.map (B.threeLabel A))).count e +
    (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum = _ at hc
  have hsum : (added.map (fun w => ((wordEdges w).map (Sym2.map (B.threeLabel A))).count e)).sum =
      ∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e := by
    rw [← List.ofFn_getElem_eq_map, List.sum_ofFn]
    rfl
  rw [hsum] at hc
  have hp := congrArg (fun m : Multiset (Sym2 Vertex) =>
    (m.map (Sym2.map (B.threeLabel A))).count e) (retainedEnding_partition s repair hs)
  simp only [Multiset.map_add, Multiset.count_add, Multiset.map_coe, Multiset.coe_count,
    List.map_cons, List.map_nil, Sym2.map_mk, B.threeLabel_anchor] at hp
  have hz : B.threeLabel A 0 = B.label 0 := B.threeLabel_core A 0
  rw [hz] at hp
  exact (congrArg (· + ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e) hc).trans hp

/-- Specialize the shared kept-spoke accounting to a one-tail ending record. -/
theorem retainedEnding_local_count (A : Fin 3 ↪ {v : V // v ∉ B.vertices})
    (s : State) (repair : Bool) (tail : List Vertex) (added : List (List Vertex))
    (h : RetainedEndingAccepted s repair [tail] added) (e : Sym2 V) :
    ((wordEdges tail).map (Sym2.map (B.threeLabel A))).count e +
      (∑ i : Fin added.length, ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) +
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e =
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e :=
  B.retainedWords_local_count A s repair tail added h.1 h.2.2.2.2.1 e

end Gallai.WholeBowtie
