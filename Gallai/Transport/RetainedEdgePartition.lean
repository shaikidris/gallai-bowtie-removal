/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorBoundary
import Gallai.Structure.ThreeAnchorRetainedRows
import Gallai.Foundations.EdgeCounts

/-! # Exact retained auxiliary and local-target multiplicities -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Private deletion and optional original-edge deletion leave exactly the
stated missing edges. The adjacency contract is pointwise, not a coverage oracle. -/
theorem retainedAux_edge_count_of_original
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (p q : B.StarSurvivor) (repair : Bool)
    (hAdj : ∀ u v, G.Adj u.val v.val → (H.Adj u v ↔
      ¬ (repair = true ∧ s(u.val, v.val) = s(p.val, q.val))))
    (D : Decomposition H) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) =
      if (∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) ∨
        (repair = true ∧ e = s(p.val, q.val)) then 0 else 1 := by
  classical
  by_cases hd : ∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label
  · rw [if_pos (Or.inl hd)]
    obtain ⟨v, hv, hdel⟩ := hd
    apply Finset.sum_eq_zero
    intro i _
    apply List.count_eq_zero.mpr
    intro hi
    obtain ⟨f, _, hf⟩ := List.mem_map.mp hi
    rw [← hf] at hv
    obtain ⟨w, _, hw⟩ := Sym2.mem_map.mp hv
    exact w.property (hw ▸ hdel)
  · induction e using Sym2.inductionOn with
    | hf u v =>
      have hu : u ∉ (Finset.univ.erase 0).map B.label := fun h => hd ⟨u, by simp, h⟩
      have hv : v ∉ (Finset.univ.erase 0).map B.label := fun h => hd ⟨v, by simp, h⟩
      let f : Sym2 B.StarSurvivor := s(⟨u, hu⟩, ⟨v, hv⟩)
      change (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count
        (Sym2.map Subtype.val f)) = _
      simp only [List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
      rw [D.sum_edge_count]
      have hf : f ∈ H.edgeSet ↔ ¬ (repair = true ∧ s(u,v) = s(p.val,q.val)) := by
        exact hAdj ⟨u, hu⟩ ⟨v, hv⟩ he
      by_cases hr : repair = true ∧ s(u,v) = s(p.val,q.val)
      · rw [if_neg (fun h => hf.mp h hr), if_pos (Or.inr hr)]
      · rw [if_pos (hf.mpr hr), if_neg (not_or.mpr ⟨hd, hr⟩)]

/-- Exact deletion adjacency specializes the original-edge counting interface. -/
theorem retainedAux_edge_count
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj]
    (p q : B.StarSurvivor) (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s(p.val,q.val)))
    (D : Decomposition H) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) =
      if (∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) ∨
        (repair = true ∧ e = s(p.val,q.val)) then 0 else 1 :=
  B.retainedAux_edge_count_of_original H p q repair
    (fun u v ha => (hAdj u v).trans (and_iff_right ha)) D e he

variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- The augmented finite target covers the bowtie boundary and the optional
original repair edge, each exactly once, for arbitrary anchor adjacency. -/
theorem retainedTarget_edge_count (repair : Bool) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ((targetEdges s ∪ retainedRepair repair).val.map
      (Sym2.map (B.threeLabel A))).count e =
      if (∃ v ∈ e, v ∈ B.vertices) ∨
        (repair = true ∧ e = s((A 1).val, (A 2).val)) then 1 else 0 := by
  classical
  let T := (targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))
  have hn : T.Nodup := (targetEdges s ∪ retainedRepair repair).nodup.map
    (Sym2.map.injective (B.threeLabel_injective A))
  have hm : e ∈ T ↔ (∃ v ∈ e, v ∈ B.vertices) ∨
      (repair = true ∧ e = s((A 1).val, (A 2).val)) := by
    dsimp only [T]
    rw [Multiset.mem_map]
    constructor
    · rintro ⟨f, hf, hfe⟩
      rcases Finset.mem_union.mp hf with ht | hr
      · exact Or.inl ((B.threeLabel_target_iff A s hrows e).mp ⟨f, ht, hfe⟩).2
      · cases repair with
        | false => simp [retainedRepair] at hr
        | true =>
          have hf' : f = s(anchor 1, anchor 2) := by simpa [retainedRepair] using hr
          subst f
          exact Or.inr ⟨rfl, by simpa only [Sym2.map_mk, B.threeLabel_anchor] using hfe.symm⟩
    · rintro (hl | ⟨hr, heq⟩)
      · obtain ⟨f, hf, hfe⟩ := (B.threeLabel_target_iff A s hrows e).mpr ⟨he, hl⟩
        exact ⟨f, Finset.mem_union_left _ hf, hfe⟩
      · refine ⟨s(anchor 1, anchor 2), Finset.mem_union_right _ ?_, ?_⟩
        · simp [retainedRepair, hr]
        · simpa only [Sym2.map_mk, B.threeLabel_anchor] using heq.symm
  by_cases ht : e ∈ T
  · exact (Multiset.count_eq_one_of_mem hn ht).trans (if_pos (hm.mp ht)).symm
  · exact (Multiset.count_eq_zero.mpr ht).trans (if_neg (fun h => ht (hm.mpr h))).symm

include hrows in
/-- The normalized row names the two retained spokes in the actual graph. -/
theorem retainedHub_normalized_neighbors (hs : s 0 = 1) (v : B.StarSurvivor) :
    B.retainedHubGraph.Adj B.completedHub v ↔
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
  rw [B.retainedHub_adj, hrows]
  constructor
  · rintro ⟨j, hj, hjv⟩
    have hj' : j = 0 ∨ j = 1 := by
      rw [hs] at hj
      exact (by decide : ∀ j : Fin 3,
        (rowMask 1).val.testBit j.val = true → j = 0 ∨ j = 1) j hj
    rcases hj' with rfl | rfl
    · exact Or.inl (Subtype.ext hjv.symm)
    · exact Or.inr (Subtype.ext hjv.symm)
  · rintro (rfl | rfl)
    · exact ⟨0, by rw [hs]; decide, rfl⟩
    · exact ⟨1, by rw [hs]; decide, rfl⟩

include hrows in
/-- A local edge not meeting a private vertex must be one of the retained spokes. -/
theorem retained_local_spoke (hs : s 0 = 1) (e : Sym2 V) (he : e ∈ G.edgeSet)
    (hl : ∃ v ∈ e, v ∈ B.vertices)
    (hd : ¬ ∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) :
    e = s(B.label 0, (A 0).val) ∨ e = s(B.label 0, (A 1).val) := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    have hu : u ∉ (Finset.univ.erase 0).map B.label := fun h => hd ⟨u, by simp, h⟩
    have hv : v ∉ (Finset.univ.erase 0).map B.label := fun h => hd ⟨v, by simp, h⟩
    obtain ⟨w, hw, hwB⟩ := hl
    have hw' : w = u ∨ w = v := by simpa using hw
    rcases hw' with hw' | hw'
    · subst w
      have hux := B.survivor_mem_vertices ⟨u, hu⟩ hwB
      have ha : B.retainedHubGraph.Adj B.completedHub ⟨v, hv⟩ := by
        change G.Adj (B.label 0) v
        exact hux ▸ he
      rcases (B.retainedHub_normalized_neighbors A s hrows hs ⟨v, hv⟩).mp ha with h | h
      · exact Or.inl (congrArg₂ (fun a b => s(a,b)) hux (congrArg Subtype.val h))
      · exact Or.inr (congrArg₂ (fun a b => s(a,b)) hux (congrArg Subtype.val h))
    · subst w
      have hvx := B.survivor_mem_vertices ⟨v, hv⟩ hwB
      have ha : B.retainedHubGraph.Adj B.completedHub ⟨u, hu⟩ := by
        change G.Adj (B.label 0) u
        exact hvx ▸ (show G.Adj u v from he).symm
      rcases (B.retainedHub_normalized_neighbors A s hrows hs ⟨u, hu⟩).mp ha with h | h
      · exact Or.inl (Sym2.eq_swap.trans
          (congrArg₂ (fun a b => s(a,b)) hvx (congrArg Subtype.val h)))
      · exact Or.inr (Sym2.eq_swap.trans
          (congrArg₂ (fun a b => s(a,b)) hvx (congrArg Subtype.val h)))

include hrows in
/-- The auxiliary and local target overlap precisely on the released spokes. -/
theorem retained_edge_balance_of_original
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, G.Adj u.val v.val → (H.Adj u v ↔
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val))))
    (D : Decomposition H) (hs : s 0 = 1) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e =
      1 + ([s(B.label 0,(A 0).val), s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
  classical
  let L : List (Sym2 V) := [s(B.label 0,(A 0).val), s(B.label 0,(A 1).val)]
  have hubB : B.label 0 ∈ B.vertices := Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hne : s(B.label 0,(A 0).val) ≠ s(B.label 0,(A 1).val) := by
    intro h
    rcases Sym2.eq_iff.mp h with h | h
    · have hi : (0 : Fin 3) = 1 := A.injective (Subtype.ext h.2)
      exact (by decide : (0 : Fin 3) ≠ 1) hi
    · exact (A 1).property (h.1 ▸ hubB)
  have hnodup : L.Nodup := by simp [L, hne]
  have hcount : L.count e = if e ∈ L then 1 else 0 := by
    by_cases h : e ∈ L
    · rw [if_pos h]; exact List.count_eq_one_of_mem hnodup h
    · rw [if_neg h]; exact List.count_eq_zero.mpr h
  have hp : (∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) →
      ∃ v ∈ e, v ∈ B.vertices := by
    rintro ⟨v, hv, hdel⟩
    obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hdel
    exact ⟨v, hv, Finset.mem_map.mpr ⟨i, Finset.mem_univ _, hi⟩⟩
  have hsp : e ∈ L → (∃ v ∈ e, v ∈ B.vertices) ∧
      ¬ (∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) := by
    have hsafe (j : Fin 3) : ¬ ∃ v ∈ s(B.label 0,(A j).val),
        v ∈ (Finset.univ.erase 0).map B.label := by
      rintro ⟨v, hv, hdel⟩
      have hv' : v = B.label 0 ∨ v = (A j).val := by simpa using hv
      rcases hv' with rfl | rfl
      · exact B.completedHub.property hdel
      · exact (B.retainedSlot A j).property hdel
    intro h
    have h' : e = s(B.label 0,(A 0).val) ∨ e = s(B.label 0,(A 1).val) := by
      simpa only [L, List.mem_cons, List.not_mem_nil, or_false] using h
    rcases h' with rfl | rfl
    · exact ⟨⟨B.label 0, by simp, hubB⟩, hsafe 0⟩
    · exact ⟨⟨B.label 0, by simp, hubB⟩, hsafe 1⟩
  have hreverse : (∃ v ∈ e, v ∈ B.vertices) →
      ¬ (∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label) → e ∈ L := by
    intro hl hd
    simpa only [L, List.mem_cons, List.not_mem_nil, or_false] using
      B.retained_local_spoke A s hrows hs e he hl hd
  have hr : repair = true ∧ e = s((A 1).val,(A 2).val) →
      ¬ (∃ v ∈ e, v ∈ B.vertices) := by
    rintro ⟨_, rfl⟩ ⟨v, hv, hB⟩
    have hv' : v = (A 1).val ∨ v = (A 2).val := by simpa using hv
    rcases hv' with rfl | rfl
    · exact (A 1).property hB
    · exact (A 2).property hB
  rw [B.retainedAux_edge_count_of_original H (B.retainedSlot A 1) (B.retainedSlot A 2)
    repair hAdj D e he, B.retainedTarget_edge_count A s hrows repair e he]
  change _ = 1 + L.count e
  rw [hcount]
  dsimp only [retainedSlot]
  by_cases hd : ∃ v ∈ e, v ∈ (Finset.univ.erase 0).map B.label <;>
    by_cases hl : ∃ v ∈ e, v ∈ B.vertices <;>
    by_cases hre : repair = true ∧ e = s((A 1).val,(A 2).val) <;>
    by_cases hmem : e ∈ L <;>
    simp_all only [hd, hl, hre, hmem, or_true, true_or, or_false, false_or,
      ite_true, ite_false, not_true_eq_false, not_false_eq_true, true_implies,
      and_false, and_true, false_and, true_and, eq_self] <;> omega

include hrows in
/-- Preserve the exact-deletion API for ordinary reconstruction callers. -/
theorem retained_edge_balance
    (H : SimpleGraph B.StarSurvivor) [DecidableRel H.Adj] (repair : Bool)
    (hAdj : ∀ u v, H.Adj u v ↔ G.Adj u.val v.val ∧
      ¬ (repair = true ∧ s(u.val,v.val) = s((A 1).val,(A 2).val)))
    (D : Decomposition H) (hs : s 0 = 1) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i, ((D.path i).walk.edges.map (Sym2.map Subtype.val)).count e) +
      ((targetEdges s ∪ retainedRepair repair).val.map (Sym2.map (B.threeLabel A))).count e =
      1 + ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e :=
  B.retained_edge_balance_of_original A s hrows H repair
    (fun u v ha => (hAdj u v).trans (and_iff_right ha)) D hs e he

end Gallai.WholeBowtie
