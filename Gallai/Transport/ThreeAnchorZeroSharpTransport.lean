/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorZero
import Gallai.Transport.ThreeAnchorZeroTransport
import Gallai.Transport.ZeroSeparatedReconstruction

/-! # One-credit finite certificates reconstruct the sharp zero puncture -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- Exact local coverage of both mapped word families, without a repair edge. -/
theorem zeroSharpThree_local_count (tails added : List (List Vertex))
    (a : Fin tails.length → Fin 3) (h : ZeroOneAccepted s tails added a)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i : Fin tails.length,
      ((wordEdges tails[i]).map (Sym2.map (B.threeLabel A))).count e) +
      (∑ i : Fin added.length,
        ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) =
      if (∃ v ∈ e, v ∈ B.vertices) then 1 else 0 := by
  have hinj := Sym2.map.injective (B.threeLabel_injective A)
  by_cases hr : ∃ f : Sym2 Vertex, Sym2.map (B.threeLabel A) f = e
  · obtain ⟨f, rfl⟩ := hr
    simp only [List.count_map_of_injective _ _ hinj]
    have hsum (ws : List (List Vertex)) : (familyEdges ws).count f =
        ∑ i : Fin ws.length, (wordEdges ws[i]).count f := by
      rw [familyEdges, List.count_flatMap, ← List.ofFn_getElem_eq_map, List.sum_ofFn]
      rfl
    have hc := congrArg (Multiset.count f) h.2.2.2.2.1.2
    simp only [Multiset.coe_count, familyEdges, List.flatMap_append, List.count_append] at hc
    rw [← hsum tails, ← hsum added]
    change (familyEdges tails).count f + (familyEdges added).count f = _
    rw [show (familyEdges tails).count f + (familyEdges added).count f = _ from hc]
    have htcount : (targetEdges s).val.count f =
        if f ∈ targetEdges s then 1 else 0 := by
      split_ifs with he
      · exact Multiset.count_eq_one_of_mem (Finset.nodup _) he
      · exact Multiset.count_eq_zero_of_notMem he
    rw [htcount]
    have hm : f ∈ targetEdges s ↔
        ∃ v ∈ Sym2.map (B.threeLabel A) f, v ∈ B.vertices := by
      constructor
      · exact B.threeLabel_target_incident A s f
      · intro hv
        obtain ⟨g, hg, hgf⟩ := (B.threeLabel_target_iff A s hrows _).mpr ⟨he, hv⟩
        exact hinj hgf ▸ hg
    simp only [hm]
  · have hz (word : List Vertex) :
        ((wordEdges word).map (Sym2.map (B.threeLabel A))).count e = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      obtain ⟨f, _, hf⟩ := List.mem_map.mp hm
      exact hr ⟨f, hf⟩
    have hl : ¬ ∃ v ∈ e, v ∈ B.vertices := by
      intro hv
      obtain ⟨f, _, hf⟩ := (B.threeLabel_target_iff A s hrows e).mpr ⟨he, hv⟩
      exact hr ⟨f, hf⟩
    simp [hz, hl]

include hrows in
/-- The finite separated contract gives a genuine at-most-one-path expansion.
All carrier selection, simplicity and even endpoint reserves are derived. -/
theorem zeroSharpThree_reconstruction
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (tails added : List (List Vertex)) (a : Fin tails.length → Fin 3)
    (h : ZeroOneAccepted s tails added a)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card B.puncture.ConnectedComponent = 3)
    (D : Decomposition B.puncture) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧ E.size ≤ D.size + 1 ∧
      ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i := fun i j hj => (hrows i _).mpr ⟨j, hj, rfl⟩
  have hall (j : Fin 3) : (A j).val ∈ B.anchors := by
    obtain ⟨i, hi⟩ := h.2.1 j
    exact B.row_subset_anchors i (hrow i j hi)
  have hs : B.syndrome = ∅ := by
    rw [← B.threeAnchor_syndrome_image A hcover s hrows, h.1]
    simp
  let attachments : Fin tails.length ↪ {v // v ∉ B.vertices} :=
    ⟨fun i => A (a i), A.injective.comp h.2.2.1⟩
  let T : Fin tails.length → NonemptyPath G := fun i =>
    B.realizeThreeMember A s hrow (tails ++ added) h.2.2.2.2.1
      tails[i] (List.mem_append_left _ (List.getElem_mem _))
  let N : Fin added.length → NonemptyPath G := fun i =>
    B.realizeThreeMember A s hrow (tails ++ added) h.2.2.2.2.1
      added[i] (List.mem_append_right _ (List.getElem_mem _))
  have ht (i) : (T i).start = (attachments i).val := by
    have hsupp := B.realizeThreeMember_support A s hrow
      (tails ++ added) h.2.2.2.2.1 tails[i] (List.mem_append_left _ (List.getElem_mem _))
    have hs' := congrArg List.head? hsupp
    rw [List.head?_map, h.2.2.2.1 i] at hs'
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at hs'
    exact (Option.some.inj hs').trans (B.threeLabel_anchor A (a i))
  have hf (i) (v) (hv : v ∈ (T i).walk.support) : v ∈ B.vertices ∨ v ∈ B.anchors := by
    rw [show (T i).walk.support = _ from
      B.realizeThreeMember_support A s hrow _ _ _ _] at hv
    obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
    by_cases hu : u.val < 5
    · exact Or.inl (B.threeLabel_fresh A u hu)
    · let j : Fin 3 := ⟨u.val - 5, by omega⟩
      have he : u = anchor j := by
        apply Fin.ext
        dsimp [anchor, j]
        omega
      rw [he, B.threeLabel_anchor]
      exact Or.inr (hall j)
  have hcounts (ws : List (List Vertex)) (hm : ∀ i : Fin ws.length, ws[i] ∈ tails ++ added)
      (e : Sym2 V) :
      (∑ i : Fin ws.length, (B.realizeThreeMember A s hrow
        (tails ++ added) h.2.2.2.2.1 ws[i] (hm i)).walk.edges.count e) =
      ∑ i : Fin ws.length, ((wordEdges ws[i]).map (Sym2.map (B.threeLabel A))).count e := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (List.count e) (B.realizeThreeMember_edges A s hrow _ _ _ _)
  have hlocal (e) (he : e ∈ G.edgeSet) :
      (∑ i, (T i).walk.edges.count e) + (∑ i, (N i).walk.edges.count e) =
      if (∃ v ∈ e, v ∈ B.vertices) then 1 else 0 := by
    rw [show (∑ i, (T i).walk.edges.count e) = _ from hcounts tails _ e,
      show (∑ i, (N i).walk.edges.count e) = _ from hcounts added _ e]
    exact B.zeroSharpThree_local_count A s hrows tails added a h e he
  obtain ⟨E, hsize, hends⟩ := B.zeroSeparated_reconstruction hs hc hA hC D attachments (fun i => hall (a i)) T ht hf N hlocal
  exact ⟨E, hsize, hsize ▸ Nat.add_le_add_left h.2.2.2.2.2 _, hends⟩

end Gallai.WholeBowtie
