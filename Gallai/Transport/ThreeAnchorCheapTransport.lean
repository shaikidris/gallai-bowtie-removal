/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Transport.ThreeAnchorOriginalTransport
import Gallai.Transport.SeparatedOriginalReconstruction

/-! # One-credit finite certificates reconstruct sharply separated repairs -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- Exact local coverage of both mapped word families, including the repair edge. -/
theorem cheapThree_local_count (p q : Fin 3) (tails added : List (List Vertex))
    (a : Fin tails.length → Fin 3) (h : CheapOriginalAccepted s p q tails added a)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ i : Fin tails.length,
      ((wordEdges tails[i]).map (Sym2.map (B.threeLabel A))).count e) +
      (∑ i : Fin added.length,
        ((wordEdges added[i]).map (Sym2.map (B.threeLabel A))).count e) =
      if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s((A p).val,(A q).val) then 1 else 0 := by
  have hinj := Sym2.map.injective (B.threeLabel_injective A)
  have hmrepair : Sym2.map (B.threeLabel A) s(anchor p, anchor q) =
      s((A p).val,(A q).val) := by simp only [Sym2.map_mk, B.threeLabel_anchor]
  by_cases hr : ∃ f : Sym2 Vertex, Sym2.map (B.threeLabel A) f = e
  · obtain ⟨f, rfl⟩ := hr
    simp only [List.count_map_of_injective _ _ hinj]
    rw [h.edge_count]
    have hm : f ∈ targetEdges s ↔
        ∃ v ∈ Sym2.map (B.threeLabel A) f, v ∈ B.vertices := by
      constructor
      · exact B.threeLabel_target_incident A s f
      · intro hv
        obtain ⟨g, hg, hgf⟩ := (B.threeLabel_target_iff A s hrows _).mpr ⟨he, hv⟩
        exact hinj hgf ▸ hg
    have hrp : f = s(anchor p, anchor q) ↔
        Sym2.map (B.threeLabel A) f = s((A p).val,(A q).val) := by
      rw [← hmrepair]
      exact hinj.eq_iff.symm
    simp only [Finset.mem_union, Finset.mem_singleton, hm, hrp]
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
    have hp : e ≠ s((A p).val,(A q).val) := fun h =>
      hr ⟨s(anchor p, anchor q), hmrepair.trans h.symm⟩
    simp [hz, hl, hp]

include hrows in
/-- The finite separated contract gives a genuine at-most-one-path expansion.
All carrier selection, simplicity and even endpoint reserves are derived. -/
theorem cheapThree_reconstruction
    (hcover : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (p q : Fin 3) (tails added : List (List Vertex)) (a : Fin tails.length → Fin 3)
    (h : CheapOriginalAccepted s p q tails added a)
    (hc : G.Connected) (hA : B.anchors.card ≤ 3)
    (hC : Fintype.card (B.pairRepairedPuncture (A p) (A q)).ConnectedComponent = 3)
    (D : Decomposition (B.pairRepairedPuncture (A p) (A q))) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧ E.size ≤ D.size + 1 ∧
      ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i := fun i j hj => (hrows i _).mpr ⟨j, hj, rfl⟩
  have hall (j : Fin 3) : (A j).val ∈ B.anchors := by
    obtain ⟨i, hi⟩ := h.2.2.1 j
    exact B.row_subset_anchors i (hrow i j hi)
  have hne : A p ≠ A q := fun he => h.2.1 (A.injective he)
  have hs := B.threeAnchor_syndrome_pair A hcover s hrows p q h.1
  have hpq := B.pairRepaired_three_components_original (A p) (A q) hne hs hc hA hC
  let attachments : Fin tails.length ↪ {v // v ∉ B.vertices} :=
    ⟨fun i => A (a i), A.injective.comp h.2.2.2.1⟩
  let T : Fin tails.length → NonemptyPath G := fun i =>
    B.realizeThreeOriginalMember A s hrow p q hpq (tails ++ added) h.2.2.2.2.2.1
      tails[i] (List.mem_append_left _ (List.getElem_mem _))
  let N : Fin added.length → NonemptyPath G := fun i =>
    B.realizeThreeOriginalMember A s hrow p q hpq (tails ++ added) h.2.2.2.2.2.1
      added[i] (List.mem_append_right _ (List.getElem_mem _))
  have ht (i) : (T i).start = (attachments i).val := by
    have hsupp := B.realizeThreeOriginalMember_support A s hrow p q hpq
      (tails ++ added) h.2.2.2.2.2.1 tails[i] (List.mem_append_left _ (List.getElem_mem _))
    have hs' := congrArg List.head? hsupp
    rw [List.head?_map, h.2.2.2.2.1 i] at hs'
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at hs'
    exact (Option.some.inj hs').trans (B.threeLabel_anchor A (a i))
  have hf (i) (v) (hv : v ∈ (T i).walk.support) : v ∈ B.vertices ∨ v ∈ B.anchors := by
    rw [show (T i).walk.support = _ from
      B.realizeThreeOriginalMember_support A s hrow p q hpq _ _ _ _] at hv
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
      (∑ i : Fin ws.length, (B.realizeThreeOriginalMember A s hrow p q hpq
        (tails ++ added) h.2.2.2.2.2.1 ws[i] (hm i)).walk.edges.count e) =
      ∑ i : Fin ws.length, ((wordEdges ws[i]).map (Sym2.map (B.threeLabel A))).count e := by
    apply Finset.sum_congr rfl
    intro i _
    exact congrArg (List.count e) (B.realizeThreeOriginalMember_edges A s hrow p q hpq _ _ _ _)
  have hlocal (e) (he : e ∈ G.edgeSet) :
      (∑ i, (T i).walk.edges.count e) + (∑ i, (N i).walk.edges.count e) =
      if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s((A p).val,(A q).val) then 1 else 0 := by
    rw [show (∑ i, (T i).walk.edges.count e) = _ from hcounts tails _ e,
      show (∑ i, (N i).walk.edges.count e) = _ from hcounts added _ e]
    exact B.cheapThree_local_count A s hrows p q tails added a h e he
  obtain ⟨E, hsize, hends⟩ := B.separatedOriginal_reconstruction (A p) (A q)
    hpq hne hs hc hA hC D attachments (fun i => hall (a i)) T ht hf N hlocal
  exact ⟨E, hsize, hsize ▸ Nat.add_le_add_left h.2.2.2.2.2.2 _, hends⟩

end Gallai.WholeBowtie
