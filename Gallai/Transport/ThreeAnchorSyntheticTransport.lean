/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorWords
import Gallai.Transport.ThreeAnchorBoundary
import Gallai.Transport.PairRepairedCoverage

/-! # Synthetic three-anchor certificates reconstruct the original graph -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- Relabelled certificate counts cover precisely the deleted local boundary. -/
theorem syntheticThree_local_count (p q : Fin 3) (connector : List Vertex)
    (added : List (List Vertex)) (h : SyntheticAccepted s p q connector added)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ((wordEdges connector).map (Sym2.map (B.threeLabel A))).count e +
      (∑ j : Fin added.length,
        ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e) =
      if ∃ v ∈ e, v ∈ B.vertices then 1 else 0 := by
  have hinj := Sym2.map.injective (B.threeLabel_injective A)
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
/-- A synthetic certificate reconstructs with at most two new paths and
preserves every retained endpoint reserve. Record selection is separate. -/
theorem syntheticThree_reconstruction (p q : Fin 3) (connector : List Vertex)
    (added : List (List Vertex)) (h : SyntheticAccepted s p q connector added)
    (hmissing : ¬ G.Adj (A p).val (A q).val)
    (D : Decomposition (B.pairRepairedPuncture (A p) (A q))) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧
      ∀ w : {v // v ∉ B.vertices}, D.endpointCount w ≤ E.endpointCount w.val := by
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i := fun i j hj => (hrows i _).mpr ⟨j, hj, rfl⟩
  obtain ⟨M, hM, heM, hfM⟩ :=
    B.syntheticThreeConnector A s hrow p q connector added h
  let N : Fin added.length → NonemptyPath G := fun j =>
    B.realizeThreeMember A s hrow (connector :: added) h.2.2.2.2.2.1
      added[j] (List.mem_cons_of_mem _ (List.getElem_mem _))
  have hlocal : ∀ e ∈ G.edgeSet,
      M.edges.count e + (∑ j, (N j).walk.edges.count e) =
        if ∃ v ∈ e, v ∈ B.vertices then 1 else 0 := by
    intro e he
    rw [heM]
    have hn : (∑ j, (N j).walk.edges.count e) =
        ∑ j : Fin added.length,
          ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e := by
      apply Finset.sum_congr rfl
      intro j _
      rw [show (N j).walk.edges = _ from
        B.realizeThreeMember_edges A s hrow _ _ _ _]
    rw [hn]
    exact B.syntheticThree_local_count A s hrows p q connector added h e he
  obtain ⟨E, hsize, hends⟩ := B.syntheticPair_reconstruction (A p) (A q)
    (fun he => h.2.1 (A.injective he)) hmissing D M hM hfM N hlocal
  exact ⟨E, hsize, hsize ▸ Nat.add_le_add_left h.2.2.2.2.2.2 _, hends⟩

end Gallai.WholeBowtie
