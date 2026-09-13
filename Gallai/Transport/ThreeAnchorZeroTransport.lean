/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorZero
import Gallai.Transport.ThreeAnchorWords
import Gallai.Transport.ThreeAnchorBoundary
import Gallai.Transport.PunctureSelected
import Gallai.Structure.ThreeAnchorRows
import Gallai.Foundations.EndpointBounds

/-! # Ambient reconstruction from ordinary zero-syndrome certificates -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- The mapped certificate covers exactly the deleted local boundary. -/
theorem zeroThree_local_count (a : Fin 3) (tail : List Vertex)
    (added : List (List Vertex)) (h : ZeroTwoAccepted s a tail added)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ((wordEdges tail).map (Sym2.map (B.threeLabel A))).count e +
      (∑ j : Fin added.length,
        ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e) =
      if (∃ v ∈ e, v ∈ B.vertices) then 1 else 0 := by
  have hinj := Sym2.map.injective (B.threeLabel_injective A)
  by_cases hr : ∃ f : Sym2 Vertex, Sym2.map (B.threeLabel A) f = e
  · obtain ⟨f, rfl⟩ := hr
    simp only [List.count_map_of_injective _ _ hinj]
    have hc := h.2.2.2.2.1.edge_count f
    have hc' : (wordEdges tail).count f +
        (∑ j : Fin added.length, (wordEdges added[j]).count f) =
          if f ∈ targetEdges s then 1 else 0 := by
      simpa [Fin.sum_univ_succ] using hc
    rw [hc']
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
/-- Zero-syndrome certificates give the actual reconstruction, with exact cost
and preservation away from their single spent anchor endpoint. -/
theorem zeroThree_reconstruction (a : Fin 3) (tail : List Vertex)
    (added : List (List Vertex)) (h : ZeroTwoAccepted s a tail added)
    (D : Decomposition B.puncture)
    (hpos : 0 < D.endpointCount (A a)) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : {v // v ∉ B.vertices}, w ≠ A a →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i := fun i j hj => (hrows i _).mpr ⟨j, hj, rfl⟩
  let T := B.realizeThreeMember A s hrow (tail :: added)
    h.2.2.2.2.1 tail (List.mem_cons_self ..)
  have hsupport : T.walk.support = tail.map (B.threeLabel A) :=
    B.realizeThreeMember_support A s hrow _ _ _ _
  have ht : T.start = (A a).val := by
    have hs := congrArg List.head? hsupport
    rw [List.head?_map, h.2.2.1] at hs
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at hs
    exact (Option.some.inj hs).trans (B.threeLabel_anchor A a)
  have hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices := by
    intro v hv
    rw [hsupport] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    cases tail with
    | nil => simp at hu
    | cons b bs =>
      have hb : b = anchor a := Option.some.inj h.2.2.1
      rcases List.mem_cons.mp hu with hu | hu
      · subst u
        exact Or.inl ((hb ▸ B.threeLabel_anchor A a).trans ht.symm)
      · exact Or.inr (B.threeLabel_fresh A u (h.2.2.2.1 u hu))
  let N : Fin added.length → NonemptyPath G := fun j =>
    B.realizeThreeMember A s hrow (tail :: added) h.2.2.2.2.1
      added[j] (List.mem_cons_of_mem _ (List.getElem_mem _))
  have hc : ∀ e ∈ G.edgeSet,
      T.walk.edges.count e + (∑ j, (N j).walk.edges.count e) =
        if (∃ v ∈ e, v ∈ B.vertices) then 1 else 0 := by
    intro e he
    have hT := B.realizeThreeMember_edges A s hrow
      (tail :: added) h.2.2.2.2.1 tail (List.mem_cons_self ..)
    have hN : (∑ j, (N j).walk.edges.count e) =
        ∑ j : Fin added.length,
          ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (List.count e)
        (B.realizeThreeMember_edges A s hrow _ _ _ _)
    change (B.realizeThreeMember A s hrow _ _ _ _).walk.edges.count e + _ = _
    rw [hT, hN]
    exact B.zeroThree_local_count A s hrows a tail added h e he
  obtain ⟨E, hsize, hends⟩ := B.puncture_single_tail_reconstruction D
    (A a) hpos T ht hf N hc
  exact ⟨E, hsize, hsize ▸ Nat.add_le_add_left h.2.2.2.2.2 _, hends⟩

end Gallai.WholeBowtie
