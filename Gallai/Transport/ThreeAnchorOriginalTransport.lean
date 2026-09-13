/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorOriginalWords
import Gallai.Transport.ThreeAnchorBoundary
import Gallai.Transport.OriginalPairReconstruction
import Gallai.Structure.ThreeAnchorRows
import Gallai.Foundations.EndpointBounds

/-! # Ambient reconstruction from original-edge three-anchor certificates -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrows : ∀ i v, v ∈ B.row i ↔
  ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)

include hrows in
/-- The mapped certificate covers exactly the local boundary and original repair. -/
theorem originalThree_local_count (p q a : Fin 3) (tail : List Vertex)
    (added : List (List Vertex)) (h : OriginalAccepted s p q a tail added)
    (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ((wordEdges tail).map (Sym2.map (B.threeLabel A))).count e +
      (∑ j : Fin added.length,
        ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e) =
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
/-- Original-edge certificates give the actual reconstruction, with exact cost
and preservation away from their single spent anchor endpoint. -/
theorem originalThree_reconstruction (p q a : Fin 3) (tail : List Vertex)
    (added : List (List Vertex)) (h : OriginalAccepted s p q a tail added)
    (hpq : G.Adj (A p).val (A q).val)
    (D : Decomposition (B.pairRepairedPuncture (A p) (A q)))
    (hpos : 0 < D.endpointCount (A a)) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : {v // v ∉ B.vertices}, w ≠ A a →
        D.endpointCount w ≤ E.endpointCount w.val := by
  have hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
      (A j).val ∈ B.row i := fun i j hj => (hrows i _).mpr ⟨j, hj, rfl⟩
  let T := B.realizeThreeOriginalMember A s hrow p q hpq (tail :: added)
    h.2.2.2.2.2.1 tail (List.mem_cons_self ..)
  have hsupport : T.walk.support = tail.map (B.threeLabel A) :=
    B.realizeThreeOriginalMember_support A s hrow p q hpq _ _ _ _
  have ht : T.start = (A a).val := by
    have hs := congrArg List.head? hsupport
    rw [List.head?_map, h.2.2.2.1] at hs
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at hs
    exact (Option.some.inj hs).trans (B.threeLabel_anchor A a)
  have hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices := by
    intro v hv
    rw [hsupport] at hv
    obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
    cases tail with
    | nil => simp at hu
    | cons b bs =>
      have hb : b = anchor a := Option.some.inj h.2.2.2.1
      rcases List.mem_cons.mp hu with hu | hu
      · subst u
        exact Or.inl ((hb ▸ B.threeLabel_anchor A a).trans ht.symm)
      · exact Or.inr (B.threeLabel_fresh A u (h.2.2.2.2.1 u hu))
  let N : Fin added.length → NonemptyPath G := fun j =>
    B.realizeThreeOriginalMember A s hrow p q hpq (tail :: added) h.2.2.2.2.2.1
      added[j] (List.mem_cons_of_mem _ (List.getElem_mem _))
  have hc : ∀ e ∈ G.edgeSet,
      T.walk.edges.count e + (∑ j, (N j).walk.edges.count e) =
        if (∃ v ∈ e, v ∈ B.vertices) ∨ e = s((A p).val,(A q).val) then 1 else 0 := by
    intro e he
    have hT := B.realizeThreeOriginalMember_edges A s hrow p q hpq
      (tail :: added) h.2.2.2.2.2.1 tail (List.mem_cons_self ..)
    have hN : (∑ j, (N j).walk.edges.count e) =
        ∑ j : Fin added.length,
          ((wordEdges added[j]).map (Sym2.map (B.threeLabel A))).count e := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (List.count e)
        (B.realizeThreeOriginalMember_edges A s hrow p q hpq _ _ _ _)
    change (B.realizeThreeOriginalMember A s hrow p q hpq _ _ _ _).walk.edges.count e + _ = _
    rw [hT, hN]
    exact B.originalThree_local_count A s hrows p q a tail added h e he
  obtain ⟨E, hsize, hends⟩ := B.originalPair_reconstruction (A p) (A q) hpq D
    (A a) hpos T ht hf N hc
  exact ⟨E, hsize, hsize ▸ Nat.add_le_add_left h.2.2.2.2.2.2 _, hends⟩

include hrows in
/-- Actual anchor parity supplies the required endpoint automatically. All even
retained vertices keep their reserves, since the spent attachment is odd. -/
theorem originalThree_reconstruction_of_parity
    (hA : ∀ v ∈ B.anchors, ∃ j, (A j).val = v)
    (p q a : Fin 3) (tail : List Vertex) (added : List (List Vertex))
    (h : OriginalAccepted s p q a tail added)
    (hpq : G.Adj (A p).val (A q).val)
    (D : Decomposition (B.pairRepairedPuncture (A p) (A q))) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  obtain ⟨i, hi⟩ := h.2.2.1
  have ha : (A a).val ∈ B.anchors := B.row_subset_anchors i
    ((hrows i _).mpr ⟨a, hi, rfl⟩)
  have hodd := B.odd_degree_anchor ha
  have hs := B.threeAnchor_syndrome_pair A hA s hrows p q h.1
  have hne : A p ≠ A q := fun he => h.2.1 (A.injective he)
  have haux : Odd ((B.pairRepairedPuncture (A p) (A q)).degree (A a)) := by
    apply Nat.not_even_iff_odd.mp
    intro he
    exact (Nat.not_even_iff_odd.mpr hodd)
      ((B.pairRepairedPuncture_even_iff (A p) (A q) hne hs (A a)).mp he)
  obtain ⟨E, hsize, hbound, hends⟩ := B.originalThree_reconstruction A s hrows
    p q a tail added h hpq D (D.endpointCount_pos_of_odd_degree (A a) haux)
  refine ⟨E, hsize, hbound, ?_⟩
  intro w hw
  apply hends w
  intro he
  subst w
  exact (Nat.not_even_iff_odd.mpr hodd) hw

end Gallai.WholeBowtie
