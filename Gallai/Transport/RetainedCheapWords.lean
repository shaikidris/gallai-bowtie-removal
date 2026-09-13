/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedEndingWords
import Gallai.Certificates.ThreeAnchorRetainedCheap

/-! # Original-graph realization of one-credit retained words -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

/-- An accepted local subgraph may omit the retained spokes. Its members
still realize in G, provided the optional repair edge is original. -/
def realizeRetainedSubsetMember (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (E : Finset (Sym2 Vertex)) (hE : E ⊆ targetEdges s ∪ retainedRepair repair)
    (words : List (List Vertex)) (h : Accepted E words)
    (word : List Vertex) (hw : word ∈ words) : NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.1 word hw).1)
    ((h.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hmem : f ∈ E := by
        change f ∈ E.val
        rw [← h.2]
        exact List.mem_flatMap.mpr ⟨word, hw, hf⟩
      rcases Finset.mem_union.mp (hE hmem) with ht | hr
      · exact B.threeLabel_target_edge A s hrow f ht
      · cases repair with
        | false => simp [retainedRepair] at hr
        | true =>
          have heq : f = s(anchor 1, anchor 2) := by simpa [retainedRepair] using hr
          subst f
          simp only [Sym2.map_mk, B.threeLabel_anchor]
          exact hp rfl)

/-- Every surviving symbol is the hub or one of the three anchors. -/
theorem threeLabel_survivor_cases (v : B.StarSurvivor) (u : Vertex)
    (hu : B.threeLabel A u = v.val) :
    v = B.completedHub ∨ v = B.retainedSlot A 0 ∨
      v = B.retainedSlot A 1 ∨ v = B.retainedSlot A 2 := by
  have cases : ∀ u : Vertex, u = 0 ∨ (0 < u.val ∧ u.val < 5) ∨
      u = anchor 0 ∨ u = anchor 1 ∨ u = anchor 2 := by decide
  rcases cases u with h | h | h | h | h
  · subst u
    exact Or.inl (Subtype.ext (hu.symm.trans (B.threeLabel_core A 0)))
  · exact (v.property (hu ▸ B.threeLabel_private A u h)).elim
  · subst u
    exact Or.inr (Or.inl (Subtype.ext (hu.symm.trans (B.threeLabel_anchor A 0))))
  · subst u
    exact Or.inr (Or.inr (Or.inl (Subtype.ext (hu.symm.trans (B.threeLabel_anchor A 1)))))
  · subst u
    exact Or.inr (Or.inr (Or.inr (Subtype.ext (hu.symm.trans (B.threeLabel_anchor A 2)))))

include hrow in
/-- A realized word has its mapped edge list and support, with no ambient
carrier assumptions. This serves both passing and ending cheap records. -/
theorem retainedSubset_word (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (E : Finset (Sym2 Vertex)) (hE : E ⊆ targetEdges s ∪ retainedRepair repair)
    (words : List (List Vertex)) (h : Accepted E words)
    (word : List Vertex) (hw : word ∈ words) :
    ∃ T : NonemptyPath G,
      T.walk.support = word.map (B.threeLabel A) ∧
      T.walk.edges = (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  let T := B.realizeRetainedSubsetMember A s hrow repair hp E hE words h word hw
  refine ⟨T, NonemptyPath.ofWord_support _ _ _ _, ?_⟩
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

include hrow in
/-- The cheap passing connector is a genuine p-q path. The remote anchor
is allowed in its support and will be excluded from its old carrier separately. -/
theorem retainedCheapPassingConnector (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapPassingAccepted s repair connector remote added) :
    ∃ M : G.Walk (A 0).val (A 1).val, M.IsPath ∧ ¬ M.Nil ∧
      M.edges = (wordEdges connector).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ M.support →
        v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 ∨
          v = B.completedHub ∨ v = B.retainedSlot A 2 := by
  obtain ⟨_, _, hh, hl, _, _, hacc, _⟩ := h
  obtain ⟨P, hsup, he⟩ := B.retainedSubset_word A s hrow repair hp
    _ (fun _ h => h) (connector :: remote :: added) hacc connector (List.mem_cons_self ..)
  have hs : P.start = (A 0).val := by
    have h := congrArg List.head? hsup
    rw [List.head?_map, hh] at h
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at h
    exact (Option.some.inj h).trans (B.threeLabel_anchor A 0)
  have ht : P.finish = (A 1).val := by
    have h := congrArg List.getLast? hsup
    rw [List.getLast?_map, hl] at h
    rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support] at h
    exact (Option.some.inj h).trans (B.threeLabel_anchor A 1)
  have hf : ∀ v : B.StarSurvivor, v.val ∈ P.walk.support →
      v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 ∨
        v = B.completedHub ∨ v = B.retainedSlot A 2 := by
    intro v hv
    rw [hsup] at hv
    obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
    rcases B.threeLabel_survivor_cases A v u hu with hx | hp | hq | hr
    · exact Or.inr (Or.inr (Or.inl hx))
    · exact Or.inl hp
    · exact Or.inr (Or.inl hq)
    · exact Or.inr (Or.inr (Or.inr hr))
  generalize hP : P = Q at hs ht he hf
  obtain ⟨u, v, M, hM, hne⟩ := Q
  dsimp only at hs ht he hf
  subst u v
  exact ⟨M, hM, hne, he, hf⟩

end Gallai.WholeBowtie
