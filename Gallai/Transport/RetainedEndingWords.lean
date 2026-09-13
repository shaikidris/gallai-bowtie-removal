/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorRetainedWords

/-! # Realizing terminal retained certificates with the spokes kept in place -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

/-- Ending words use original local edges other than the retained spokes,
and optionally the original anchor repair edge. -/
def realizeRetainedEndingMember (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (tails added : List (List Vertex)) (h : RetainedEndingAccepted s repair tails added)
    (word : List Vertex) (hw : word ∈ tails ++ added) : NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.2.2.2.2.1.1 word hw).1)
    ((h.2.2.2.2.1.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hf' : f ∈ (targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪
          retainedRepair repair := by
        change f ∈ ((targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪
          retainedRepair repair).val
        rw [← h.2.2.2.2.1.2]
        exact List.mem_flatMap.mpr ⟨word, hw, hf⟩
      rcases Finset.mem_union.mp hf' with ht | hr
      · exact B.threeLabel_target_edge A s hrow f (Finset.mem_sdiff.mp ht).1
      · cases repair with
        | false => simp [retainedRepair] at hr
        | true =>
          have heq : f = s(anchor 1,anchor 2) := by simpa [retainedRepair] using hr
          subst f
          simp only [Sym2.map_mk, B.threeLabel_anchor]
          exact hp rfl)

theorem realizeRetainedEndingMember_edges (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (tails added : List (List Vertex)) (h : RetainedEndingAccepted s repair tails added)
    (word : List Vertex) (hw : word ∈ tails ++ added) :
    (B.realizeRetainedEndingMember A s hrow repair hp tails added h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

/-- A strict private slot maps to a deleted private vertex, not the retained hub. -/
theorem threeLabel_private (u : Vertex) (hu : 0 < u.val ∧ u.val < 5) :
    B.threeLabel A u ∈ (Finset.univ.erase 0).map B.label := by
  let i : Fin 5 := ⟨u.val, hu.2⟩
  have hi : i.castAdd 3 = u := Fin.ext rfl
  rw [← hi, B.threeLabel_core]
  exact Finset.mem_map.mpr ⟨i, by simp [i, Fin.ext_iff, Nat.ne_of_gt hu.1], rfl⟩

include hrow in
/-- Every terminal tail is an actual hub-rooted path whose remaining vertices
are private, exactly the freshness condition used by terminal restoration. -/
theorem retainedEndingTail (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (tails added : List (List Vertex)) (h : RetainedEndingAccepted s repair tails added)
    (word : List Vertex) (hw : word ∈ tails) :
    ∃ T : NonemptyPath G, T.start = B.label 0 ∧
      T.walk.edges = (wordEdges word).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ (Finset.univ.erase 0).map B.label := by
  let hw' := List.mem_append_left added hw
  let T := B.realizeRetainedEndingMember A s hrow repair hp tails added h word hw'
  have hsup : T.walk.support = word.map (B.threeLabel A) := NonemptyPath.ofWord_support _ _ _ _
  obtain ⟨hh, hf⟩ := h.2.2.2.1 word hw
  have hstart : T.start = B.label 0 := by
    have he := congrArg List.head? hsup
    rw [List.head?_map, hh] at he
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at he
    exact (Option.some.inj he).trans (B.threeLabel_core A 0)
  refine ⟨T, hstart, B.realizeRetainedEndingMember_edges A s hrow repair hp _ _ h _ _, ?_⟩
  intro v hv
  rw [hsup] at hv
  obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
  have hword : word = 0 :: word.tail := List.eq_cons_of_mem_head? (by simp [hh])
  have hu' : u = 0 ∨ u ∈ word.tail := List.mem_cons.mp (hword ▸ hu)
  rcases hu' with rfl | hu'
  · exact Or.inl (huv.symm.trans ((B.threeLabel_core A 0).trans hstart.symm))
  · exact Or.inr (huv ▸ B.threeLabel_private A u (hf u hu'))

end Gallai.WholeBowtie
