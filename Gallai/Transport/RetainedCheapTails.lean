/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapWords

/-! # The hub and remote tails supplied by cheap retained certificates -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

include hrow

/-- Any accepted remote-rooted word supplies a tail whose surviving vertices
are precisely among the remote anchor, the hub and its two neighbours. -/
theorem retainedCheapRemoteWord (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (E : Finset (Sym2 Vertex)) (hE : E ⊆ targetEdges s ∪ retainedRepair repair)
    (words : List (List Vertex)) (h : Accepted E words)
    (remote : List Vertex) (hw : remote ∈ words) (hh : remote.head? = some (anchor 2)) :
    ∃ T : NonemptyPath G, T.start = (A 2).val ∧
      T.walk.edges = (wordEdges remote).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
        v = B.retainedSlot A 2 ∨ v = B.completedHub ∨
          v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
  obtain ⟨T, hsup, he⟩ := B.retainedSubset_word A s hrow repair hp E hE words h remote hw
  have ht : T.start = (A 2).val := by
    have h := congrArg List.head? hsup
    rw [List.head?_map, hh] at h
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at h
    exact (Option.some.inj h).trans (B.threeLabel_anchor A 2)
  refine ⟨T, ht, he, ?_⟩
  intro v hv
  rw [hsup] at hv
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
  rcases B.threeLabel_survivor_cases A v u hu with hx | hp | hq | hr
  · exact Or.inr (Or.inl hx)
  · exact Or.inr (Or.inr (Or.inl hp))
  · exact Or.inr (Or.inr (Or.inr hq))
  · exact Or.inl hr

/-- The passing certificate's remote tail is directly realizable. -/
theorem retainedCheapPassingRemote (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapPassingAccepted s repair connector remote added) :
    ∃ T : NonemptyPath G, T.start = (A 2).val ∧
      T.walk.edges = (wordEdges remote).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
        v = B.retainedSlot A 2 ∨ v = B.completedHub ∨
          v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
  obtain ⟨_, _, _, _, hh, _, hacc, _⟩ := h
  exact B.retainedCheapRemoteWord A s hrow repair hp _ (fun _ h => h)
    _ hacc remote (by simp) hh

/-- The ending certificate's remote tail is directly realizable, with both
retained spokes omitted from the active local edge set. -/
theorem retainedCheapEndingRemote (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (tails : List (List Vertex)) (remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapEndingAccepted s repair tails remote added) :
    ∃ T : NonemptyPath G, T.start = (A 2).val ∧
      T.walk.edges = (wordEdges remote).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
        v = B.retainedSlot A 2 ∨ v = B.completedHub ∨
          v = B.retainedSlot A 0 ∨ v = B.retainedSlot A 1 := by
  obtain ⟨_, _, _, _, hh, _, hacc, _⟩ := h
  apply B.retainedCheapRemoteWord A s hrow repair hp _ _ _ hacc remote
    (by simp) hh
  intro e he
  rcases Finset.mem_union.mp he with ht | hr
  · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp ht).1
  · exact Finset.mem_union_right _ hr

/-- Each hub tail avoids the two old hub neighbours; its only possible
surviving vertices are the attachment hub and remote anchor. -/
theorem retainedCheapEndingTail (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (tails : List (List Vertex)) (remote : List Vertex) (added : List (List Vertex))
    (h : Retained.CheapEndingAccepted s repair tails remote added)
    (word : List Vertex) (hw : word ∈ tails) :
    ∃ T : NonemptyPath G, T.start = B.label 0 ∧
      T.walk.edges = (wordEdges word).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
        v = B.completedHub ∨ v = B.retainedSlot A 2 := by
  obtain ⟨_, _, _, htail, _, _, hacc, _⟩ := h
  have hsub : (targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}) ∪ retainedRepair repair ⊆
      targetEdges s ∪ retainedRepair repair := by
    intro e he
    rcases Finset.mem_union.mp he with ht | hr
    · exact Finset.mem_union_left _ (Finset.mem_sdiff.mp ht).1
    · exact Finset.mem_union_right _ hr
  obtain ⟨T, hsup, he⟩ := B.retainedSubset_word A s hrow repair hp _ hsub _ hacc word
    (List.mem_append_left _ hw)
  obtain ⟨hh, hf⟩ := htail word hw
  have ht : T.start = B.label 0 := by
    have h := congrArg List.head? hsup
    rw [List.head?_map, hh] at h
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at h
    exact (Option.some.inj h).trans (B.threeLabel_core A 0)
  refine ⟨T, ht, he, ?_⟩
  intro v hv
  rw [hsup] at hv
  obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
  have hword : word = 0 :: word.tail := List.eq_cons_of_mem_head? (by simp [hh])
  rcases List.mem_cons.mp (hword ▸ hu) with h0 | hu'
  · subst u
    exact Or.inl (Subtype.ext (huv.symm.trans (B.threeLabel_core A 0)))
  · rcases hf u hu' with hprivate | hr
    · exact (v.property (huv ▸ B.threeLabel_private A u hprivate)).elim
    · subst u
      exact Or.inr (Subtype.ext (huv.symm.trans (B.threeLabel_anchor A 2)))

end Gallai.WholeBowtie
