/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedEndingWords

/-! # Strict-private connectors from retained synthetic certificates -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

/-- All synthetic record words use only original local edges, with no retained spokes. -/
def realizeRetainedSyntheticMember (connector : List Vertex) (added : List (List Vertex))
    (h : Retained.SyntheticAccepted s connector added)
    (word : List Vertex) (hw : word ∈ connector :: added) : NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.2.2.2.2.2.1.1 word hw).1)
    ((h.2.2.2.2.2.1.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hf' : f ∈ targetEdges s \ {s(0,anchor 0),s(0,anchor 1)} := by
        change f ∈ (targetEdges s \ {s(0,anchor 0),s(0,anchor 1)}).val
        rw [← h.2.2.2.2.2.1.2]
        exact List.mem_flatMap.mpr ⟨word,hw,hf⟩
      exact B.threeLabel_target_edge A s hrow f (Finset.mem_sdiff.mp hf').1)

theorem realizeRetainedSyntheticMember_edges (connector : List Vertex) (added : List (List Vertex))
    (h : Retained.SyntheticAccepted s connector added)
    (word : List Vertex) (hw : word ∈ connector :: added) :
    (B.realizeRetainedSyntheticMember A s hrow connector added h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

include hrow in
/-- The synthetic connector is fresh even for an old carrier containing x. -/
theorem retainedSyntheticConnector (connector : List Vertex) (added : List (List Vertex))
    (h : Retained.SyntheticAccepted s connector added) :
    ∃ M : G.Walk (A 1).val (A 2).val, M.IsPath ∧
      M.edges = (wordEdges connector).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v ∈ M.support, v = (A 1).val ∨ v = (A 2).val ∨
        v ∈ (Finset.univ.erase 0).map B.label := by
  let P := B.realizeRetainedSyntheticMember A s hrow connector added h connector (by simp)
  have hsup : P.walk.support = connector.map (B.threeLabel A) := NonemptyPath.ofWord_support _ _ _ _
  have hs : P.start = (A 1).val := by
    have he := congrArg List.head? hsup
    rw [List.head?_map, h.2.2.1] at he
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at he
    exact (Option.some.inj he).trans (B.threeLabel_anchor A 1)
  have ht : P.finish = (A 2).val := by
    have he := congrArg List.getLast? hsup
    rw [List.getLast?_map, h.2.2.2.1] at he
    rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support] at he
    exact (Option.some.inj he).trans (B.threeLabel_anchor A 2)
  have he := B.realizeRetainedSyntheticMember_edges A s hrow connector added h connector (by simp)
  have hf : ∀ v ∈ P.walk.support, v = (A 1).val ∨ v = (A 2).val ∨
      v ∈ (Finset.univ.erase 0).map B.label := by
    intro v hv
    rw [hsup] at hv
    obtain ⟨u,hu,huv⟩ := List.mem_map.mp hv
    rcases h.2.2.2.2.1 u hu with h1 | h2 | hp
    · exact Or.inl (huv.symm.trans (h1 ▸ B.threeLabel_anchor A 1))
    · exact Or.inr (Or.inl (huv.symm.trans (h2 ▸ B.threeLabel_anchor A 2)))
    · exact Or.inr (Or.inr (huv ▸ B.threeLabel_private A u hp))
  change P.walk.edges = _ at he
  generalize hP : P = Q at hs ht he hf
  obtain ⟨u,v,M,hM,_⟩ := Q
  dsimp only at hs ht he hf
  subst u v
  exact ⟨M,hM,he,hf⟩

end Gallai.WholeBowtie
