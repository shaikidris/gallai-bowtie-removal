/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorWords
import Gallai.Structure.ThreeAnchorRetainedRows

/-! # Retained passing certificates supply actual original-graph connectors -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true → (A j).val ∈ B.row i)

/-- Optional retained repair edges are required to be original when present. -/
def realizeRetainedMember (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (words : List (List Vertex)) (h : Accepted (targetEdges s ∪ retainedRepair repair) words)
    (word : List Vertex) (hw : word ∈ words) : NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.1 word hw).1)
    ((h.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      have hf' : f ∈ targetEdges s ∪ retainedRepair repair := by
        change f ∈ (targetEdges s ∪ retainedRepair repair).val
        rw [← h.2]
        exact List.mem_flatMap.mpr ⟨word, hw, hf⟩
      rcases Finset.mem_union.mp hf' with ht | hr
      · exact B.threeLabel_target_edge A s hrow f ht
      · cases repair with
        | false => simp [retainedRepair] at hr
        | true =>
          have heq : f = s(anchor 1, anchor 2) := by simpa [retainedRepair] using hr
          subst f
          simp only [Sym2.map_mk, B.threeLabel_anchor]
          exact hp rfl)

theorem realizeRetainedMember_support (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (words : List (List Vertex)) (h : Accepted (targetEdges s ∪ retainedRepair repair) words)
    (word : List Vertex) (hw : word ∈ words) :
    (B.realizeRetainedMember A s hrow repair hp words h word hw).walk.support =
      word.map (B.threeLabel A) := NonemptyPath.ofWord_support _ _ _ _

theorem realizeRetainedMember_edges (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (words : List (List Vertex)) (h : Accepted (targetEdges s ∪ retainedRepair repair) words)
    (word : List Vertex) (hw : word ∈ words) :
    (B.realizeRetainedMember A s hrow repair hp words h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

include hrow in
/-- A passing record supplies the nonempty connector, exact edges and the
survivor support restriction consumed by the retained through splice. -/
theorem retainedPassingConnector (repair : Bool)
    (hp : repair = true → G.Adj (A 1).val (A 2).val)
    (connector : List Vertex) (added : List (List Vertex))
    (h : RetainedPassingAccepted s repair connector added) :
    ∃ M : G.Walk (A 0).val (A 1).val, M.IsPath ∧ ¬ M.Nil ∧
      M.edges = (wordEdges connector).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v : B.StarSurvivor, v.val ∈ M.support →
        v.val = (A 0).val ∨ v.val = (A 1).val ∨ v.val = B.label 0 := by
  obtain ⟨_, _, hh, hl, hcore, hacc, _⟩ := h
  let P := B.realizeRetainedMember A s hrow repair hp (connector :: added) hacc
    connector (List.mem_cons_self ..)
  have hsupport : P.walk.support = connector.map (B.threeLabel A) :=
    B.realizeRetainedMember_support A s hrow repair hp _ hacc _ _
  have hs : P.start = (A 0).val := by
    have he := congrArg List.head? hsupport
    rw [List.head?_map, hh] at he
    rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at he
    exact (Option.some.inj he).trans (B.threeLabel_anchor A 0)
  have ht : P.finish = (A 1).val := by
    have he := congrArg List.getLast? hsupport
    rw [List.getLast?_map, hl] at he
    rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support] at he
    exact (Option.some.inj he).trans (B.threeLabel_anchor A 1)
  have he : P.walk.edges = (wordEdges connector).map (Sym2.map (B.threeLabel A)) :=
    B.realizeRetainedMember_edges A s hrow repair hp _ hacc _ _
  have hf : ∀ v : B.StarSurvivor, v.val ∈ P.walk.support →
      v.val = (A 0).val ∨ v.val = (A 1).val ∨ v.val = B.label 0 := by
    intro v hv
    rw [hsupport] at hv
    obtain ⟨u, hu, huv⟩ := List.mem_map.mp hv
    rcases hcore u hu with h0 | h1 | hc
    · exact Or.inl (huv.symm.trans (h0 ▸ B.threeLabel_anchor A 0))
    · exact Or.inr (Or.inl (huv.symm.trans (h1 ▸ B.threeLabel_anchor A 1)))
    · exact Or.inr (Or.inr (B.survivor_mem_vertices v (huv ▸ B.threeLabel_fresh A u hc)))
  generalize hP : P = Q at hs ht he hf
  obtain ⟨u, v, M, hM, hne⟩ := Q
  dsimp only at hs ht he hf
  subst u v
  exact ⟨M, hM, hne, he, hf⟩

end Gallai.WholeBowtie
