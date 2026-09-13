/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorLabels
import Gallai.Certificates.WordRelabel

/-! # Accepted three-anchor words become original-graph simple paths -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
  (A j).val ∈ B.row i)

/-- Interpret a word occurrence using exactly the certified local edges. -/
def realizeThreeMember (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words) :
    NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.1 word hw).1)
    ((h.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      apply B.threeLabel_target_edge A s hrow f
      change f ∈ (targetEdges s).val
      rw [← h.2]
      exact List.mem_flatMap.mpr ⟨word, hw, hf⟩)

/-- Word interpretation retains the full vertex list. -/
theorem realizeThreeMember_support (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words) :
    (B.realizeThreeMember A s hrow words h word hw).walk.support =
      word.map (B.threeLabel A) :=
  NonemptyPath.ofWord_support _ _ _ _

/-- Word interpretation retains each edge occurrence under the injective label map. -/
theorem realizeThreeMember_edges (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words) :
    (B.realizeThreeMember A s hrow words h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

/-- All finite connector support guarantees survive interpretation. -/
theorem realizeThreeMember_core_support (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words)
    (p q : Fin 3) (hcore : ∀ v ∈ word, v = anchor p ∨ v = anchor q ∨ v.val < 5) :
    ∀ v ∈ (B.realizeThreeMember A s hrow words h word hw).walk.support,
      v = (A p).val ∨ v = (A q).val ∨ v ∈ B.vertices := by
  intro v hv
  rw [B.realizeThreeMember_support] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  rcases hcore u hu with hp | hq | hf
  · exact Or.inl (hp ▸ B.threeLabel_anchor A p)
  · exact Or.inr (Or.inl (hq ▸ B.threeLabel_anchor A q))
  · exact Or.inr (Or.inr (B.threeLabel_fresh A u hf))

/-- The certified first anchor is the actual start of the interpreted carrier. -/
theorem realizeThreeMember_start (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words)
    (p : Fin 3) (hp : word.head? = some (anchor p)) :
    (B.realizeThreeMember A s hrow words h word hw).start = (A p).val := by
  have hs := congrArg List.head?
    (B.realizeThreeMember_support A s hrow words h word hw)
  rw [List.head?_map, hp] at hs
  rw [List.head?_eq_some_head (by simp), SimpleGraph.Walk.head_support] at hs
  exact (Option.some.inj hs).trans (B.threeLabel_anchor A p)

/-- The certified last anchor is the actual finish of the interpreted carrier. -/
theorem realizeThreeMember_finish (words : List (List Vertex))
    (h : Accepted (targetEdges s) words) (word : List Vertex) (hw : word ∈ words)
    (q : Fin 3) (hq : word.getLast? = some (anchor q)) :
    (B.realizeThreeMember A s hrow words h word hw).finish = (A q).val := by
  have hs := congrArg List.getLast?
    (B.realizeThreeMember_support A s hrow words h word hw)
  rw [List.getLast?_map, hq] at hs
  rw [List.getLast?_eq_some_getLast (by simp), SimpleGraph.Walk.getLast_support] at hs
  exact (Option.some.inj hs).trans (B.threeLabel_anchor A q)

include hrow in
/-- A synthetic record supplies a correctly typed original-graph connector,
with the exact edge list and the freshness needed by repair-edge transport. -/
theorem syntheticThreeConnector (p q : Fin 3) (connector : List Vertex)
    (added : List (List Vertex)) (h : SyntheticAccepted s p q connector added) :
    ∃ M : G.Walk (A p).val (A q).val, M.IsPath ∧
      M.edges = (wordEdges connector).map (Sym2.map (B.threeLabel A)) ∧
      ∀ v ∈ M.support, v = (A p).val ∨ v = (A q).val ∨ v ∈ B.vertices := by
  let P := B.realizeThreeMember A s hrow (connector :: added) h.2.2.2.2.2.1
    connector (List.mem_cons_self ..)
  have hs : P.start = (A p).val :=
    B.realizeThreeMember_start A s hrow _ _ _ _ p h.2.2.1
  have ht : P.finish = (A q).val :=
    B.realizeThreeMember_finish A s hrow _ _ _ _ q h.2.2.2.1
  have he : P.walk.edges =
      (wordEdges connector).map (Sym2.map (B.threeLabel A)) :=
    B.realizeThreeMember_edges A s hrow _ _ _ _
  have hf : ∀ v ∈ P.walk.support,
      v = (A p).val ∨ v = (A q).val ∨ v ∈ B.vertices :=
    B.realizeThreeMember_core_support A s hrow _ _ _ _ p q h.2.2.2.2.1
  generalize hP : P = Q at hs ht he hf
  obtain ⟨u, v, M, hM, _⟩ := Q
  dsimp only at hs ht he hf
  subst u v
  exact ⟨M, hM, he, hf⟩

end Gallai.WholeBowtie
