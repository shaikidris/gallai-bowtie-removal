/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Transport.ThreeAnchorWords

/-! # Interpret original-edge certificate words in the ambient graph -/

namespace Gallai.WholeBowtie

open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
variable (hrow : ∀ i j, (rowMask (s i)).val.testBit j.val = true →
  (A j).val ∈ B.row i)

include hrow in
/-- The augmented local target embeds in G when its repair edge is original. -/
theorem threeLabel_original_edge (p q : Fin 3) (hpq : G.Adj (A p).val (A q).val)
    (e : Sym2 Vertex) (he : e ∈ targetEdges s ∪ {s(anchor p, anchor q)}) :
    Sym2.map (B.threeLabel A) e ∈ G.edgeSet := by
  rcases Finset.mem_union.mp he with h | h
  · exact B.threeLabel_target_edge A s hrow e h
  · have heq := Finset.mem_singleton.mp h
    subst e
    simp only [Sym2.map_mk, B.threeLabel_anchor]
    exact hpq

/-- Every accepted word becomes a nonempty simple path, including words using
the original repair edge. -/
def realizeThreeOriginalMember (p q : Fin 3) (hpq : G.Adj (A p).val (A q).val)
    (words : List (List Vertex))
    (h : Accepted (targetEdges s ∪ {s(anchor p, anchor q)}) words)
    (word : List Vertex) (hw : word ∈ words) : NonemptyPath G :=
  NonemptyPath.ofWord (word.map (B.threeLabel A))
    (by simpa only [List.length_map] using (h.1 word hw).1)
    ((h.1 word hw).2.map (B.threeLabel_injective A)) (by
      intro e he
      change e ∈ wordEdges (word.map (B.threeLabel A)) at he
      rw [wordEdges_map] at he
      obtain ⟨f, hf, rfl⟩ := List.mem_map.mp he
      apply B.threeLabel_original_edge A s hrow p q hpq f
      change f ∈ (targetEdges s ∪ {s(anchor p, anchor q)}).val
      rw [← h.2]
      exact List.mem_flatMap.mpr ⟨word, hw, hf⟩)

/-- Interpretation retains the exact support. -/
theorem realizeThreeOriginalMember_support (p q : Fin 3)
    (hpq : G.Adj (A p).val (A q).val) (words : List (List Vertex))
    (h : Accepted (targetEdges s ∪ {s(anchor p, anchor q)}) words)
    (word : List Vertex) (hw : word ∈ words) :
    (B.realizeThreeOriginalMember A s hrow p q hpq words h word hw).walk.support =
      word.map (B.threeLabel A) := NonemptyPath.ofWord_support _ _ _ _

/-- Interpretation retains the exact mapped edge list. -/
theorem realizeThreeOriginalMember_edges (p q : Fin 3)
    (hpq : G.Adj (A p).val (A q).val) (words : List (List Vertex))
    (h : Accepted (targetEdges s ∪ {s(anchor p, anchor q)}) words)
    (word : List Vertex) (hw : word ∈ words) :
    (B.realizeThreeOriginalMember A s hrow p q hpq words h word hw).walk.edges =
      (wordEdges word).map (Sym2.map (B.threeLabel A)) := by
  change (NonemptyPath.ofWord _ _ _ _).walk.edges = _
  rw [NonemptyPath.ofWord_edges]
  exact wordEdges_map (B.threeLabel A) word

end Gallai.WholeBowtie
