/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarAssignment

/-! # Realizing sparse completed-star words in the original graph

The four private labels and released hub are original bowtie vertices here,
not vertices added to a larger full-incidence graph. Only edges justified by
the original incidence rows may be used by a realized local word.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Interpret the nine local symbols in the original ambient graph. -/
def completedLabel (A : B.AnchorNumbering) : Star.Vertex → V
  | .x => B.label 0
  | .a => B.label 1
  | .b => B.label 2
  | .c => B.label 3
  | .d => B.label 4
  | .p => (A 0).val
  | .q => (A 1).val
  | .r => (A 2).val
  | .s => (A 3).val

theorem completedLabel_core (A : B.AnchorNumbering) (i : Fin 5) :
    B.completedLabel A (core i) = B.label i := by fin_cases i <;> rfl

theorem completedLabel_anchor (A : B.AnchorNumbering) (j : Fin 4) :
    B.completedLabel A (anchor j) = (A j).val := by fin_cases j <;> rfl

/-- The indexed terminal role has exactly the original released attachment. -/
theorem completed_terminal_boundary (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.TerminalIndex B.completedHub) :
    ((boundaries (profileInterface (Star.profileOf D B.completedHub)))[
      B.completedCarrierRoleEquiv D hfour (.inl i)]).map
        (B.completedLabel (B.carrierAnchorOrder D hfour)) =
      [(D.runNeighbor B.completedHub (.inl i)).val] := by
  simp only [B.completedCarrierRoleEquiv_terminal, terminalRole_boundary]
  simp only [List.map_cons, List.map_nil, B.completedLabel_anchor,
    B.carrierAnchorOrder_terminal]

/-- Both sides of an indexed through role belong to the same original carrier. -/
theorem completed_through_boundary (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.ThroughIndex B.completedHub) :
    ((boundaries (profileInterface (Star.profileOf D B.completedHub)))[
      B.completedCarrierRoleEquiv D hfour (.inr i)]).map
        (B.completedLabel (B.carrierAnchorOrder D hfour)) =
      [(D.runNeighbor B.completedHub (.inr (i, finTwoEquiv 0))).val,
        (D.runNeighbor B.completedHub (.inr (i, finTwoEquiv 1))).val] := by
  simp only [B.completedCarrierRoleEquiv_through, throughRole_boundary]
  simp only [List.map_cons, List.map_nil, B.completedLabel_anchor,
    B.carrierAnchorOrder_through]

/-- Local symbolic simplicity remains simplicity in the original graph. -/
theorem completedLabel_injective (A : B.AnchorNumbering) :
    Function.Injective (B.completedLabel A) := by
  have hc := B.label.injective
  have ha := Subtype.val_injective.comp A.injective
  have hs := B.label_ne_numberedAnchor A
  intro v w h
  cases v <;> cases w <;> simp only [completedLabel] at h
  all_goals first
    | rfl
    | exact False.elim (hs _ _ h)
    | exact False.elim (hs _ _ h.symm)
    | exact False.elim (by have he := hc h; omega)
    | exact False.elim (by have he := ha h; omega)

/-- Every allowed internal symbol is a bowtie vertex. -/
theorem completedLabel_fresh (A : B.AnchorNumbering) (v : Star.Vertex)
    (hv : v ∈ Star.fresh.toFinset) : B.completedLabel A v ∈ B.vertices := by
  cases v <;> simp only [Star.fresh, List.mem_toFinset, List.mem_cons,
    List.not_mem_nil, or_false] at hv
  all_goals first
    | contradiction
    | exact Finset.mem_map.mpr ⟨_, Finset.mem_univ _, rfl⟩

/-- The six fixed local edges are exactly edges of the original bowtie. -/
theorem completedLabel_core_edge (A : B.AnchorNumbering) (e : Sym2 Star.Vertex)
    (he : e ∈ coreEdges) : Sym2.map (B.completedLabel A) e ∈ G.edgeSet := by
  have hex : ∀ e : Sym2 Star.Vertex, e ∈ coreEdges →
      ∃ i j : Fin 5, bowtieGraph.Adj i j ∧ s(core i, core j) = e := by
    intro e
    induction e using Sym2.inductionOn with
    | hf u v => cases u <;> cases v <;> decide
  obtain ⟨i, j, hij, rfl⟩ := hex e he
  change G.Adj (B.completedLabel A (core i)) (B.completedLabel A (core j))
  rw [B.completedLabel_core, B.completedLabel_core]
  exact (B.adj_iff i j).mpr hij

/-- Sparse target-edge membership implies actual original adjacency. -/
theorem completedLabel_target_edge (A : B.AnchorNumbering) (e : Sym2 Star.Vertex)
    (he : e ∈ targetEdges (B.completedStarState A)) :
    Sym2.map (B.completedLabel A) e ∈ G.edgeSet := by
  rcases (mem_targetEdges _ _).mp he with he | ⟨i, j, hbit, rfl⟩
  · exact B.completedLabel_core_edge A e he
  · change G.Adj (B.completedLabel A (core i)) (B.completedLabel A (anchor j))
    rw [B.completedLabel_core, B.completedLabel_anchor]
    exact (B.completedStarState_bit A i j).mp hbit

/-- Conversely, every original edge incident with a bowtie label occurs in
the same sparse local target. No original spoke is silently omitted. -/
theorem completedLabel_target_covers (A : B.AnchorNumbering) (i : Fin 5) (v : V)
    (ha : G.Adj (B.label i) v) :
    ∃ e ∈ targetEdges (B.completedStarState A),
      Sym2.map (B.completedLabel A) e = s(B.label i, v) := by
  by_cases hv : v ∈ B.vertices
  · obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hv
    have hj := (B.adj_iff i j).mp ha
    have he : s(core i, core j) ∈ coreEdges :=
      (by decide : ∀ i j : Fin 5, bowtieGraph.Adj i j → s(core i, core j) ∈ coreEdges) i j hj
    refine ⟨s(core i, core j), (mem_targetEdges _ _).mpr (Or.inl he), ?_⟩
    change s(B.completedLabel A (core i), B.completedLabel A (core j)) = _
    rw [B.completedLabel_core, B.completedLabel_core]
  · have hA : v ∈ B.anchors := (B.mem_anchors _).mpr ⟨i, (B.mem_row i _).mpr ⟨ha, hv⟩⟩
    obtain ⟨j, hj⟩ := A.surjective ⟨v, hA⟩
    have hjval : (A j).val = v := congrArg Subtype.val hj
    have hb : (B.completedStarState A i).val.testBit j.val = true :=
      (B.completedStarState_bit A i j).mpr (by rw [hjval]; exact ha)
    refine ⟨s(core i, anchor j), (mem_targetEdges _ _).mpr (Or.inr ⟨i, j, hb, rfl⟩), ?_⟩
    change s(B.completedLabel A (core i), B.completedLabel A (anchor j)) = _
    rw [B.completedLabel_core, B.completedLabel_anchor, hjval]

/-- The graph of original local edges embeds into G, not merely its expansion. -/
def completedLocalHom (A : B.AnchorNumbering) : graph (B.completedStarState A) →g G where
  toFun := B.completedLabel A
  map_rel' {u v} h :=
    B.completedLabel_target_edge A s(u, v) ((graph_edges _ _).mpr h)

/-- Interpret one accepted sparse record word as a nonempty simple path of G. -/
noncomputable def realizeCompletedWord (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) : NonemptyPath G := by
  let P := h.realize (graph (B.completedStarState A)) (fun e he => (graph_edges _ e).mp he) i
  exact {
    start := B.completedLabel A P.start
    finish := B.completedLabel A P.finish
    walk := P.walk.map (B.completedLocalHom A)
    isPath := P.isPath.map (B.completedLabel_injective A)
    nonempty := fun hn => P.nonempty ((SimpleGraph.Walk.nil_map_iff (B.completedLocalHom A)).mp hn) }

/-- The interpreted word has exactly its original symbolic support image. -/
theorem realizeCompletedWord_support (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) :
    (B.realizeCompletedWord A words h i).walk.support = words[i].map (B.completedLabel A) := by
  let P := h.realize (graph (B.completedStarState A)) (fun e he => (graph_edges _ e).mp he) i
  exact (SimpleGraph.Walk.support_map (B.completedLocalHom A) P.walk).trans
    (congrArg (List.map (B.completedLabel A)) (h.realize_support _ _ i))

/-- Edge multiplicities are transported without adding any completion spoke. -/
theorem realizeCompletedWord_edges (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) :
    (B.realizeCompletedWord A words h i).walk.edges =
      (Certificate.wordEdges words[i]).map (Sym2.map (B.completedLabel A)) := by
  let P := h.realize (graph (B.completedStarState A)) (fun e he => (graph_edges _ e).mp he) i
  exact (SimpleGraph.Walk.edges_map (B.completedLocalHom A) P.walk).trans
    (congrArg (List.map (Sym2.map (B.completedLabel A))) (h.realize_edges _ _ i))

/-- A terminal word can meet an old surviving vertex only at its attachment
or at the released hub. No avoidance of other anchors is assumed of the old path. -/
theorem realizeCompletedWord_terminal_old (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i])
    (v : B.StarSurvivor) (hv : v.val ∈ (B.realizeCompletedWord A words h i).walk.support) :
    v.val = (A j).val ∨ v.val = B.label 0 := by
  rw [B.realizeCompletedWord_support] at hv
  obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
  rcases Certificate.compatible_single_support hr hw with rfl | hf
  · exact Or.inl (he.symm.trans (B.completedLabel_anchor A j))
  · exact Or.inr (B.survivor_mem_vertices v (he ▸ B.completedLabel_fresh A w hf))

/-- The same old-vertex restriction for a two-attachment connector. -/
theorem realizeCompletedWord_through_old (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j k : Fin 4)
    (hr : Certificate.Compatible [anchor j, anchor k] Star.fresh.toFinset words[i])
    (v : B.StarSurvivor) (hv : v.val ∈ (B.realizeCompletedWord A words h i).walk.support) :
    v.val = (A j).val ∨ v.val = (A k).val ∨ v.val = B.label 0 := by
  rw [B.realizeCompletedWord_support] at hv
  obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
  rcases Certificate.compatible_pair_support hr hw with rfl | rfl | hf
  · exact Or.inl (he.symm.trans (B.completedLabel_anchor A j))
  · exact Or.inr (Or.inl (he.symm.trans (B.completedLabel_anchor A k)))
  · exact Or.inr (Or.inr (B.survivor_mem_vertices v (he ▸ B.completedLabel_fresh A w hf)))

end Gallai.WholeBowtie
