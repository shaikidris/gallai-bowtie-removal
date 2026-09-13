/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.EvenSubgraph
import Lean.Elab.Tactic.Omega

/-!
# Whole bowties and incidence-row parity

A whole bowtie is an actual component of the induced even graph with exactly
the six prescribed edges. Oddness of its external anchors and evenness of
its incidence rows are consequences, not fields of the input structure.
-/

namespace Gallai

open scoped Finset

/-- The six-edge bowtie, with hub zero and private pairs one/two and three/four. -/
abbrev bowtieGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)}

/-- The hub has internal degree four and every private vertex internal degree two. -/
theorem bowtieGraph_degree (i : Fin 5) : bowtieGraph.degree i = if i = 0 then 4 else 2 := by
  revert i
  decide

universe u

variable {V : Type u} [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]

/-- A labelled component of the original even graph with exactly the bowtie shape. -/
structure WholeBowtie where
  /-- The five distinct original vertices, with the centre labelled zero. -/
  label : Fin 5 ↪ V
  /-- The whole connected component in the induced even graph. -/
  component : (evenSubgraph G).ConnectedComponent
  /-- No other even vertices belong to this component. -/
  component_vertices : evenComponentVertices component = Set.range label
  /-- There are exactly the prescribed internal edges, with no extra chords. -/
  adj_iff : ∀ i j, G.Adj (label i) (label j) ↔ bowtieGraph.Adj i j

namespace WholeBowtie

variable {G} (B : WholeBowtie G)

/-- The five original vertices of the bowtie. -/
def vertices : Finset V := Finset.univ.map B.label

/-- Finite membership coincides with membership in the whole even component. -/
theorem mem_vertices (v : V) :
    v ∈ B.vertices ↔ v ∈ evenComponentVertices B.component := by
  rw [B.component_vertices]
  simp [vertices]

/-- Every labelled bowtie vertex belongs to its whole component. -/
theorem label_mem_component (i : Fin 5) :
    B.label i ∈ evenComponentVertices B.component := by
  rw [B.component_vertices]
  exact ⟨i, rfl⟩

/-- Original ordinary degrees of all five vertices are even. -/
theorem even_degree_label (i : Fin 5) : Even (G.degree (B.label i)) :=
  even_of_mem_evenComponent B.component (B.label_mem_component i)

/-- The bowtie has exactly five vertices. -/
theorem card_vertices : #B.vertices = 5 := by simp [vertices]

variable [DecidableEq V]

/-- The complete external incidence row at a labelled vertex. -/
def row (i : Fin 5) : Finset V := G.neighborFinset (B.label i) \ B.vertices

/-- The complete external neighbourhood of the five bowtie vertices. -/
def anchors : Finset V := Finset.univ.biUnion B.row

/-- Row membership is original adjacency together with being outside the bowtie. -/
@[simp] theorem mem_row (i : Fin 5) (v : V) :
    v ∈ B.row i ↔ G.Adj (B.label i) v ∧ v ∉ B.vertices := by
  simp [row]

/-- An anchor is incident to at least one of the five rows. -/
@[simp] theorem mem_anchors (v : V) : v ∈ B.anchors ↔ ∃ i, v ∈ B.row i := by
  simp [anchors]

/-- Every anchor is odd in the original graph, by whole-component closure. -/
theorem odd_degree_anchor {v : V} (hv : v ∈ B.anchors) : Odd (G.degree v) := by
  obtain ⟨i, hi⟩ := (B.mem_anchors v).mp hv
  obtain ⟨hadj, hout⟩ := (B.mem_row i v).mp hi
  exact odd_of_adj_evenComponent B.component (B.label_mem_component i) hadj
    (fun h => hout ((B.mem_vertices v).mpr h))

/-- External rows equal the neighbour/anchor intersections used in the manuscript. -/
theorem row_eq_inter_anchors (i : Fin 5) :
    B.row i = G.neighborFinset (B.label i) ∩ B.anchors := by
  ext v
  constructor
  · intro h
    exact Finset.mem_inter.mpr ⟨(G.mem_neighborFinset _ _).mpr ((B.mem_row i v).mp h).1,
      (B.mem_anchors v).mpr ⟨i, h⟩⟩
  · intro h
    obtain ⟨ha, hA⟩ := Finset.mem_inter.mp h
    obtain ⟨j, hj⟩ := (B.mem_anchors v).mp hA
    exact (B.mem_row i v).mpr ⟨(G.mem_neighborFinset _ _).mp ha, ((B.mem_row j v).mp hj).2⟩

/-- The internal neighbour set is the injective image of the fixed bowtie neighbours. -/
theorem internal_neighbors (i : Fin 5) :
    G.neighborFinset (B.label i) ∩ B.vertices =
      (bowtieGraph.neighborFinset i).map B.label := by
  ext v
  constructor
  · intro h
    obtain ⟨ha, hb⟩ := Finset.mem_inter.mp h
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hb
    exact Finset.mem_map.mpr ⟨j,
      (bowtieGraph.mem_neighborFinset _ _).mpr
        ((B.adj_iff i j).mp ((G.mem_neighborFinset _ _).mp ha)), rfl⟩
  · intro h
    obtain ⟨j, hj, rfl⟩ := Finset.mem_map.mp h
    exact Finset.mem_inter.mpr
      ⟨(G.mem_neighborFinset _ _).mpr
        ((B.adj_iff i j).mpr ((bowtieGraph.mem_neighborFinset _ _).mp hj)),
        Finset.mem_map.mpr ⟨j, Finset.mem_univ j, rfl⟩⟩

/-- The exact ordinary-degree partition into external and internal incidences. -/
theorem card_row_add_internal_degree (i : Fin 5) :
    #(B.row i) + bowtieGraph.degree i = G.degree (B.label i) := by
  have h := Finset.card_sdiff_add_card_inter (G.neighborFinset (B.label i)) B.vertices
  rw [B.internal_neighbors i] at h
  simpa [row] using h

/-- Every external incidence row has even cardinality. -/
theorem even_card_row (i : Fin 5) : Even #(B.row i) := by
  have he := B.even_degree_label i
  have hsize := B.card_row_add_internal_degree i
  rw [bowtieGraph_degree] at hsize
  rw [Nat.even_iff] at he ⊢
  split_ifs at hsize <;> omega

end WholeBowtie
end Gallai
