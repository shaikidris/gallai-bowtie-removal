/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Combinatorics.SimpleGraph.Paths
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected
import Mathlib.Combinatorics.SimpleGraph.Star
import Mathlib.Algebra.Ring.Parity
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Find

/-!
# Bowtie removal in Gallai path decompositions

The selected statements concern finite simple graphs. A decomposition partitions
edges into nonempty simple paths; isolated vertices contribute no path. The
even subgraph is induced by the vertices whose degrees in the original graph
are even. A whole bowtie is an entire component of that induced subgraph,
consisting of two triangles meeting in one centre.

Theorem A removes one such component under one of four sufficient conditions.
Theorem B expands a degree-four star at a cost of exactly two paths and records
the endpoint multiplicities; the four-leaf star shows this cost is sharp.
Theorem C composes a stated subclass of removals for an arbitrary finite family,
allowing shared odd anchors. The two corollaries describe the small-odd kernel
and a necessary counting boundary for a counterexample within that kernel.

These are partial structural results, not the unrestricted two-exception
conjecture. The holes in the six advertised statements are intentional Challenge
holes; the separate Solution must prove exactly these statements. Definitions
below are explicit and import no project proof code.
-/

namespace Gallai
open scoped Finset symmDiff
universe u
variable {V : Type u}

/-- A simple oriented path with at least one edge. -/
structure NonemptyPath (G : SimpleGraph V) where
  /-- Initial vertex. -/
  start : V
  /-- Final vertex. -/
  finish : V
  /-- The underlying walk. -/
  walk : G.Walk start finish
  /-- No repeated vertices. -/
  isPath : walk.IsPath
  /-- The walk has an edge. -/
  nonempty : ¬ walk.Nil

/-- An indexed family covering each graph edge exactly once. -/
structure Decomposition (G : SimpleGraph V) where
  /-- Number of paths. -/
  size : ℕ
  /-- The indexed simple paths. -/
  path : Fin size → NonemptyPath G
  /-- Each edge occurs on a unique path. -/
  covers : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (path i).walk.edges

/-- Number of path ends at a vertex. -/
def Decomposition.endpointCount {G : SimpleGraph V} [DecidableEq V]
    (D : Decomposition G) (v : V) : ℕ :=
  ∑ i : Fin D.size, ((if (D.path i).start = v then 1 else 0) +
    (if (D.path i).finish = v then 1 else 0))

/-- Existence of a path partition within the given integer budget. -/
def HasPathBudget (G : SimpleGraph V) (k : ℕ) : Prop :=
  ∃ D : Decomposition G, D.size ≤ k

section PathBudgetSupport
variable {G : SimpleGraph V}
namespace Decomposition
universe v
/-- Reindex an exact finite path family, matching the proof-library definition. -/
noncomputable def ofFamily {I : Type v} [Fintype I] (paths : I → NonemptyPath G)
    (hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges) : Decomposition G where
  size := Fintype.card I
  path := fun i => paths ((Fintype.equivFin I).symm i)
  covers := by
    intro e he
    obtain ⟨i, hi, hu⟩ := hcover e he
    refine ⟨Fintype.equivFin I i, ?_, ?_⟩
    · have hp : paths ((Fintype.equivFin I).symm (Fintype.equivFin I i)) = paths i :=
        congrArg paths ((Fintype.equivFin I).symm_apply_apply i)
      exact (congrArg (fun P : NonemptyPath G => e ∈ P.walk.edges) hp).mpr hi
    intro j hj
    apply (Fintype.equivFin I).symm.injective
    simpa using hu ((Fintype.equivFin I).symm j) hj
end Decomposition

/-- Each edge is the exact edge list of a nonempty simple path. -/
theorem exists_singleEdgePath (e : Sym2 V) (he : e ∈ G.edgeSet) :
    ∃ P : NonemptyPath G, P.walk.edges = [e] := by
  induction e using Sym2.ind with
  | _ a b =>
    have hab : G.Adj a b := he
    refine ⟨⟨a, b, .cons hab .nil, ?_, ?_⟩, by simp⟩
    · simp [SimpleGraph.Walk.cons_isPath_iff, hab.ne]
    · simp
end PathBudgetSupport

/-- Every finite graph admits a decomposition, taking each edge separately. -/
theorem exists_pathBudget [Fintype V] (G : SimpleGraph V) :
    ∃ k, HasPathBudget G k := by
  classical
  let paths (e : G.edgeSet) : NonemptyPath G :=
    (exists_singleEdgePath (G := G) e.val e.property).choose
  have hedges (e : G.edgeSet) : (paths e).walk.edges = [e.val] :=
    (exists_singleEdgePath (G := G) e.val e.property).choose_spec
  have hcover : ∀ e ∈ G.edgeSet, ∃! i, e ∈ (paths i).walk.edges := by
    intro e he
    refine ⟨⟨e, he⟩, ?_, ?_⟩
    · simp [hedges]
    · intro i hi
      simp only [hedges, List.mem_singleton] at hi
      exact Subtype.ext hi.symm
  let D := Decomposition.ofFamily paths hcover
  exact ⟨D.size, D, le_rfl⟩

/-- The least path budget. Existence above makes this a genuine minimum. -/
noncomputable def pathNumber [Fintype V] (G : SimpleGraph V) : ℕ := by
  classical
  exact Nat.find (exists_pathBudget G)

section EvenGraph
variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- Original even-degree vertices, including isolates. -/
abbrev evenVertices : Set V := {v | Even (G.degree v)}
/-- The graph induced by those vertices. -/
abbrev evenSubgraph : SimpleGraph (evenVertices G) := G.induce (evenVertices G)
/-- Original neighbours of original even degree. -/
def evenNeighbors (v : V) : Finset V :=
  (G.neighborFinset v).filter fun w => Even (G.degree w)
/-- E-degree: the number of even neighbours. -/
def eDegree (v : V) : ℕ := #(evenNeighbors G v)
/-- Component support viewed in the original vertex type. -/
def evenComponentVertices {G : SimpleGraph V} [DecidableRel G.Adj]
    (K : (evenSubgraph G).ConnectedComponent) : Set V :=
  Subtype.val '' K.supp
end EvenGraph

/-- Two triangles with common centre zero. -/
abbrev bowtieGraph : SimpleGraph (Fin 5) :=
  SimpleGraph.fromEdgeSet {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)}

variable [Fintype V] (G : SimpleGraph V) [DecidableRel G.Adj]
/-- A whole connected component of the even graph with exactly the bowtie shape. -/
structure WholeBowtie where
  /-- Five distinct vertices; zero labels the centre. -/
  label : Fin 5 ↪ V
  /-- The entire even component. -/
  component : (evenSubgraph G).ConnectedComponent
  /-- No additional even vertices in this component. -/
  component_vertices : evenComponentVertices component = Set.range label
  /-- Exactly the six internal bowtie edges. -/
  adj_iff : ∀ i j, G.Adj (label i) (label j) ↔ bowtieGraph.Adj i j

namespace WholeBowtie
variable {G} (B : WholeBowtie G)
/-- The five bowtie vertices. -/
def vertices : Finset V := Finset.univ.map B.label
variable [DecidableEq V]
/-- External neighbours of a labelled vertex. -/
def row (i : Fin 5) : Finset V := G.neighborFinset (B.label i) \ B.vertices
/-- All external neighbours of the bowtie. -/
def anchors : Finset V := Finset.univ.biUnion B.row
/-- Private vertices with nonempty external rows. -/
theorem activePrivate._proof_1 : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (4 + 1) :=
  Nat.instNeZeroSucc
attribute [local instance] activePrivate._proof_1
def activePrivate {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G) : Finset (Fin 5) :=
  Finset.univ.filter (fun i => i ≠ 0 ∧ (B.row i).Nonempty)
attribute [-instance] activePrivate._proof_1
/-- Number of active private vertices, not number of external edges. -/
def activity {V : Type u} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G) : ℕ := #B.activePrivate
/-- Anchors having odd total incidence with the five bowtie vertices. -/
theorem syndrome._proof_1 : @NeZero Nat (@Zero.ofOfNat0 Nat (instOfNatNat (nat_lit 0))) (4 + 1) :=
  Nat.instNeZeroSucc
attribute [local instance] syndrome._proof_1
def syndrome {V : Type u} [DecidableEq V] [Fintype V]
    {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G) : Finset V :=
  B.row 0 ∆ (B.row 1 ∆ (B.row 2 ∆ (B.row 3 ∆ B.row 4)))
attribute [-instance] syndrome._proof_1
end WholeBowtie

namespace TwoBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
/-- Two disjoint whole bowties and subcubic residual even vertices. -/
def Kernel (X Y : WholeBowtie G) : Prop :=
  Disjoint X.vertices Y.vertices ∧
  ∀ v, Even (G.degree v) → v ∉ X.vertices → v ∉ Y.vertices → eDegree G v ≤ 3
/-- Original odd-degree vertices. -/
def oddVertices (G : SimpleGraph V) [DecidableRel G.Adj] : Finset V :=
  Finset.univ.filter fun v => Odd (G.degree v)
end TwoBowtie
end Gallai

namespace Gallai.Star
universe u
variable {V : Type u}
/-- The two private edges are the pairs zero/one and two/three. -/
def privateAdj (i j : Fin 4) : Prop := i.val / 2 = j.val / 2 ∧ i ≠ j
/-- Retain all old edges; add four vertices adjacent to the hub and each old
neighbour of the hub, together with the two private edges. -/
def expansion (H : SimpleGraph V) (x : V) : SimpleGraph (V ⊕ Fin 4) where
  Adj
    | .inl v, .inl w => H.Adj v w
    | .inl v, .inr _ => v = x ∨ H.Adj x v
    | .inr _, .inl w => w = x ∨ H.Adj x w
    | .inr i, .inr j => privateAdj i j
  symm := by
    constructor
    intro v w h
    cases v <;> cases w
    · exact H.adj_symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro v
    cases v with
    | inl v => exact H.irrefl
    | inr i => exact fun h => h.2 rfl
end Gallai.Star

namespace Gallai.Palomar
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Theorem A. A whole bowtie with one other possible E-degree exception is
removable under any of the four displayed alternatives. The other exception
is exposed twice; at odd order the same witness exposes the centre twice. -/
theorem theoremA (B : WholeBowtie G) (hc : G.Connected) (y : V)
    (hyout : y ∉ B.vertices) (hy : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3)
    (hcase : B.anchors.card ≤ 4 ∨ B.activity ≤ 2 ∨
      (∃ w ∈ B.row 0, ∀ v, G.Adj w v → Even (G.degree v) → v = B.label 0 ∨ v = y) ∨
      Odd (Fintype.card V)) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount y ∧
      (Odd (Fintype.card V) → 2 ≤ P.endpointCount (B.label 0)) := by
  sorry

/-- Theorem B. Every decomposition lifts after expansion at a degree-four hub
with exactly two additional paths and the full displayed endpoint profile. -/
theorem expansion (D : Decomposition G) (x : V) (hd : G.degree x = 4) :
    ∃ E : Decomposition (Star.expansion G x), E.size = D.size + 2 ∧
      (∀ v, v ≠ x → E.endpointCount (Sum.inl v) = D.endpointCount v) ∧
      (D.endpointCount x = 0 → E.endpointCount (Sum.inl x) = 0) ∧
      (D.endpointCount x = 2 → E.endpointCount (Sum.inl x) = 2) ∧
      (D.endpointCount x = 4 → E.endpointCount (Sum.inl x) = 0) := by
  sorry

/-- Sharpness: the four-leaf star needs two paths, and its expansion needs four. -/
theorem expansionSharp :
    pathNumber (SimpleGraph.starGraph (0 : Fin 5)) = 2 ∧
      pathNumber (Star.expansion (SimpleGraph.starGraph (0 : Fin 5)) 0) = 4 := by
  sorry

/-- Theorem C. Any finite family of disjoint supported whole bowties can be
removed jointly. Shared anchors are allowed. One optional original even vertex
outside the family can be exposed twice on the resulting bounded witness. -/
theorem theoremC (hc : G.Connected) (t : ℕ) (Bs : Fin t → WholeBowtie G)
    (designated : Option V)
    (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
    (hs : ∀ i, (Bs i).activity ≤ 2 ∨ (Bs i).anchors.card ≤ 3 ∨
      ((Bs i).anchors.card = 4 ∧
        ((Bs i).syndrome = ∅ ∨ (Bs i).syndrome = (Bs i).anchors)))
    (hy : ∀ y ∈ designated, Even (G.degree y) ∧ 0 < G.degree y ∧
      ∀ i, y ∉ (Bs i).vertices)
    (hcap : ∀ v, Even (G.degree v) → (∀ i, v ∉ (Bs i).vertices) →
      (∀ y ∈ designated, v ≠ y) → eDegree G v ≤ 3) :
    ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
      ∀ y ∈ designated, 2 ≤ D.endpointCount y := by
  sorry

/-- Corollary A1. With at most four odd vertices in the two-bowtie kernel,
either prescribed centre can be exposed twice. Witnesses may differ. -/
theorem corollaryA1 {X Y : WholeBowtie G} (hc : G.Connected)
    (h : TwoBowtie.Kernel X Y) (ho : (TwoBowtie.oddVertices G).card ≤ 4) :
    ∀ z ∈ ({X.label 0, Y.label 0} : Finset V),
      ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2 ∧
        2 ≤ D.endpointCount z := by
  sorry

/-- Corollary A2. A counterexample within the two-bowtie kernel must have five
anchors at each bowtie, six odd vertices and order at least sixteen. At order
sixteen there are no other even vertices and at least four shared anchors. -/
theorem corollaryA2 {X Y : WholeBowtie G} (hc : G.Connected)
    (h : TwoBowtie.Kernel X Y)
    (hn : ¬ ∃ D : Decomposition G, D.size ≤ (Fintype.card V + 1) / 2) :
    5 ≤ X.anchors.card ∧ 5 ≤ Y.anchors.card ∧
    6 ≤ (TwoBowtie.oddVertices G).card ∧ 16 ≤ Fintype.card V ∧
    (Fintype.card V = 16 →
      (∀ v, Even (G.degree v) → v ∈ X.vertices ∪ Y.vertices) ∧
      4 ≤ (X.anchors ∩ Y.anchors).card) := by
  sorry
end Gallai.Palomar
