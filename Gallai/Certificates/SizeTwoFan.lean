/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStar

/-! # Exact initial paths for the exceptional size-two Fan state

The two initial paths are disjoint from the retained pq spokes. Three edges
remain for addibility, rather than being asserted to be covered by a basic
reconstruction record. All statements here concern this finite local graph.
-/
namespace Gallai.Certificate.SizeTwo.Fan

open Star.Vertex
open scoped Finset

def state : CompletedStar.State := ![15,0,12,12,12]

def initialWords : List (List Star.Vertex) :=
  [[a,b,r,c,x,d,s], [a,x,r,d,c,s]]

def initialEdges : Finset (Sym2 Star.Vertex) :=
  (initialWords.flatMap wordEdges).toFinset

def retainedEdges : Finset (Sym2 Star.Vertex) := {s(x,p),s(x,q)}

def restoredEdges : Finset (Sym2 Star.Vertex) := {s(x,s),s(b,x),s(b,s)}

/-- The added paths are individually simple and partition their edge set. -/
theorem initial_accepted : Accepted initialEdges initialWords := by decide

/-- The retained auxiliary spokes never overlap either new path. -/
theorem initial_disjoint_retained : Disjoint initialEdges retainedEdges := by decide

/-- None of the three Fan edges has already been inserted. -/
theorem restored_disjoint_initial :
    Disjoint restoredEdges (retainedEdges ∪ initialEdges) := by decide

/-- The two initial paths and three restores exhaust the original local edges. -/
theorem target_partition : CompletedStar.targetEdges state =
    retainedEdges ∪ initialEdges ∪ restoredEdges := by decide

/-- Adding the two initial paths supplies exactly two endpoints at a and s. -/
theorem initial_endpoints (v : Star.Vertex) : endpoints initialWords v =
    (if v = a then 2 else 0) + (if v = s then 2 else 0) := by
  cases v <;> decide

/-- At the first recipient, only c and d can lack endpoints once a,p,q,r
have their required reserves. -/
theorem initial_hub_neighbors (v : Star.Vertex) :
    s(x,v) ∈ retainedEdges ∪ initialEdges ↔ v ∈ ({a,c,d,p,q,r} : Finset _) := by
  cases v <;> decide

/-- The second recipient initially has only a and r as neighbours. -/
theorem initial_b_neighbors (v : Star.Vertex) :
    s(b,v) ∈ retainedEdges ∪ initialEdges ↔ v ∈ ({a,r} : Finset _) := by
  cases v <;> decide

/-- The graph consisting only of the two added paths. -/
def initialGraph : SimpleGraph Star.Vertex := SimpleGraph.fromEdgeSet ↑initialEdges

theorem initialGraph_edges (e : Sym2 Star.Vertex) :
    e ∈ initialEdges ↔ e ∈ initialGraph.edgeSet := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    change s(u,v) ∈ initialEdges ↔ (SimpleGraph.fromEdgeSet ↑initialEdges).Adj u v
    rw [SimpleGraph.fromEdgeSet_adj]
    cases u <;> cases v <;> decide

/-- An actual decomposition, not merely a checked edge multiset. -/
def initialDecomposition : Decomposition initialGraph :=
  initial_accepted.toDecomposition initialGraph initialGraph_edges

theorem initialDecomposition_size : initialDecomposition.size = 2 := rfl

theorem initialDecomposition_endpoints (v : Star.Vertex) :
    initialDecomposition.endpointCount v =
      (if v = a then 2 else 0) + (if v = s then 2 else 0) := by
  rw [initialDecomposition, Accepted.toDecomposition_endpointCount]
  exact initial_endpoints v

end Gallai.Certificate.SizeTwo.Fan
