/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.RecordSoundness
import Gallai.Certificates.Star

/-! # Completed-star catalogue schema

The five rows use the catalogue order x,a,b,c,d and the four bit positions
use p,q,r,s. Target edges are original row incidences, not the completed
auxiliary spokes. This adapter does not assert symmetry or universe coverage.
-/

namespace Gallai.Certificate.CompletedStar

open Star.Vertex

/-- Five four-bit incidence rows; no admissibility is assumed by this type. -/
abbrev State := Fin 5 → Fin 16

/-- Core labels in the JSON row order. -/
def core (i : Fin 5) : Star.Vertex := ![x, a, b, c, d] i

/-- Anchor labels in increasing bit order. -/
def anchor (j : Fin 4) : Star.Vertex := ![p, q, r, s] j

/-- The six bowtie edges, before any anchor incidence is added. -/
def coreEdges : Finset (Sym2 Star.Vertex) :=
  {s(x, a), s(x, b), s(a, b), s(x, c), s(x, d), s(c, d)}

/-- Exactly the original local edges specified by the five row masks. -/
def targetEdges (state : State) : Finset (Sym2 Star.Vertex) :=
  coreEdges ∪ (Finset.univ.filter (fun ij : Fin 5 × Fin 4 =>
    (state ij.1).val.testBit ij.2.val)).image (fun ij => s(core ij.1, anchor ij.2))

/-- Membership exposes the row and bit that justify every noncore edge. -/
theorem mem_targetEdges (state : State) (e : Sym2 Star.Vertex) :
    e ∈ targetEdges state ↔ e ∈ coreEdges ∨
      ∃ i j, (state i).val.testBit j.val = true ∧ s(core i, anchor j) = e := by
  simp [targetEdges]

/-- All possible targets lie inside the full 26-edge local star. -/
theorem targetEdges_subset (state : State) :
    targetEdges state ⊆ Star.activeEdges.toFinset := by
  intro e he
  rcases (mem_targetEdges state e).mp he with he | ⟨i, j, _, rfl⟩
  · have h : coreEdges ⊆ Star.activeEdges.toFinset := by decide
    exact h he
  · have h : ∀ i j, s(core i, anchor j) ∈ Star.activeEdges.toFinset := by decide
    exact h i j

/-- The simple graph realized by the local original-edge specification. -/
def graph (state : State) : SimpleGraph Star.Vertex :=
  SimpleGraph.fromEdgeSet ↑(targetEdges state)

/-- No edge is lost to loop suppression in the simple-graph constructor. -/
theorem graph_edges (state : State) (e : Sym2 Star.Vertex) :
    e ∈ targetEdges state ↔ e ∈ (graph state).edgeSet := by
  induction e using Sym2.inductionOn with
  | hf u v =>
    change _ ↔ (SimpleGraph.fromEdgeSet ↑(targetEdges state)).Adj u v
    rw [SimpleGraph.fromEdgeSet_adj]
    constructor
    · intro he
      refine ⟨he, ?_⟩
      have hn : ∀ u v, s(u, v) ∈ Star.activeEdges.toFinset → u ≠ v := by
        intro u v
        cases u <;> cases v <;> decide
      exact hn u v (targetEdges_subset state he)
    · exact And.left

/-- The ten ordered endpoint interfaces used by the completed-star catalogue. -/
def boundaries (i : Fin 10) : List (List Star.Vertex) :=
  ![[[p, q], [r, s]], [[p, r], [q, s]], [[p, s], [q, r]],
    [[p], [q], [r, s]], [[p], [r], [q, s]], [[p], [s], [q, r]],
    [[q], [r], [p, s]], [[q], [s], [p, r]], [[r], [s], [p, q]],
    [[p], [q], [r], [s]]] i

/-- Every role permits only released or private vertices away from its anchors. -/
def roles (i : Fin 10) : List (List Star.Vertex × Finset Star.Vertex) :=
  (boundaries i).map (fun boundary => (boundary, Star.fresh.toFinset))

/-- Every interface uses each anchor exactly once as a boundary occurrence. -/
theorem boundary_count (i : Fin 10) (v : Star.Vertex) :
    (boundaries i).flatten.count v = if v ∈ Star.anchors then 1 else 0 := by
  cases v <;> revert i <;> decide

/-- Acceptance of a completed-star record includes its exact ordered roles. -/
def AcceptedRecord (state : State) (i : Fin 10)
    (replacements added : List (List Star.Vertex)) : Prop :=
  RecordAccepted (targetEdges state) (roles i) replacements added 2
    Star.anchors.toFinset (fun v => (boundaries i).flatten.count v)

instance (state : State) (i : Fin 10) (replacements added : List (List Star.Vertex)) :
    Decidable (AcceptedRecord state i replacements added) := by
  unfold AcceptedRecord
  infer_instance

/-- An accepted actual-schema record supplies a local decomposition without
assuming an edge-set correspondence or replacing original incidences by spokes. -/
theorem acceptedRecord_sound (state : State) (i : Fin 10)
    (replacements added : List (List Star.Vertex))
    (h : AcceptedRecord state i replacements added) :
    ∃ D : Decomposition (graph state),
      D.size = replacements.length + added.length ∧
      D.size ≤ (boundaries i).length + 2 ∧
      ∀ v ∈ Star.anchors, 1 ≤ D.endpointCount v := by
  obtain ⟨D, hs, hb, he⟩ := record_sound _ _ _ _ _ _ _ h _ (graph_edges state)
  refine ⟨D, hs, ?_, ?_⟩
  · simpa [roles] using hb
  · intro v hv
    have hv' := he v (List.mem_toFinset.mpr hv)
    simpa [boundary_count, hv] using hv'

end Gallai.Certificate.CompletedStar
