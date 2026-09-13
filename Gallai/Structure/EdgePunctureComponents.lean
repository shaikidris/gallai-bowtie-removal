/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Combinatorics.SimpleGraph.Connectivity.Connected

/-! # Components after deleting one edge of a connected graph -/

namespace Gallai

variable {V : Type*} {G : SimpleGraph V}

/-- Every vertex can reach one of the deleted edge's endpoints without that edge. -/
theorem reachable_endpoint_delete_edge (hc : G.Connected) (x w v : V)
    (hxw : G.Adj x w) :
    (G.deleteEdges {s(x, w)}).Reachable v x ∨
      (G.deleteEdges {s(x, w)}).Reachable v w := by
  classical
  obtain ⟨P, hP⟩ := hc.exists_isPath v x
  by_cases he : s(x, w) ∈ P.edges
  · have hwP := P.snd_mem_support_of_mem_edges he
    let Q := P.takeUntil w hwP
    have hxQ := SimpleGraph.Walk.endpoint_notMem_support_takeUntil hP hwP hxw.ne
    have heQ : s(x, w) ∉ Q.edges := fun h => hxQ (Q.fst_mem_support_of_mem_edges h)
    exact Or.inr ⟨Q.toDeleteEdges {s(x, w)} (by grind)⟩
  · exact Or.inl ⟨P.toDeleteEdges {s(x, w)} (by grind)⟩

/-- Every actual component after a one-edge puncture contains a deleted endpoint.
This includes isolated endpoints, and needs no separate two-component assumption. -/
theorem component_contains_deleted_endpoint (hc : G.Connected) (x w : V)
    (hxw : G.Adj x w) (C : (G.deleteEdges {s(x, w)}).ConnectedComponent) :
    x ∈ C.supp ∨ w ∈ C.supp := by
  obtain ⟨v, rfl⟩ := C.exists_rep
  rcases reachable_endpoint_delete_edge hc x w v hxw with hx | hw
  · exact Or.inl (SimpleGraph.ConnectedComponent.sound hx.symm)
  · exact Or.inr (SimpleGraph.ConnectedComponent.sound hw.symm)

end Gallai
