/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.ComponentAssembly
import Gallai.Operations.FiniteUnionEndpoints

/-! # Simultaneous endpoint reserves in component assembly -/
namespace Gallai

/-- Assemble chosen component decompositions, retaining every chosen endpoint
reserve rather than only a single designated vertex. -/
theorem decomposition_component_reserves {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (D : ∀ C : G.ConnectedComponent, Decomposition (G.induce C.supp)) :
    ∃ E : Decomposition G, E.size = ∑ C, (D C).size ∧
      ∀ C (v : C.supp), (D C).endpointCount v ≤ E.endpointCount v.val := by
  classical
  let K (C : G.ConnectedComponent) := C.toSimpleGraph.spanningCoe
  let P (C : G.ConnectedComponent) : Decomposition (K C) :=
    (D C).map (Function.Embedding.subtype _)
  have hd : (↑(Finset.univ : Finset G.ConnectedComponent) : Set G.ConnectedComponent).Pairwise
      (fun C B => Disjoint (K C).edgeSet (K B).edgeSet) := by
    intro C _ B _ hCB
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hc hb
      exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hCB)
        ((C.adj_spanningCoe_toSimpleGraph).mp hc).1
        ((B.adj_spanningCoe_toSimpleGraph).mp hb).1
  have he : Finset.univ.sup K = G := by
    rw [Finset.sup_eq_iSup]
    apply le_antisymm
    · exact iSup_le fun C => iSup_le fun _ => G.spanningCoe_induce_le C.supp
    · intro a b hab
      simp only [SimpleGraph.iSup_adj]
      exact ⟨G.connectedComponentMk a, Finset.mem_univ _,
        (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph _).mpr ⟨rfl,hab⟩⟩
  obtain ⟨E,hE,hEv⟩ := decomposition_finset_sup_endpoints Finset.univ K P hd
  have hs : E.size = ∑ C, (D C).size := by
    simpa only [P,Decomposition.map_size] using hE
  have hv : ∀ C (v : C.supp), (D C).endpointCount v ≤ E.endpointCount v.val := by
    intro C v
    rw [hEv]
    have hm := (D C).map_endpointCount (Function.Embedding.subtype _) v
    change (P C).endpointCount v.val = (D C).endpointCount v at hm
    rw [← hm]
    exact Finset.single_le_sum (f := fun i => (P i).endpointCount v.val)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ C)
  have hout : ∃ E : Decomposition (Finset.univ.sup K),
      E.size = ∑ C, (D C).size ∧
      ∀ C (v : C.supp), (D C).endpointCount v ≤ E.endpointCount v.val := ⟨E,hs,hv⟩
  rwa [he] at hout

end Gallai
