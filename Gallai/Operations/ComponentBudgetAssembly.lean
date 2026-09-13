/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.ComponentAssembly

/-! # Componentwise budget assembly preserving designated endpoints

Budgets are kept as an exact sum. In particular, ceiling budgets on other
components are not replaced by the stronger floor assumptions.
-/

namespace Gallai

/-- Combine actual component budgets while retaining two designated endpoints. -/
theorem endpoint_budget_of_components {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (y : V)
    (k : G.ConnectedComponent → ℕ)
    (D : Decomposition (G.induce (G.connectedComponentMk y).supp))
    (hD : D.size ≤ k (G.connectedComponentMk y))
    (hy : 2 ≤ D.endpointCount ⟨y, rfl⟩)
    (hb : ∀ C : G.ConnectedComponent, C ≠ G.connectedComponentMk y →
      HasPathBudget (G.induce C.supp) (k C)) :
    ∃ E : Decomposition G, E.size ≤ ∑ C, k C ∧ 2 ≤ E.endpointCount y := by
  classical
  let C₀ := G.connectedComponentMk y
  let K (C : G.ConnectedComponent) := C.toSimpleGraph.spanningCoe
  let s : Finset G.ConnectedComponent := Finset.univ.erase C₀
  have hd : (s : Set G.ConnectedComponent).Pairwise
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
        (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph _).mpr ⟨rfl, hab⟩⟩
  have hg : K C₀ ⊔ s.sup K = G := by
    rw [← Finset.sup_insert]
    have hins : insert C₀ s = Finset.univ := Finset.insert_erase (Finset.mem_univ _)
    rw [hins, he]
  have hdis : Disjoint (K C₀).edgeSet (s.sup K).edgeSet := by
    rw [Finset.sup_eq_iSup]
    simp only [SimpleGraph.edgeSet_iSup, Set.disjoint_iUnion_right]
    intro C hC
    have hne : C₀ ≠ C := (Finset.mem_erase.mp hC).1.symm
    apply Set.disjoint_left.mpr
    intro e
    induction e using Sym2.inductionOn with
    | hf a b =>
      intro hc hb
      exact Set.disjoint_left.mp (G.pairwise_disjoint_supp_connectedComponent hne)
        ((C₀.adj_spanningCoe_toSimpleGraph).mp hc).1
        ((C.adj_spanningCoe_toSimpleGraph).mp hb).1
  obtain ⟨E, hE⟩ := pathBudget_finset_sup s K k hd (fun C hC => by
    obtain ⟨P, hP⟩ := hb C (Finset.mem_erase.mp hC).1
    exact ⟨P.map (Function.Embedding.subtype _), by simpa using hP⟩)
  obtain ⟨F, hs, hends⟩ :=
    (D.map (Function.Embedding.subtype _)).union_disjoint_endpoints E hdis
  have hsum : (∑ C ∈ s, k C) + k C₀ = ∑ C, k C :=
    Finset.sum_erase_add _ _ (Finset.mem_univ _)
  have hsize : F.size ≤ ∑ C, k C := by
    simp only [Decomposition.map_size] at hs
    change D.size ≤ k C₀ at hD
    omega
  have hexpose : 2 ≤ F.endpointCount y := by
    rw [hends y]
    have hmap := D.map_endpointCount (Function.Embedding.subtype _) ⟨y, rfl⟩
    change (D.map (Function.Embedding.subtype _)).endpointCount y =
      D.endpointCount ⟨y, rfl⟩ at hmap
    rw [hmap]
    omega
  have hout : ∃ F : Decomposition (K C₀ ⊔ s.sup K),
      F.size ≤ ∑ C, k C ∧ 2 ≤ F.endpointCount y := ⟨F, hsize, hexpose⟩
  rwa [hg] at hout

end Gallai
