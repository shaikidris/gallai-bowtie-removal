/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.ComponentAssembly

/-! # Exact-sum budget assembly without a designated vertex -/
namespace Gallai

/-- Arbitrary component budgets combine by addition, including empty graphs and isolates. -/
theorem budget_sum_of_components {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (k : G.ConnectedComponent → ℕ)
    (hb : ∀ C : G.ConnectedComponent, HasPathBudget (G.induce C.supp) (k C)) :
    HasPathBudget G (∑ C, k C) := by
  classical
  let K (C : G.ConnectedComponent) := C.toSimpleGraph.spanningCoe
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
        (SimpleGraph.ConnectedComponent.adj_spanningCoe_toSimpleGraph _).mpr ⟨rfl, hab⟩⟩
  have hout := pathBudget_finset_sup Finset.univ K k hd (fun C _ => by
    obtain ⟨D, hD⟩ := hb C
    exact ⟨D.map (Function.Embedding.subtype _), by simpa using hD⟩)
  simpa only [he] using hout

end Gallai
