/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.FiniteUnion

/-! # Finite union preserving the complete endpoint vector -/
namespace Gallai

/-- Unlike budget-only assembly, this keeps all component reserves in the
same resulting witness. -/
theorem decomposition_finset_sup_endpoints {V I : Type*} [DecidableEq V]
    (s : Finset I) (K : I → SimpleGraph V) (D : ∀ i, Decomposition (K i))
    (hd : (s : Set I).Pairwise fun i j => Disjoint (K i).edgeSet (K j).edgeSet) :
    ∃ E : Decomposition (s.sup K), E.size = ∑ i ∈ s, (D i).size ∧
      ∀ v, E.endpointCount v = ∑ i ∈ s, (D i).endpointCount v := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    refine ⟨Decomposition.empty, ?_, ?_⟩
    · simp [Decomposition.empty]
    · intro v
      simp [Decomposition.empty, Decomposition.endpointCount]
  | @insert a s ha ih =>
    have hds : (s : Set I).Pairwise
        (fun i j => Disjoint (K i).edgeSet (K j).edgeSet) :=
      fun _ hi _ hj hij => hd (Finset.mem_insert_of_mem hi)
        (Finset.mem_insert_of_mem hj) hij
    obtain ⟨E,hE,hEv⟩ := ih hds
    have hdis : Disjoint (K a).edgeSet (s.sup K).edgeSet := by
      rw [Finset.sup_eq_iSup]
      simp only [SimpleGraph.edgeSet_iSup, Set.disjoint_iUnion_right]
      intro i hi
      exact hd (Finset.mem_insert_self a s) (Finset.mem_insert_of_mem hi)
        (fun h => ha (h ▸ hi))
    obtain ⟨F,hF,hFv⟩ := (D a).union_disjoint_endpoints E hdis
    rw [Finset.sup_insert]
    refine ⟨F, ?_, ?_⟩
    · rw [hF,hE,Finset.sum_insert ha]
    · intro v
      rw [hFv,hEv,Finset.sum_insert ha]

end Gallai
