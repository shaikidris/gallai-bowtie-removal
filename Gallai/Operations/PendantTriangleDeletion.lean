/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.PendantTriangle
import Gallai.Structure.CutVertexPieces

/-! # Restore a pendant triangle from the actual induced deletion

The graph identity is derived from adjacency and full private-neighbourhood
conditions. The input is a decomposition of the smaller vertex subtype,
not a decomposition already living on the desired original graph.
-/

namespace Gallai.Decomposition

universe u
variable {V : Type u} [DecidableEq V] {G : SimpleGraph V}

/-- Restore a whole pendant triangle from its induced deletion. The exact graph
partition and freshness conditions are derived, not supplied as certificates. -/
theorem restore_pendant_triangle_deletion (f : Fin 3 ↪ V)
    (htri : ∀ i j, i ≠ j → G.Adj (f i) (f j))
    (hprivate : ∀ i, i ≠ 0 → ∀ v, G.Adj (f i) v → ∃ j, f j = v)
    (hx : ∃ v, (v ≠ f 1 ∧ v ≠ f 2) ∧ G.Adj (f 0) v)
    (D : Decomposition (G.induce {v | v ≠ f 1 ∧ v ≠ f 2})) :
    ∃ E : Decomposition G, E.size = D.size + 1 ∧
      ∀ v : {v : V // v ≠ f 1 ∧ v ≠ f 2},
        E.endpointCount v.val = D.endpointCount v := by
  classical
  let S : Set V := {v | v ≠ f 1 ∧ v ≠ f 2}
  let H := (G.induce S).spanningCoe
  let T := (⊤ : SimpleGraph (Fin 3)).map f
  have hzero : f 0 ∈ S :=
    ⟨fun h => (by decide : (0 : Fin 3) ≠ 1) (f.injective h),
      fun h => (by decide : (0 : Fin 3) ≠ 2) (f.injective h)⟩
  have h1 : ∀ v, ¬ H.Adj (f 1) v := by
    intro v h
    exact ((spanning_induce_adj_iff G S _ _).mp h).2.1.1 rfl
  have h2 : ∀ v, ¬ H.Adj (f 2) v := by
    intro v h
    exact ((spanning_induce_adj_iff G S _ _).mp h).2.1.2 rfl
  have hincident : ∃ v, H.Adj (f 0) v := by
    obtain ⟨v, hv, ha⟩ := hx
    exact ⟨v, (spanning_induce_adj_iff G S _ _).mpr ⟨ha, hzero, hv⟩⟩
  have hborder {u : V} (hu : u ∉ S) {v : V} (ha : G.Adj u v) : T.Adj u v := by
    have hu' : u = f 1 ∨ u = f 2 := by
      simpa only [S, Set.mem_ofPred_eq, not_and_or, not_not] using hu
    have selected : ∃ i : Fin 3, i ≠ 0 ∧ f i = u := by
      rcases hu' with h | h
      · exact ⟨1, by decide, h.symm⟩
      · exact ⟨2, by decide, h.symm⟩
    obtain ⟨i, hi, rfl⟩ := selected
    obtain ⟨j, rfl⟩ := hprivate i hi v ha
    exact SimpleGraph.map_adj_apply.mpr (show (⊤ : SimpleGraph (Fin 3)).Adj i j from
      fun h => ha.ne (congrArg f h))
  have hgraph : T ⊔ H = G := by
    ext u v
    constructor
    · rintro (h | h)
      · obtain ⟨i, j, hij, rfl, rfl⟩ := (SimpleGraph.map_adj f ⊤ u v).mp h
        exact htri i j hij
      · exact ((spanning_induce_adj_iff G S u v).mp h).1
    · intro h
      by_cases hu : u ∈ S
      · by_cases hv : v ∈ S
        · exact Or.inr ((spanning_induce_adj_iff G S u v).mpr ⟨h, hu, hv⟩)
        · exact Or.inl (hborder hv h.symm).symm
      · exact Or.inl (hborder hu h)
  let D0 : Decomposition H := D.map (Function.Embedding.subtype _)
  obtain ⟨E, hs, he⟩ := D0.attach_pendant_triangle f h1 h2 hincident
  have hout : ∃ E : Decomposition (T ⊔ H), E.size = D.size + 1 ∧
      ∀ v : S, E.endpointCount v.val = D.endpointCount v := by
    refine ⟨E, hs, ?_⟩
    intro v
    rw [he v.val v.property.1 v.property.2]
    exact D.map_endpointCount (Function.Embedding.subtype _) v
  rwa [hgraph] at hout

end Gallai.Decomposition
