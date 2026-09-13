/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RepairEdgeCarrier
import Gallai.Structure.PairRepairedPuncture

/-! # Realize a repaired-puncture carrier in the original vertex type

The single-edge supergraph admits either repair status. Its old carriers avoid
all five deleted bowtie vertices, which supplies connector freshness directly.
-/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Include the repaired auxiliary in the original graph plus its possible repair edge. -/
def pairRepairedHom (p q : {v : V // v ∉ B.vertices}) :
    B.pairRepairedPuncture p q →g G ⊔ SimpleGraph.edge p.val q.val where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    change (toggleEdge B.puncture p q).Adj u v at huv
    unfold toggleEdge at huv
    split at huv
    · exact Or.inl huv.1
    · rcases huv with h | h
      · exact Or.inl h
      · right
        rw [SimpleGraph.edge_adj] at h ⊢
        exact ⟨by simpa only [Subtype.ext_iff] using h.1,
          fun he => h.2 (Subtype.val_injective he)⟩

/-- Map an actual auxiliary carrier without identifying any vertices. -/
def pairRepairedCarrier (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) :
    NonemptyPath (G ⊔ SimpleGraph.edge p.val q.val) :=
  P.map (B.pairRepairedHom p q) Subtype.val_injective

omit [DecidableEq V] in
/-- Every vertex of a mapped old carrier lies outside the deleted bowtie. -/
theorem pairRepairedCarrier_outside (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q))
    (v : V) (hv : v ∈ (B.pairRepairedCarrier p q P).walk.support) :
    v ∉ B.vertices := by
  change v ∈ (P.walk.map (B.pairRepairedHom p q)).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
  exact hu ▸ u.property

omit [DecidableEq V] in
/-- A connector using only deleted vertices internally is fresh for every old carrier. -/
theorem pairRepairedCarrier_fresh (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (M : G.Walk p.val q.val)
    (hM : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ B.vertices) :
    ∀ v, v ∈ M.support → v ∈ (B.pairRepairedCarrier p q P).walk.support →
      v = p.val ∨ v = q.val := by
  intro v hvM hvP
  rcases hM v hvM with hp | hq | hB
  · exact Or.inl hp
  · exact Or.inr hq
  · exact (B.pairRepairedCarrier_outside p q P v hvP hB).elim

/-- Restore the actual auxiliary carrier through a checked core-only connector.
No surviving-edge or old-carrier-avoidance premises are left to the consumer. -/
theorem restore_pairRepairedCarrier (p q : {v : V // v ∉ B.vertices})
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (he : s(p, q) ∈ P.walk.edges)
    (M : G.Walk p.val q.val) (hM : M.IsPath)
    (hcore : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ B.vertices) :
    ∃ Q : NonemptyPath G, Q.start = P.start.val ∧ Q.finish = P.finish.val ∧
      ∀ e, Q.walk.edges.count e + (if s(p.val, q.val) = e then 1 else 0) =
        (B.pairRepairedCarrier p q P).walk.edges.count e + M.edges.count e := by
  have he' : s(p.val, q.val) ∈ (B.pairRepairedCarrier p q P).walk.edges := by
    change s(p.val, q.val) ∈ (P.walk.map (B.pairRepairedHom p q)).edges
    rw [SimpleGraph.Walk.edges_map]
    exact List.mem_map.mpr ⟨s(p, q), he, rfl⟩
  exact (B.pairRepairedCarrier p q P).restoreMissingEdge he' M hM
    (B.pairRepairedCarrier_fresh p q P M hcore)

end Gallai.WholeBowtie
