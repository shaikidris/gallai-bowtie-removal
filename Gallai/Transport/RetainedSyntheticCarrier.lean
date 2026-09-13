/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RepairEdgeCarrier
import Gallai.Structure.RetainedHubAuxiliary

/-! # Synthetic retained repair: the old carrier may contain the hub -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Map the retained auxiliary into the original graph with its repair edge. -/
def retainedRepairHom (p q : B.StarSurvivor) :
    B.retainedHubRepair p q →g G ⊔ SimpleGraph.edge p.val q.val where
  toFun := Subtype.val
  map_rel' := by
    intro u v huv
    change (toggleEdge B.retainedHubGraph p q).Adj u v at huv
    unfold toggleEdge at huv
    split at huv
    · exact Or.inl huv.1
    · rcases huv with h | h
      · exact Or.inl h
      · right
        rw [SimpleGraph.edge_adj] at h ⊢
        exact ⟨by simpa only [Subtype.ext_iff] using h.1,
          fun he => h.2 (Subtype.val_injective he)⟩

/-- No old vertices are identified in the carrier map. -/
def retainedRepairCarrier (p q : B.StarSurvivor)
    (P : NonemptyPath (B.retainedHubRepair p q)) :
    NonemptyPath (G ⊔ SimpleGraph.edge p.val q.val) :=
  P.map (B.retainedRepairHom p q) Subtype.val_injective

theorem retainedRepairCarrier_edges (p q : B.StarSurvivor)
    (P : NonemptyPath (B.retainedHubRepair p q)) :
    (B.retainedRepairCarrier p q P).walk.edges =
      P.walk.edges.map (Sym2.map Subtype.val) := SimpleGraph.Walk.edges_map _ _

/-- Old support avoids exactly the four deleted private vertices. -/
theorem retainedRepairCarrier_private_free (p q : B.StarSurvivor)
    (P : NonemptyPath (B.retainedHubRepair p q)) (v : V)
    (hv : v ∈ (B.retainedRepairCarrier p q P).walk.support) :
    v ∉ (Finset.univ.erase 0).map B.label := by
  change v ∈ (P.walk.map (B.retainedRepairHom p q)).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, _, hu⟩ := List.mem_map.mp hv
  exact hu ▸ u.property

/-- Restore the unique repair run using a strict-private connector. The
retained hub is deliberately not admitted as a fresh internal vertex. -/
theorem restore_retainedRepairCarrier (p q : B.StarSurvivor)
    (P : NonemptyPath (B.retainedHubRepair p q)) (he : s(p,q) ∈ P.walk.edges)
    (M : G.Walk p.val q.val) (hM : M.IsPath)
    (hf : ∀ v ∈ M.support, v = p.val ∨ v = q.val ∨ v ∈ (Finset.univ.erase 0).map B.label) :
    ∃ Q : NonemptyPath G, Q.start = P.start.val ∧ Q.finish = P.finish.val ∧
      ∀ e, Q.walk.edges.count e + (if s(p.val,q.val) = e then 1 else 0) =
        (B.retainedRepairCarrier p q P).walk.edges.count e + M.edges.count e := by
  have he' : s(p.val,q.val) ∈ (B.retainedRepairCarrier p q P).walk.edges := by
    rw [B.retainedRepairCarrier_edges]
    exact List.mem_map.mpr ⟨s(p,q), he, rfl⟩
  apply (B.retainedRepairCarrier p q P).restoreMissingEdge he' M hM
  intro v hvM hvP
  rcases hf v hvM with hp | hq | hd
  · exact Or.inl hp
  · exact Or.inr hq
  · exact (B.retainedRepairCarrier_private_free p q P v hvP hd).elim

/-- A carrier not owning the repair edge transfers unchanged into G. -/
def unchangedRetainedRepairCarrier (p q : B.StarSurvivor)
    (P : NonemptyPath (B.retainedHubRepair p q)) (hn : s(p,q) ∉ P.walk.edges) : NonemptyPath G :=
  (B.retainedRepairCarrier p q P).transfer G (by
    intro e he
    have hs := (B.retainedRepairCarrier p q P).walk.edges_subset_edgeSet he
    rw [SimpleGraph.edgeSet_sup] at hs
    rcases hs with hg | hr
    · exact hg
    · have heq : e = s(p.val,q.val) := SimpleGraph.edgeSet_edge_subset hr
      rw [B.retainedRepairCarrier_edges] at he
      obtain ⟨f, hf, hfe⟩ := List.mem_map.mp he
      have hfp : f = s(p,q) := (Sym2.map.injective Subtype.val_injective) (hfe.trans heq)
      exact (hn (hfp ▸ hf)).elim)

end Gallai.WholeBowtie
