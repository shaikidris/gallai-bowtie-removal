/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedRemoteSeparation
import Gallai.Operations.Concatenate

/-! # Component-safe terminal carriers for one-credit retained reconstruction -/

namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Append a tail whose surviving vertices, apart from its attachment, are
unreachable from the old carrier's terminal vertex. -/
theorem retainedSeparated_append (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (P : NonemptyPath H) (T : NonemptyPath G) (ht : T.start = P.finish.val)
    (hf : ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
      v = P.finish ∨ ¬ H.Reachable P.finish v) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = T.finish ∧
      N.walk.edges = P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  let old := P.map φ Subtype.val_injective
  have hj : old.finish = T.start := ht.symm
  have hi : ∀ v, v ∈ old.walk.support → v ∈ T.walk.support → v = old.finish := by
    intro v hv hT
    change v ∈ (P.walk.map φ).support at hv
    rw [SimpleGraph.Walk.support_map] at hv
    obtain ⟨w, hw, he⟩ := List.mem_map.mp hv
    change w.val = v at he
    subst v
    rcases hf w hT with heq | hn
    · exact congrArg Subtype.val heq
    · exact (hn (P.walk.dropUntil w hw).reachable.symm).elim
  refine ⟨old.append T hj hi, rfl, rfl, ?_⟩
  exact (NonemptyPath.append_edges _ _ _ _).trans
    (congrArg (fun es => es ++ T.walk.edges) (SimpleGraph.Walk.edges_map φ P.walk))

/-- A hub-ending carrier can use the remote anchor in its new tail. -/
theorem retainedCheap_hub_append (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (P : NonemptyPath H) (hp : P.finish = B.completedHub)
    (T : NonemptyPath G) (ht : T.start = B.label 0)
    (hf : ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
      v = B.completedHub ∨ v = r) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = T.finish ∧
      N.walk.edges = P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  apply B.retainedSeparated_append H hOriginal P T
    (ht.trans (congrArg Subtype.val hp).symm)
  intro v hv
  rcases hf v hv with hx | he
  · exact Or.inl (hx.trans hp.symm)
  · exact Or.inr (by simpa only [hp, he] using hr)

/-- A remote-ending carrier can use any vertex of the hub component in its
new tail, even when the tail visits both old hub neighbours. -/
theorem retainedCheap_remote_append (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (P : NonemptyPath H) (hp : P.finish = r)
    (T : NonemptyPath G) (ht : T.start = r.val)
    (hf : ∀ v : B.StarSurvivor, v.val ∈ T.walk.support →
      v = r ∨ H.Reachable B.completedHub v) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = T.finish ∧
      N.walk.edges = P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  apply B.retainedSeparated_append H hOriginal P T
    (ht.trans (congrArg Subtype.val hp).symm)
  intro v hv
  rcases hf v hv with he | hw
  · exact Or.inl (he.trans hp.symm)
  · refine Or.inr ?_
    intro hrv
    rw [hp] at hrv
    exact hr (hw.trans hrv.symm)

end Gallai.WholeBowtie
