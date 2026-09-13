/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SyndromeStarCarrier
import Gallai.Transport.FreshCarrierTail
import Gallai.Transport.FreshCarrierBothEnds

/-! # A released carrier consumes only its connector's local core vertices -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A mapped hub-free old piece contains no vertex of the whole bowtie. -/
theorem completedMapWalk_avoids_core {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support)
    (v : V) (hv : v ∈ (B.completedMapWalk P hx).support) : v ∉ B.vertices := by
  rw [B.completedMapWalk_support] at hv
  obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
  intro hB
  exact B.completed_support_ne_hub P hx hu (B.survivor_mem_vertices u hB)

/-- The connector is the only source of core vertices in a through replacement.
Thus certificate disjointness between connector and tails implies actual
same-carrier freshness, independently of other old-anchor intersections. -/
theorem completedThroughCarrier_core_support {a b c d : B.StarSurvivor}
    (L : B.completedStar.Walk a b) (R : B.completedStar.Walk c d)
    (M : G.Walk b.val c.val) (hL : L.IsPath) (hR : R.IsPath)
    (hM : M.IsPath) (hne : ¬ M.Nil) (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0)
    (v : V) (hv : v ∈ (B.completedThroughCarrier L R M hL hR hM hne hLR hxL hxR hm).walk.support)
    (hB : v ∈ B.vertices) : v ∈ M.support := by
  change v ∈ (((B.completedMapWalk L hxL).append M).append
    (B.completedMapWalk R hxR)).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff,SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with (hv | hv) | hv
  · exact (B.completedMapWalk_avoids_core L hxL v hv hB).elim
  · exact hv
  · exact (B.completedMapWalk_avoids_core R hxR v hv hB).elim

/-- Attach a remote endpoint tail to the very same reconstructed through
carrier. Only connector-tail core disjointness is required. -/
theorem completedThroughCarrier_with_tail {a b c d : B.StarSurvivor}
    (L : B.completedStar.Walk a b) (R : B.completedStar.Walk c d)
    (M : G.Walk b.val c.val) (hL : L.IsPath) (hR : R.IsPath)
    (hM : M.IsPath) (hne : ¬ M.Nil) (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0)
    (T : NonemptyPath G) (hj : d.val = T.start)
    (ht : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    (hd : Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices)) :
    ∃ N : NonemptyPath G, N.start = a.val ∧ N.finish = T.finish ∧
      N.walk.edges = ((L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
        R.edges.map (Sym2.map Subtype.val)) ++ T.walk.edges := by
  let P := B.completedThroughCarrier L R M hL hR hM hne hLR hxL hxR hm
  have hdis : Disjoint (P.freshSupport B.vertices) (T.freshSupport B.vertices) := by
    apply Finset.disjoint_left.mpr
    intro v hv hvt
    obtain ⟨hvP,hvB⟩ := Finset.mem_inter.mp hv
    have hvM := B.completedThroughCarrier_core_support L R M hL hR hM hne hLR
      hxL hxR hm v (List.mem_toFinset.mp hvP) hvB
    exact Finset.disjoint_left.mp hd
      (Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hvM,hvB⟩) hvt
  refine ⟨P.appendFresh T B.vertices hj ht hdis,rfl,rfl,?_⟩
  exact (P.appendFresh_edges T B.vertices hj ht hdis).trans
    (congrArg (fun es => es ++ T.walk.edges)
      (B.completedThroughCarrier_edges L R M hL hR hM hne hLR hxL hxR hm))

/-- Both remote endpoints may be extended on the same through carrier.
The three core-disjointness assumptions are precisely the same-owner
certificate checks for the connector and its two tails. -/
theorem completedThroughCarrier_with_two_tails {a b c d : B.StarSurvivor}
    (L : B.completedStar.Walk a b) (R : B.completedStar.Walk c d)
    (M : G.Walk b.val c.val) (hL : L.IsPath) (hR : R.IsPath)
    (hM : M.IsPath) (hne : ¬ M.Nil) (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0)
    (U T : NonemptyPath G) (hu : a.val = U.start) (ht : d.val = T.start)
    (hU : ∀ v ∈ U.walk.support, v = U.start ∨ v ∈ B.vertices)
    (hT : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    (hMU : Disjoint (M.support.toFinset ∩ B.vertices) (U.freshSupport B.vertices))
    (hMT : Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices))
    (hUT : Disjoint (U.freshSupport B.vertices) (T.freshSupport B.vertices)) :
    ∃ N : NonemptyPath G, N.start = U.finish ∧ N.finish = T.finish ∧
      N.walk.edges = (U.walk.edges.reverse ++
        ((L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
          R.edges.map (Sym2.map Subtype.val))) ++ T.walk.edges := by
  let P := B.completedThroughCarrier L R M hL hR hM hne hLR hxL hxR hm
  have hsub : P.freshSupport B.vertices ⊆ M.support.toFinset ∩ B.vertices := by
    intro v hv
    obtain ⟨hp,hvB⟩ := Finset.mem_inter.mp hv
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr
      (B.completedThroughCarrier_core_support L R M hL hR hM hne hLR hxL hxR hm
        v (List.mem_toFinset.mp hp) hvB),hvB⟩
  obtain ⟨N,hNs,hNt,hNe,_⟩ := P.extend_both_fresh U T B.vertices hu ht hU hT
    (hMU.mono_left hsub) (hMT.mono_left hsub) hUT
  refine ⟨N,hNs,hNt,?_⟩
  exact hNe.trans (congrArg (fun es => (U.walk.edges.reverse ++ es) ++ T.walk.edges)
    (B.completedThroughCarrier_edges L R M hL hR hM hne hLR hxL hxR hm))

end Gallai.WholeBowtie
