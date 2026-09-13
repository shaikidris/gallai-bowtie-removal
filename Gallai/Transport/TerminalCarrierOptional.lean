/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ReleasedCarrierFootprint
import Gallai.Transport.FreshCarrierOptional
import Gallai.Transport.SyndromeTerminalRelease

/-! # Terminal hub replacement with an optional remote tail on its old carrier -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The released old prefix contributes no core vertices, even if it is nil. -/
theorem completedTerminalCarrier_core_support {a b : B.StarSurvivor} {c : V}
    (L : B.completedStar.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0)
    (v : V)
    (hv : v ∈ (B.completedTerminalCarrier L M hL hM hne hx hm).walk.support)
    (hB : v ∈ B.vertices) : v ∈ M.support := by
  change v ∈ ((B.completedMapWalk L hx).append M).support at hv
  rw [SimpleGraph.Walk.mem_support_append_iff] at hv
  rcases hv with hv | hv
  · exact (B.completedMapWalk_avoids_core L hx v hv hB).elim
  · exact hv

/-- Reconstruct a terminal carrier and, when present, extend its other endpoint.
Only disjointness of local core footprints is assumed; the old prefix may
visit other anchors. None leaves the old endpoint unchanged and adds no path. -/
theorem retainedTerminalCarrier_with_optional_tail
    (H : SimpleGraph B.StarSurvivor) (hle : H ≤ B.completedStar)
    {a b : B.StarSurvivor} {c : V}
    (L : H.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0)
    (U : Option (NonemptyPath G))
    (hU : ∀ T ∈ U, a.val = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices)) :
    ∃ N : NonemptyPath G,
      N.start = (U.map (·.finish)).getD a.val ∧ N.finish = c ∧
      N.walk.edges = ((U.map (fun T => T.walk.edges.reverse)).getD []) ++
        (L.edges.map (Sym2.map Subtype.val) ++ M.edges) := by
  let P := B.retainedTerminalCarrier H hle L M hL hM hne hx hm
  have hsub : P.freshSupport B.vertices ⊆ M.support.toFinset ∩ B.vertices := by
    intro v hv
    obtain ⟨hp,hB⟩ := Finset.mem_inter.mp hv
    have hcore := B.completedTerminalCarrier_core_support
      (B.retainedLiftWalk H hle L) M (B.retainedLiftWalk_isPath H hle L hL)
      hM hne (by simpa only [B.retainedLiftWalk_support] using hx) hm
      v (List.mem_toFinset.mp hp) hB
    exact Finset.mem_inter.mpr ⟨List.mem_toFinset.mpr hcore,hB⟩
  obtain ⟨N,hNs,hNt,hNe⟩ := P.extend_optional_fresh U none B.vertices
    (by
      intro T ht
      obtain ⟨hj,hfresh,hd⟩ := hU T ht
      exact ⟨hj,hfresh,hd.mono_left hsub⟩)
    (by simp) (by simp)
  refine ⟨N,hNs,hNt,?_⟩
  have he := hNe.trans (congrArg
    (fun es => (((U.map (fun T => T.walk.edges.reverse)).getD []) ++ es) ++ [])
    (B.retainedTerminalCarrier_edges H hle L M hL hM hne hx hm))
  simpa only [List.append_nil] using he

/-- The actual syndrome carrier loses its possibly synthetic terminal spoke
and receives both its mandatory hub word and its optional remote word. The
edge equation accounts for the released spoke, not merely the trimmed prefix. -/
theorem syndrome_terminal_release_optional (P : NonemptyPath B.syndromeStar)
    (hx : P.finish = B.completedHub) {c : V}
    (M : G.Walk P.walk.reverse.snd.val c) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = P.walk.reverse.snd.val ∨ v.val = B.label 0)
    (U : Option (NonemptyPath G))
    (hU : ∀ T ∈ U, P.start.val = T.start ∧
      (∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) ∧
      Disjoint (M.support.toFinset ∩ B.vertices) (T.freshSupport B.vertices)) :
    ∃ N : NonemptyPath G,
      N.start = (U.map (·.finish)).getD P.start.val ∧ N.finish = c ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e +
          ((U.map (fun T => T.walk.edges.reverse)).getD []).count e := by
  let L := P.walk.reverse.tail.reverse
  have hL : L.IsPath := P.isPath.reverse.tail.reverse
  have hfree : B.completedHub ∉ L.support := by
    change B.completedHub ∉ P.walk.reverse.tail.reverse.support
    rw [SimpleGraph.Walk.support_reverse,List.mem_reverse]
    have h := P.reverse.start_notMem_tail_support
    change P.finish ∉ P.walk.reverse.tail.support at h
    intro hv
    exact h ((congrArg (fun v => v ∈ P.walk.reverse.tail.support) hx).mpr hv)
  obtain ⟨N,hNs,hNt,hNe⟩ := B.retainedTerminalCarrier_with_optional_tail
    B.syndromeStar B.syndromeStar_le_completedStar L M hL hM hne hfree hm U hU
  refine ⟨N,hNs,hNt,?_⟩
  intro e
  have hnew := congrArg (List.count e) hNe
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) P.reverse_tail_edges_append_spoke
  simp only [List.map_append,List.map_cons,List.map_nil,Sym2.map_mk,
    List.count_append,List.count_cons,List.count_nil,hx] at hold
  simp only [List.count_append] at hnew
  have hsp : (if (s(B.label 0,P.walk.reverse.snd.val) == e) = true then 1 else 0 : ℕ) =
      (if s(B.label 0,P.walk.reverse.snd.val) = e then 1 else 0) := by simp
  change (L.edges.map (Sym2.map Subtype.val)).count e +
    (0 + if (s(B.label 0,P.walk.reverse.snd.val) == e) = true then 1 else 0) = _ at hold
  rw [hsp] at hold
  omega

end Gallai.WholeBowtie
