/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapTerminalCarrier
import Gallai.Transport.RetainedThroughReplacement

/-! # A retained through splice allowing one separated remote anchor -/

namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Released old pieces can be connected through the hub and a remote anchor,
provided both vertices are absent from those pieces. -/
def retainedCheapThroughCarrier (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) {a b c d : B.StarSurvivor}
    (L : H.Walk a b) (R : H.Walk c d) (M : G.Walk b.val c.val)
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hrL : r ∉ L.support) (hrR : r ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = b ∨ v = c ∨ v = B.completedHub ∨ v = r) : NonemptyPath G := by
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  refine NonemptyPath.splice (L.map φ) M (R.map φ)
    (hL.map Subtype.val_injective) hM (hR.map Subtype.val_injective) hne ?_ ?_ ?_
  · intro w hwL hwR
    rw [SimpleGraph.Walk.support_map] at hwL hwR
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hwL
    obtain ⟨v', hv', he'⟩ := List.mem_map.mp hwR
    have hvv : v = v' := Subtype.ext (he.trans he'.symm)
    exact hLR hv (hvv.symm ▸ hv')
  · intro w hwL hwM
    rw [SimpleGraph.Walk.support_map] at hwL
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hwL
    change v.val = w at he
    subst w
    rcases hm v hwM with hb | hc | hx | hr
    · exact congrArg Subtype.val hb
    · exact (hLR (hc ▸ hv) R.start_mem_support).elim
    · exact (hxL (hx ▸ hv)).elim
    · exact (hrL (hr ▸ hv)).elim
  · intro w hwM hwR
    rw [SimpleGraph.Walk.support_map] at hwR
    obtain ⟨v, hv, he⟩ := List.mem_map.mp hwR
    change v.val = w at he
    subst w
    rcases hm v hwM with hb | hc | hx | hr
    · exact (hLR L.end_mem_support (hb ▸ hv)).elim
    · exact congrArg Subtype.val hc
    · exact (hxR (hx ▸ hv)).elim
    · exact (hrR (hr ▸ hv)).elim

/-- The remote-aware splice has the same exact edge formula as an ordinary splice. -/
theorem retainedCheapThroughCarrier_edges (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) {a b c d : B.StarSurvivor}
    (L : H.Walk a b) (R : H.Walk c d) (M : G.Walk b.val c.val)
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hrL : r ∉ L.support) (hrR : r ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = b ∨ v = c ∨ v = B.completedHub ∨ v = r) :
    (B.retainedCheapThroughCarrier H hOriginal r L R M hL hR hM hne
      hLR hxL hxR hrL hrR hm).walk.edges =
      (L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
        R.edges.map (Sym2.map Subtype.val) := by
  let φ : H →g G := ⟨Subtype.val, fun {u v} h => hOriginal u v h⟩
  change (((L.map φ).append M).append (R.map φ)).edges = _
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
    SimpleGraph.Walk.edges_map, SimpleGraph.Walk.edges_map]
  rfl

/-- Replace an actual through-hub run. Remote avoidance is derived from
non-reachability, not imposed on the old carrier as an additional assumption. -/
theorem retainedCheapThroughReplacement (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (P : NonemptyPath H) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (M : G.Walk (P.takeTo B.completedHub hx hs).walk.reverse.snd.val
      (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = (P.takeTo B.completedHub hx hs).walk.reverse.snd ∨
      v = (P.dropFrom B.completedHub hx ht).walk.snd ∨ v = B.completedHub ∨ v = r) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = P.finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0, (P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
          s(B.label 0, (P.dropFrom B.completedHub hx ht).walk.snd.val)] :
          List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  let L := P.releaseLeft B.completedHub hx hs
  let R := P.releaseRight B.completedHub hx ht
  have hadj := P.release_attachments_adj B.completedHub hx hs ht
  have hrL : r ∉ L.support := by
    intro h
    exact hr (hadj.1.reachable.trans (L.dropUntil r h).reachable.symm)
  have hrR : r ∉ R.support := by
    intro h
    exact hr (hadj.2.reachable.trans (R.takeUntil r h).reachable)
  let N := B.retainedCheapThroughCarrier H hOriginal r L R M
    (P.releaseLeft_isPath B.completedHub hx hs) (P.releaseRight_isPath B.completedHub hx ht)
    hM hne (P.release_supports_disjoint B.completedHub hx hs ht)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.hub_notMem_releaseRight B.completedHub hx ht) hrL hrR hm
  refine ⟨N, rfl, rfl, ?_⟩
  intro e
  have hnew := congrArg (fun es : List (Sym2 V) => es.count e)
    (B.retainedCheapThroughCarrier_edges H hOriginal r L R M
      (P.releaseLeft_isPath B.completedHub hx hs) (P.releaseRight_isPath B.completedHub hx ht)
      hM hne (P.release_supports_disjoint B.completedHub hx hs ht)
      (P.hub_notMem_releaseLeft B.completedHub hx hs)
      (P.hub_notMem_releaseRight B.completedHub hx ht) hrL hrR hm)
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  simp only [List.map_append, List.map_cons, List.map_nil, Sym2.map_mk,
    List.count_append] at hold
  simp only [List.count_append] at hnew
  change N.walk.edges.count e = _ at hnew
  change (L.edges.map (Sym2.map Subtype.val)).count e +
    ([s(B.label 0, (P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
      s(B.label 0, (P.dropFrom B.completedHub hx ht).walk.snd.val)] :
      List (Sym2 V)).count e +
    (R.edges.map (Sym2.map Subtype.val)).count e = _ at hold
  omega

end Gallai.WholeBowtie
