/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedOriginalCarrier
import Gallai.Operations.HubRelease

/-! # Replace an actual retained through-run, in either orientation -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Reverse only the connector when the old attachments are oppositely ordered. -/
theorem orientRetainedConnector (p q b c : B.StarSurvivor)
    (hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p))
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = p.val ∨ v.val = q.val ∨ v.val = B.label 0) :
    ∃ K : G.Walk b.val c.val, K.IsPath ∧ ¬ K.Nil ∧
      (∀ e, K.edges.count e = M.edges.count e) ∧
      ∀ v : B.StarSurvivor, v.val ∈ K.support →
        v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0 := by
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨M, hM, hne, fun _ => rfl, hm⟩
  · refine ⟨M.reverse, hM.reverse, ?_, ?_, ?_⟩
    · intro hn
      exact hne (SimpleGraph.Walk.nil_reverse.mp hn)
    · intro e
      simp only [SimpleGraph.Walk.edges_reverse, List.count_reverse]
    · intro v hv
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      rcases hm v hv with hp | hq | hx
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hq
      · exact Or.inr (Or.inr hx)

/-- Replace the actual two-spoke run by the finite connector. The output has
the original endpoints and exchanges exactly the two spokes for connector edges. -/
theorem retainedThroughReplacement (H : SimpleGraph B.StarSurvivor)
    (hle : H ≤ B.completedStar) (p q : B.StarSurvivor)
    (hneighbors : ∀ v, H.Adj B.completedHub v → v = p ∨ v = q)
    (P : NonemptyPath H) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = p.val ∨ v.val = q.val ∨ v.val = B.label 0) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = P.finish.val ∧
      ∀ e : Sym2 V,
        N.walk.edges.count e +
          ([s(B.label 0, (P.takeTo B.completedHub hx hs).walk.reverse.snd.val),
            s(B.label 0, (P.dropFrom B.completedHub hx ht).walk.snd.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  let b := (P.takeTo B.completedHub hx hs).walk.reverse.snd
  let c := (P.dropFrom B.completedHub hx ht).walk.snd
  have hadj := P.release_attachments_adj B.completedHub hx hs ht
  have hbc := P.release_attachments_ne B.completedHub hx hs ht
  have hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p) := by
    rcases hneighbors b hadj.1 with hb | hb <;>
      rcases hneighbors c hadj.2 with hc | hc
    · exact False.elim (hbc (hb.trans hc.symm))
    · exact Or.inl ⟨hb, hc⟩
    · exact Or.inr ⟨hb, hc⟩
    · exact False.elim (hbc (hb.trans hc.symm))
  obtain ⟨K, hK, hKn, hKe, hKs⟩ := B.orientRetainedConnector p q b c hpair M hM hne hm
  let L := P.releaseLeft B.completedHub hx hs
  let R := P.releaseRight B.completedHub hx ht
  let N := B.retainedThroughCarrier H hle L R K
    (P.releaseLeft_isPath B.completedHub hx hs) (P.releaseRight_isPath B.completedHub hx ht)
    hK hKn (P.release_supports_disjoint B.completedHub hx hs ht)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.hub_notMem_releaseRight B.completedHub hx ht) hKs
  refine ⟨N, rfl, rfl, ?_⟩
  intro e
  have hnew := B.retainedThroughCarrier_edges H hle L R K
    (P.releaseLeft_isPath B.completedHub hx hs) (P.releaseRight_isPath B.completedHub hx ht)
    hK hKn (P.release_supports_disjoint B.completedHub hx hs ht)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.hub_notMem_releaseRight B.completedHub hx ht) hKs
  have hnewCount := congrArg (fun es : List (Sym2 V) => es.count e) hnew
  have hold := congrArg (fun es : List (Sym2 B.StarSurvivor) =>
    (es.map (Sym2.map Subtype.val)).count e) (P.release_edges B.completedHub hx hs ht)
  simp only [List.map_append, List.map_cons, List.map_nil, Sym2.map_mk,
    List.count_append] at hold
  simp only [List.count_append] at hnewCount
  change N.walk.edges.count e = _ at hnewCount
  have heK := hKe e
  have hnew' : N.walk.edges.count e =
      (L.edges.map (Sym2.map Subtype.val)).count e + K.edges.count e +
        (R.edges.map (Sym2.map Subtype.val)).count e := hnewCount
  have hold' : (L.edges.map (Sym2.map Subtype.val)).count e +
      ([s(B.label 0, b.val), s(B.label 0, c.val)] : List (Sym2 V)).count e +
      (R.edges.map (Sym2.map Subtype.val)).count e =
      (P.walk.edges.map (Sym2.map Subtype.val)).count e := hold
  change _ + ([s(B.label 0, b.val), s(B.label 0, c.val)] : List (Sym2 V)).count e = _
  omega

end Gallai.WholeBowtie
