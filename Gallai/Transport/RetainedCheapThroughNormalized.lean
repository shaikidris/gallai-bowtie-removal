/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RetainedCheapThroughCarrier

/-! # Label-oriented cheap through replacement -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Orient only the new connector, retaining its edge counts and remote support. -/
theorem orientRetainedCheapConnector (p q b c r : B.StarSurvivor)
    (hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p))
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = p ∨ v = q ∨ v = B.completedHub ∨ v = r) :
    ∃ K : G.Walk b.val c.val, K.IsPath ∧ ¬ K.Nil ∧
      (∀ e, K.edges.count e = M.edges.count e) ∧
      ∀ v : B.StarSurvivor, v.val ∈ K.support →
        v = b ∨ v = c ∨ v = B.completedHub ∨ v = r := by
  rcases hpair with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact ⟨M, hM, hne, fun _ => rfl, hm⟩
  · refine ⟨M.reverse, hM.reverse, ?_, ?_, ?_⟩
    · exact fun hn => hne (SimpleGraph.Walk.nil_reverse.mp hn)
    · intro e
      simp only [SimpleGraph.Walk.edges_reverse, List.count_reverse]
    · intro v hv
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hv
      rcases hm v hv with hp | hq | hx | hr
      · exact Or.inr (Or.inl hp)
      · exact Or.inl hq
      · exact Or.inr (Or.inr (Or.inl hx))
      · exact Or.inr (Or.inr (Or.inr hr))

/-- A normalized p-q certificate works in either orientation of the actual
through carrier, with the same two-spoke multiset and old endpoint pair. -/
theorem retainedCheapThrough_normalized (H : SimpleGraph B.StarSurvivor)
    (hOriginal : ∀ u v : B.StarSurvivor, H.Adj u v → G.Adj u.val v.val)
    (p q r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (hneighbors : ∀ v, H.Adj B.completedHub v → v = p ∨ v = q)
    (P : NonemptyPath H) (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v = p ∨ v = q ∨ v = B.completedHub ∨ v = r) :
    ∃ N : NonemptyPath G, N.start = P.start.val ∧ N.finish = P.finish.val ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,p.val),s(B.label 0,q.val)] : List (Sym2 V)).count e =
        (P.walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  let b := (P.takeTo B.completedHub hx hs).walk.reverse.snd
  let c := (P.dropFrom B.completedHub hx ht).walk.snd
  have hadj := P.release_attachments_adj B.completedHub hx hs ht
  have hbc := P.release_attachments_ne B.completedHub hx hs ht
  have hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p) := by
    rcases hneighbors b hadj.1 with hb | hb <;>
      rcases hneighbors c hadj.2 with hc | hc
    · exact (hbc (hb.trans hc.symm)).elim
    · exact Or.inl ⟨hb,hc⟩
    · exact Or.inr ⟨hb,hc⟩
    · exact (hbc (hb.trans hc.symm)).elim
  obtain ⟨K, hK, hKn, hKe, hKs⟩ :=
    B.orientRetainedCheapConnector p q b c r hpair M hM hne hm
  obtain ⟨N, hNs, hNt, hN⟩ :=
    B.retainedCheapThroughReplacement H hOriginal r hr P hx hs ht K hK hKn hKs
  refine ⟨N, hNs, hNt, ?_⟩
  intro e
  have h := hN e
  change N.walk.edges.count e +
    ([s(B.label 0,b.val),s(B.label 0,c.val)] : List (Sym2 V)).count e = _ at h
  rw [hKe e] at h
  rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · simpa only [hb,hc] using h
  · simpa only [hb,hc,List.count_cons,List.count_nil,Nat.add_zero,Nat.zero_add,
      Nat.add_comm] using h

end Gallai.WholeBowtie
