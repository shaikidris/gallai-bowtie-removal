/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.SyndromeStar
import Gallai.Transport.RetainedThroughReplacement
import Gallai.Foundations.DegreeTwoCarriers

/-! # Safe mapping after release of possibly synthetic syndrome spokes -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Syndrome spokes are a subset of completed anchor spokes, whether or not
they were original edges. Off-hub edges are unchanged. -/
theorem syndromeStar_le_completedStar : B.syndromeStar ≤ B.completedStar := by
  intro u v h
  rcases h with ⟨h,_,_⟩ | ⟨hu,hv⟩ | ⟨hv,hu⟩
  · exact Or.inl h
  · exact Or.inr (Or.inl ⟨hu,B.syndrome_subset_anchors hv⟩)
  · exact Or.inr (Or.inr ⟨hv,B.syndrome_subset_anchors hu⟩)

/-- Map any hub-free old walk, including a nil released prefix. -/
def syndromeMapWalk {a b : B.StarSurvivor} (P : B.syndromeStar.Walk a b)
    (hx : B.completedHub ∉ P.support) : G.Walk a.val b.val :=
  B.completedMapWalk (B.retainedLiftWalk B.syndromeStar B.syndromeStar_le_completedStar P)
    (by simpa only [B.retainedLiftWalk_support] using hx)

theorem syndromeMapWalk_edges {a b : B.StarSurvivor} (P : B.syndromeStar.Walk a b)
    (hx : B.completedHub ∉ P.support) :
    (B.syndromeMapWalk P hx).edges = P.edges.map (Sym2.map Subtype.val) := by
  unfold syndromeMapWalk
  rw [B.completedMapWalk_edges,B.retainedLiftWalk_edges]

theorem syndromeMapWalk_support {a b : B.StarSurvivor} (P : B.syndromeStar.Walk a b)
    (hx : B.completedHub ∉ P.support) :
    (B.syndromeMapWalk P hx).support = P.support.map Subtype.val := by
  unfold syndromeMapWalk
  rw [B.completedMapWalk_support,B.retainedLiftWalk_support]

/-- Preserve an untouched carrier without assuming the auxiliary embeds in G. -/
def syndromeAvoidingPath (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∉ P.walk.support) : NonemptyPath G :=
  B.completedAvoidingPath
    (P.map (SimpleGraph.Hom.ofLE B.syndromeStar_le_completedStar) Function.injective_id)
    (by
      change B.completedHub ∉ (P.walk.map _).support
      rw [SimpleGraph.Walk.support_map]
      change B.completedHub ∉ P.walk.support.map id
      simpa only [List.map_id] using hx)

theorem syndromeAvoidingPath_edges (P : NonemptyPath B.syndromeStar)
    (hx : B.completedHub ∉ P.walk.support) :
    (B.syndromeAvoidingPath P hx).walk.edges = P.walk.edges.map (Sym2.map Subtype.val) := by
  unfold syndromeAvoidingPath
  rw [B.completedAvoidingPath_edges]
  change ((P.walk.map (SimpleGraph.Hom.ofLE B.syndromeStar_le_completedStar)).edges).map _ = _
  rw [SimpleGraph.Walk.edges_map]
  simp

/-- Replace the unique hub run and map all other carriers after excluding
the hub. The count identity is for the selected carrier; family summation
and simultaneous endpoint tails remain separate reconstruction obligations. -/
theorem syndromeStar_passing_replacement
    (p q : B.StarSurvivor) (hSigma : B.syndrome = {p.val,q.val})
    (hsize : B.syndrome.card = 2) (D : Decomposition B.syndromeStar)
    (hz : D.endpointCount B.completedHub = 0)
    (M : G.Walk p.val q.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = p.val ∨ v.val = q.val ∨ v.val = B.label 0) :
    ∃ j : Fin D.size, ∃ N : NonemptyPath G,
      N.start = (D.path j).start.val ∧ N.finish = (D.path j).finish.val ∧
      (∀ i, i ≠ j → B.completedHub ∉ (D.path i).walk.support) ∧
      ∀ e : Sym2 V, N.walk.edges.count e +
        ([s(B.label 0,p.val),s(B.label 0,q.val)] : List (Sym2 V)).count e =
        ((D.path j).walk.edges.map (Sym2.map Subtype.val)).count e + M.edges.count e := by
  obtain ⟨j,hx,hs,ht,ho⟩ := D.degree_two_through_carrier B.completedHub
    (B.syndromeStar_hub_degree_two hsize) hz
  have hneighbors : ∀ v, B.syndromeStar.Adj B.completedHub v → v = p ∨ v = q := by
    intro v hv
    have h := (B.syndromeStar_hub_adj v).mp hv
    rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at h
    exact h.imp Subtype.ext Subtype.ext
  obtain ⟨N,hNs,hNt,hNe⟩ := B.retainedThroughReplacement B.syndromeStar
    B.syndromeStar_le_completedStar p q hneighbors (D.path j) hx hs ht M hM hne hm
  refine ⟨j,N,hNs,hNt,ho,?_⟩
  let b := ((D.path j).takeTo B.completedHub hx hs).walk.reverse.snd
  let c := ((D.path j).dropFrom B.completedHub hx ht).walk.snd
  have hadj := (D.path j).release_attachments_adj B.completedHub hx hs ht
  have hbc := (D.path j).release_attachments_ne B.completedHub hx hs ht
  have hpair : (b = p ∧ c = q) ∨ (b = q ∧ c = p) := by
    rcases hneighbors b hadj.1 with hb | hb <;> rcases hneighbors c hadj.2 with hc | hc
    · exact (hbc (hb.trans hc.symm)).elim
    · exact Or.inl ⟨hb,hc⟩
    · exact Or.inr ⟨hb,hc⟩
    · exact (hbc (hb.trans hc.symm)).elim
  intro e
  have he := hNe e
  change N.walk.edges.count e +
    ([s(B.label 0,b.val),s(B.label 0,c.val)] : List (Sym2 V)).count e = _ at he
  rcases hpair with ⟨hb,hc⟩ | ⟨hb,hc⟩
  · simpa only [hb,hc] using he
  · simpa only [hb,hc,List.count_cons,List.count_nil,Nat.add_zero,Nat.zero_add,
      Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using he

end Gallai.WholeBowtie
