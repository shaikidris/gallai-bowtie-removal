/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedHubAuxiliary
import Gallai.Transport.CompletedStarCarrier

/-! # Reuse completed-star splicing for retained original-edge auxiliaries -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Private deletion is a subgraph of star completion on the same survivors. -/
theorem retainedHub_le_completedStar : B.retainedHubGraph ≤ B.completedStar :=
  fun _ _ h => Or.inl h

/-- Deleting an original repair edge retains this same inclusion. -/
theorem retainedHubRepair_le_completedStar (p q : B.StarSurvivor)
    (hpq : G.Adj p.val q.val) : B.retainedHubRepair p q ≤ B.completedStar := by
  intro u v h
  change (toggleEdge B.retainedHubGraph p q).Adj u v at h
  simp only [toggleEdge, show B.retainedHubGraph.Adj p q from hpq, if_true] at h
  exact Or.inl h.1

variable (H : SimpleGraph B.StarSurvivor) (hle : H ≤ B.completedStar)

/-- Identity inclusion into the already-supported carrier ambient graph. -/
def retainedLiftWalk {a b : B.StarSurvivor} (P : H.Walk a b) :
    B.completedStar.Walk a b := P.map (SimpleGraph.Hom.ofLE hle)

theorem retainedLiftWalk_support {a b : B.StarSurvivor} (P : H.Walk a b) :
    (B.retainedLiftWalk H hle P).support = P.support := by
  rw [retainedLiftWalk, SimpleGraph.Walk.support_map]
  change P.support.map id = P.support
  simp

theorem retainedLiftWalk_edges {a b : B.StarSurvivor} (P : H.Walk a b) :
    (B.retainedLiftWalk H hle P).edges = P.edges := by
  rw [retainedLiftWalk, SimpleGraph.Walk.edges_map]
  change P.edges.map (Sym2.map id) = P.edges
  simp

theorem retainedLiftWalk_isPath {a b : B.StarSurvivor} (P : H.Walk a b)
    (hp : P.IsPath) : (B.retainedLiftWalk H hle P).IsPath :=
  hp.map Function.injective_id

/-- Released through pieces use the checked completed-star splice unchanged.
Old pieces may be nil and may visit any other anchor. -/
def retainedThroughCarrier {a b c d : B.StarSurvivor}
    (L : H.Walk a b) (R : H.Walk c d) (M : G.Walk b.val c.val)
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0) : NonemptyPath G :=
  B.completedThroughCarrier (B.retainedLiftWalk H hle L) (B.retainedLiftWalk H hle R)
    M (B.retainedLiftWalk_isPath H hle L hL)
    (B.retainedLiftWalk_isPath H hle R hR) hM hne
    (by simpa only [B.retainedLiftWalk_support] using hLR)
    (by simpa only [B.retainedLiftWalk_support] using hxL)
    (by simpa only [B.retainedLiftWalk_support] using hxR) hm

/-- The reused splice preserves the exact old-edge/connector accounting. -/
theorem retainedThroughCarrier_edges {a b c d : B.StarSurvivor}
    (L : H.Walk a b) (R : H.Walk c d) (M : G.Walk b.val c.val)
    (hL : L.IsPath) (hR : R.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0) :
    (B.retainedThroughCarrier H hle L R M hL hR hM hne hLR hxL hxR hm).walk.edges =
      (L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
        R.edges.map (Sym2.map Subtype.val) := by
  unfold retainedThroughCarrier
  simpa only [B.retainedLiftWalk_edges] using
    B.completedThroughCarrier_edges (B.retainedLiftWalk H hle L)
      (B.retainedLiftWalk H hle R) M (B.retainedLiftWalk_isPath H hle L hL)
      (B.retainedLiftWalk_isPath H hle R hR) hM hne
      (by simpa only [B.retainedLiftWalk_support] using hLR)
      (by simpa only [B.retainedLiftWalk_support] using hxL)
      (by simpa only [B.retainedLiftWalk_support] using hxR) hm

/-- A released terminal prefix reuses the same checked fresh-tail splice. -/
def retainedTerminalCarrier {a b : B.StarSurvivor} {c : V}
    (L : H.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0) : NonemptyPath G :=
  B.completedTerminalCarrier (B.retainedLiftWalk H hle L) M
    (B.retainedLiftWalk_isPath H hle L hL) hM hne
    (by simpa only [B.retainedLiftWalk_support] using hx) hm

/-- Exact terminal-prefix and tail edge accounting. -/
theorem retainedTerminalCarrier_edges {a b : B.StarSurvivor} {c : V}
    (L : H.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0) :
    (B.retainedTerminalCarrier H hle L M hL hM hne hx hm).walk.edges =
      L.edges.map (Sym2.map Subtype.val) ++ M.edges := by
  unfold retainedTerminalCarrier
  simpa only [B.retainedLiftWalk_edges] using
    B.completedTerminalCarrier_edges (B.retainedLiftWalk H hle L) M
      (B.retainedLiftWalk_isPath H hle L hL) hM hne
      (by simpa only [B.retainedLiftWalk_support] using hx) hm

end Gallai.WholeBowtie
