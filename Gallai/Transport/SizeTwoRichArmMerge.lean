/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SyndromeStarCarrier

/-! # Joining a released hub arm to a remote reserve carrier

Component separation supplies all old-support avoidance. The released arm may
be nil; the connector uses only its two attachments and the released hub among
old vertices. Different reserve carriers need not avoid one another.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An original-graph connector merges a hub-component arm with a remote
endpoint carrier, with literal endpoints and an exact edge-list identity. -/
theorem sizeTwo_rich_arm_merge (w : B.StarSurvivor)
    (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    {a b : B.StarSurvivor} (L : B.syndromeStar.Walk a b)
    (hL : L.IsPath) (hxL : B.completedHub ∉ L.support)
    (hcomp : B.syndromeStar.Reachable B.completedHub a)
    (Q : NonemptyPath B.syndromeStar) (hQ : Q.finish = w)
    (M : G.Walk b.val Q.finish.val) (hM : M.IsPath) (hne : ¬ M.Nil)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = Q.finish.val ∨ v.val = B.label 0) :
    ∃ N : NonemptyPath G,
      N.start = a.val ∧ N.finish = Q.start.val ∧
      N.walk.edges = (L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
        Q.walk.reverse.edges.map (Sym2.map Subtype.val) := by
  have hxR : B.completedHub ∉ Q.walk.reverse.support := by
    intro hx
    have hx' : B.completedHub ∈ Q.walk.support := by simpa using hx
    exact hsep (hQ ▸ (Q.walk.dropUntil B.completedHub hx').reachable)
  have hLR : L.support.Disjoint Q.walk.reverse.support := by
    apply List.disjoint_left.mpr
    intro v hvL hvR
    have hvQ : v ∈ Q.walk.support := by simpa using hvR
    exact hsep ((hcomp.trans (L.takeUntil v hvL).reachable).trans
      (hQ ▸ (Q.walk.dropUntil v hvQ).reachable))
  refine ⟨B.retainedThroughCarrier B.syndromeStar B.syndromeStar_le_completedStar
    L Q.walk.reverse M hL Q.isPath.reverse hM hne hLR hxL hxR hm, rfl, rfl, ?_⟩
  exact B.retainedThroughCarrier_edges B.syndromeStar B.syndromeStar_le_completedStar
    L Q.walk.reverse M hL Q.isPath.reverse hM hne hLR hxL hxR hm

end Gallai.WholeBowtie
