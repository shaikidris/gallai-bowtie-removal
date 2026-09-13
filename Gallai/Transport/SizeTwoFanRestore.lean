/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoFanPassing
import Gallai.Inputs.ThreeEdgeFanRestore

/-! # Apply the three Fan restorations to the actual initial graph

The final identification of this restored graph with G is a separate edge
coverage obligation; no graph equality is assumed in this construction.
-/
namespace Gallai.WholeBowtie

open Certificate
open scoped Finset

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

def sizeTwoFanRestored (A : B.AnchorNumbering) : SimpleGraph V :=
  (((B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A) ⊔
    SimpleGraph.edge (B.label 0) (A 3).val) ⊔
    SimpleGraph.edge (B.label 2) (B.label 0)) ⊔
    SimpleGraph.edge (B.label 2) (A 3).val

/-- A finite missing core edge is genuinely absent in the ambient initial graph. -/
theorem sizeTwoFan_initial_missing (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (i : Fin 5) (t : Star.Vertex)
    (hmissing : s(CompletedStar.core i,t) ∉
      SizeTwo.Fan.retainedEdges ∪ SizeTwo.Fan.initialEdges) :
    ¬ (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj (B.label i) (B.completedLabel A t) := by
  intro ha
  obtain ⟨u,hu,he⟩ := (B.sizeTwoFan_initial_core_adj A hSigma i _).mp ha
  have hut : u = t := B.completedLabel_injective A he
  exact hmissing (hut ▸ hu)

/-- The actual auxiliary, without any extra passing-bound premise, restores
all three missing edges at a total cost of exactly two paths. -/
theorem sizeTwoFan_restored_decomposition (A : B.AnchorNumbering)
    (hstate : B.completedStarState A = SizeTwo.Fan.state)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) :
    ∃ P : Decomposition (B.sizeTwoFanRestored A), P.size = D.size + 2 ∧ ∀ v,
      P.endpointCount v + (if (A 3).val = v then 2 else 0) =
        (D.map (Function.Embedding.subtype _)).endpointCount v +
        (B.sizeTwoFanAddedDecomposition A).endpointCount v +
        if B.label 2 = v then 2 else 0 := by
  classical
  let : DecidableRel (B.sizeTwoFanAux ⊔ B.sizeTwoFanAdded A).Adj := Classical.decRel _
  obtain ⟨E,hsize,he⟩ := B.sizeTwoFan_initial_decomposition A hstate hSigma D
  obtain ⟨hanchor,ha,hs⟩ := B.sizeTwoFan_initial_reserves A D E he
  obtain ⟨hpassx,hpassb⟩ := B.sizeTwoFan_initial_passing A hSigma E hanchor ha
  have hxb : B.label 0 ≠ B.label 2 := fun hh =>
    (by decide : (0 : Fin 5) ≠ 2) (B.label.injective hh)
  have hxs : B.label 0 ≠ (A 3).val := B.label_ne_numberedAnchor A 0 3
  have hbs : B.label 2 ≠ (A 3).val := B.label_ne_numberedAnchor A 2 3
  have hmissingxs := B.sizeTwoFan_initial_missing A hSigma 0 .s (by decide)
  have hmissingbx := B.sizeTwoFan_initial_missing A hSigma 2 .x (by decide)
  have hmissingbs := B.sizeTwoFan_initial_missing A hSigma 2 .s (by decide)
  obtain ⟨P,hP,hbalance⟩ := E.three_edge_fan_restore (B.label 0) (B.label 2) (A 3).val
    hxb hxs hbs hmissingxs hmissingbx hmissingbs hs hpassx hpassb
  refine ⟨P,hP.trans hsize,?_⟩
  intro v
  exact (hbalance v).trans (congrArg (fun n => n + if B.label 2 = v then 2 else 0) (he v))

end Gallai.WholeBowtie
