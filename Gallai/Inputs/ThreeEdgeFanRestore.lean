/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.InwardStar
import Gallai.Inputs.MatchingRestore

/-!
# Three-edge restoration for the size-two Fan exception

Restore xs towards x, bx towards b, and bs towards b. The initial donor
reserve of three pays for two endpoints at b; the intermediate endpoint at
x is borrowed and returned. This isolates the restoration step, not the
graph-specific construction of its initial decomposition.
-/

namespace Gallai.Decomposition

open scoped Finset

universe u

variable {V : Type u} {G : SimpleGraph V} [DecidableEq V]
  [Fintype V] [DecidableRel G.Adj]

/-- Three missing edges are restored at zero path cost under the precise
passing bounds used by the exceptional Fan reconstruction. -/
theorem three_edge_fan_restore (D : Decomposition G) (x b s : V)
    (hxb : x ≠ b) (hxs : x ≠ s) (hbs : b ≠ s)
    (hxs_missing : ¬ G.Adj x s) (hbx_missing : ¬ G.Adj b x)
    (hbs_missing : ¬ G.Adj b s)
    (hs : 3 ≤ D.endpointCount s)
    (hpassx : #{v ∈ G.neighborFinset x | D.endpointCount v = 0} ≤ 2)
    (hpassb : #{v ∈ G.neighborFinset b | D.endpointCount v = 0} = 0) :
    ∃ E : Decomposition
        (((G ⊔ SimpleGraph.edge x s) ⊔ SimpleGraph.edge b x) ⊔ SimpleGraph.edge b s),
      E.size = D.size ∧ ∀ v,
        E.endpointCount v + (if s = v then 2 else 0) =
          D.endpointCount v + if b = v then 2 else 0 := by
  classical
  obtain ⟨D₁, hsize₁, hbal₁⟩ := D.single_edge_addibility x s hxs hxs_missing
    (by omega)
  have hpass₁ := D.passing_neighbors_mono_of_donor_not_adj x s b D₁
    hxb.symm hbs hbal₁ hbs_missing
  have hbx₁ : ¬ (G ⊔ SimpleGraph.edge x s).Adj b x := by
    simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, hbx_missing, hxb.symm, hbs]
  have hx₁ := hbal₁ x
  simp only [Ne.symm hxs, if_false, if_true, Nat.add_zero] at hx₁
  obtain ⟨D₂, hsize₂, hbal₂⟩ := D₁.single_edge_addibility b x hxb.symm hbx₁
    (by omega)
  have hpass₂ := D₁.passing_neighbors_le_add_one b x D₂ hbal₂
  have hbs₂ : ¬ ((G ⊔ SimpleGraph.edge x s) ⊔ SimpleGraph.edge b x).Adj b s := by
    simp [SimpleGraph.sup_adj, SimpleGraph.edge_adj, hbs_missing,
      hxb.symm, hxs.symm, hbs, hbs.symm]
  have hs₁ := hbal₁ s
  have hs₂ := hbal₂ s
  simp only [if_true, hxs, hbs, if_false, Nat.add_zero] at hs₁ hs₂
  obtain ⟨D₃, hsize₃, hbal₃⟩ := D₂.single_edge_addibility b s hbs hbs₂
    (by omega)
  refine ⟨D₃, hsize₃.trans (hsize₂.trans hsize₁), ?_⟩
  intro v
  have h₁ := hbal₁ v
  have h₂ := hbal₂ v
  have h₃ := hbal₃ v
  split_ifs at * <;> omega

end Gallai.Decomposition
