/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ZeroSyndromeAllRecords
import Gallai.Structure.ZeroSyndromeRows
import Gallai.Transport.ZeroSyndromeReconstruction

/-! # High-activity four-anchor zero-syndrome removal

The puncture need not be connected. Its actual component budget selects the
two-credit or one-credit certificate, with the latter consuming the proved
three-component separation resource.
-/
namespace Gallai.WholeBowtie
open Certificate.ZeroSyndrome
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Exhaustive records and component credits produce the actual Gallai-budget
decomposition, exposing the designated even vertex at least twice. -/
theorem high_zero_four_anchor_removal (hz : B.syndrome = ∅) (hc : G.Connected)
    (hA : #B.anchors = 4) (ha : 3 ≤ B.activity)
    (y : {v : V // v ∉ B.vertices}) (hy : Even (G.degree y.val))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y.val → eDegree G v ≤ 3) :
    ∃ P : Decomposition G, P.size ≤ (Fintype.card V + 1) / 2 ∧
      2 ≤ P.endpointCount y.val := by
  classical
  let A := B.anchorNumbering hA
  have hs := B.completedStarState_highZero A hz ha
  obtain ⟨D, hyD, hcredit⟩ := B.zero_puncture_endpoint_credit hz hc (by omega) y hy hcap
  obtain ⟨f, hf⟩ := B.zero_anchor_carriers hz D
  rcases hcredit with htwo | ⟨hone, hthree⟩
  · obtain ⟨tails, added, hr⟩ := all_two_records _ hs _ _ (B.zero_interface_mem A D f hf)
    refine ⟨B.zeroReconstruction A D f hf tails added hr,
      (B.zeroReconstruction_budget A D f hf tails added hr).trans htwo, ?_⟩
    exact hyD.trans (B.zeroReconstruction_endpoint_reserve A D f hf tails added hr y hy)
  · obtain ⟨tails, added, hr⟩ := all_one_records _ hs _ (B.zero_separated_mem A hc hthree)
    obtain ⟨P, hp, hpy⟩ := B.zeroOneCredit_reconstruction A D f hf tails added hr y hy
    exact ⟨P, hp.trans hone, hyD.trans hpy⟩

end Gallai.WholeBowtie
