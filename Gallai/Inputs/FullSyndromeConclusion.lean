/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCoverage
import Gallai.Inputs.CompletedStarBudget
import Gallai.Transport.CompletedStarCoverage

/-! # Unconditional four-anchor full-syndrome removal

The actual graph supplies its row state and carrier interface. Exhaustive
coverage supplies the record; neither is a premise of the public theorem.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Full-syndrome removal at arbitrary order, exposing the other exception. -/
theorem full_syndrome_endpoint (hfour : #B.anchors = 4)
    (hfull : B.syndrome = B.anchors) (hc : G.Connected)
    (y : V) (hy : y ∉ B.vertices) (hyEven : Even (G.degree y))
    (hcap : ∀ v, Even (G.degree v) → v ≠ B.label 0 → v ≠ y → eDegree G v ≤ 3) :
    ∃ E : Decomposition G,
      E.size ≤ (Fintype.card V + 1) / 2 ∧ 2 ≤ E.endpointCount y := by
  obtain ⟨D, hD, hDy⟩ := B.completedStar_endpoint_budget hfour hfull hc y hy hyEven hcap
  obtain ⟨repl, added, hr⟩ := Coverage.all_records
    (B.completedStarState (B.carrierAnchorOrder D hfour))
    (B.completedStarState_full D hfour hfull)
    (profileInterface (Star.profileOf D B.completedHub))
  refine ⟨B.completedReconstruction D hfour hr,
    (B.completedReconstruction_budget D hfour hr).trans hD, ?_⟩
  exact hDy.trans (B.completedReconstruction_endpoint_reserve D hfour hr
    (B.completedOutside y hy) hy)

end Gallai.WholeBowtie
