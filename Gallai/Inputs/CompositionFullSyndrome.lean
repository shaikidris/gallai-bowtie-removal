/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarFamily
import Gallai.Certificates.CompletedStarCoverage
import Gallai.Inputs.CompletedStarBudget
import Gallai.Transport.CompletedStarCoverage

/-! # Full-syndrome induction step for composable families

Certificate reconstruction consumes an arbitrary smaller-family decomposition;
the one-exception endpoint budget is not used in this induction step.
-/
namespace Gallai.Composition
open Certificate.CompletedStar
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Full-syndrome reconstruction works with every auxiliary decomposition. -/
theorem full_syndrome_lift (B : WholeBowtie G) (hfour : B.anchors.card = 4)
    (hfull : B.syndrome = B.anchors) (D : Decomposition B.completedStar) :
    ∃ E : Decomposition G, E.size ≤ D.size + 2 ∧
      ∀ v : B.StarSurvivor, v.val ∉ B.vertices →
        D.endpointCount v ≤ E.endpointCount v.val := by
  obtain ⟨repl, added, hr⟩ := Coverage.all_records
    (B.completedStarState (B.carrierAnchorOrder D hfour))
    (B.completedStarState_full D hfour hfull)
    (profileInterface (Star.profileOf D B.completedHub))
  exact ⟨B.completedReconstruction D hfour hr,
    B.completedReconstruction_budget D hfour hr,
    B.completedReconstruction_endpoint_reserve D hfour hr⟩

/-- Consume the smaller-family hypothesis in the connected full-syndrome auxiliary. -/
theorem full_syndrome_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (hfour : (Bs 0).anchors.card = 4) (hfull : (Bs 0).syndrome = (Bs 0).anchors)
    (ih : ∀ (he : Even (Bs 0).anchors.card)
      (cols : ∀ w ∈ (Bs 0).anchors, Odd (G.neighborFinset w ∩ (Bs 0).vertices).card)
      (d' : Option (Bs 0).StarSurvivor),
      (Bs 0).completedStar.Connected →
      Admissible (completedFamily Bs h.1 he cols) d' →
      Conclusion (Bs 0).completedStar d') : Conclusion G d := by
  have he : Even (Bs 0).anchors.card := by rw [hfour]; decide
  have cols := (Bs 0).full_syndrome_columns hfull
  have hc' := (Bs 0).completedStar_connected hc
  have hn := (Bs 0).completedStar_card
  cases d with
  | none =>
    have had := completedFamily_admissible_none Bs h.1 he cols h
    obtain ⟨D, hD, _⟩ := ih he cols none hc' had
    obtain ⟨E, hE, _⟩ := full_syndrome_lift (Bs 0) hfour hfull D
    refine ⟨E, ?_, by simp⟩
    omega
  | some y =>
    have hy := h.2.2.1 y (by simp)
    let y' := (Bs 0).completedOutside y (hy.2.2 0)
    have had := completedFamily_admissible_some Bs h.1 he cols hc y' h
    obtain ⟨D, hD, hends⟩ := ih he cols (some y') hc' had
    obtain ⟨E, hE, hr⟩ := full_syndrome_lift (Bs 0) hfour hfull D
    refine ⟨E, ?_, ?_⟩
    · omega
    · intro z hz
      have hz' : z = y := by
        simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
      subst z
      exact (hends y' (by simp)).trans (hr y' (hy.2.2 0))

end Gallai.Composition
