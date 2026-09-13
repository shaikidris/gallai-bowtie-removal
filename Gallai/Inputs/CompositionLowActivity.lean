/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.LowActivityReduction
import Gallai.Structure.PrivateDeletionFamily

/-! # The low-activity induction step for composable families

The explicit induction hypothesis concerns only the smaller remaining family.
This step is not the full induction theorem.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Consume smaller-family conclusions to close either designation case at low activity. -/
theorem low_activity_step {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
    (d : Option V) (h : Admissible Bs d) (hc : G.Connected)
    (ha : (Bs 0).activity ≤ 2)
    (ih : ∀ (I : Finset (Fin 5)) (hi : ∀ i ∈ I, (Bs 0).row i = ∅)
      (d' : Option {v : V // v ∉ I.map (Bs 0).label}),
      ((Bs 0).privateDeletion I).Connected →
      Admissible (privateFamily Bs h.1 I hi) d' →
      Conclusion ((Bs 0).privateDeletion I) d') : Conclusion G d := by
  obtain ⟨I, h0, hcard, hi, hlift⟩ := (Bs 0).exists_inactiveReduction ha
  have hc' := (Bs 0).privateDeletion_connected I h0 hi hc
  have hn := (Bs 0).privateDeletion_card I
  rw [hcard] at hn
  cases d with
  | none =>
    have had := privateFamily_admissible_none Bs h.1 I hi (by omega) h
    obtain ⟨D, hD, _⟩ := ih I hi none hc' had
    obtain ⟨E, hE, _⟩ := hlift D
    refine ⟨E, ?_, by simp⟩
    omega
  | some y =>
    have hy := h.2.2.1 y (by simp)
    have hyI : y ∉ I.map (Bs 0).label := by
      intro hm
      obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hm
      exact hy.2.2 0 (((Bs 0).mem_vertices _).mpr ((Bs 0).label_mem_component j))
    let y' : {v : V // v ∉ I.map (Bs 0).label} := ⟨y, hyI⟩
    have had := privateFamily_admissible_some Bs h.1 I hi (by omega) y' h
    obtain ⟨D, hD, he⟩ := ih I hi (some y') hc' had
    obtain ⟨E, hE, hends⟩ := hlift D
    refine ⟨E, ?_, ?_⟩
    · omega
    · intro z hz
      have hz' : z = y := by
        simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
      subst z
      rw [hends y' (hy.2.2 0)]
      exact he y' (by simp)

end Gallai.Composition
