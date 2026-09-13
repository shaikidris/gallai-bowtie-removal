/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedRelabeling
import Gallai.Structure.ComposableBowties

/-! # Relabeling the selected bowtie without changing the ambient family -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]

/-- Replace the head's labels, retaining every other bowtie. -/
def retainedRelabeledFamily {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G) (c : Fin 8) :
    Fin (t + 1) → WholeBowtie G :=
  Fin.cases ((Bs 0).retainedRelabel c) (fun j => Bs j.succ)

/-- Every family member has exactly the same vertex set after normalization. -/
theorem retainedRelabeledFamily_vertices {t : ℕ}
    (Bs : Fin (t + 1) → WholeBowtie G) (c : Fin 8) (i : Fin (t + 1)) :
    (retainedRelabeledFamily Bs c i).vertices = (Bs i).vertices := by
  refine Fin.cases ?_ (fun j => ?_) i
  · exact (Bs 0).retainedRelabel_vertices c
  · rfl

/-- Small-anchor support and all global hypotheses survive normalization.
The designated vertex and any overlaps among odd anchor sets are unchanged. -/
theorem retainedRelabeledFamily_admissible {t : ℕ}
    (Bs : Fin (t + 1) → WholeBowtie G) (c : Fin 8) (d : Option V)
    (h : Admissible Bs d) (hA : (Bs 0).anchors.card ≤ 3) :
    Admissible (retainedRelabeledFamily Bs c) d := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro i j hij
    simpa only [retainedRelabeledFamily_vertices] using h.1 i j hij
  · intro i
    refine Fin.cases ?_ (fun j => h.2.1 j.succ) i
    apply Or.inr (Or.inl ?_)
    change ((Bs 0).retainedRelabel c).anchors.card ≤ 3
    rwa [(Bs 0).retainedRelabel_anchors]
  · intro y hy
    obtain ⟨he, hp, hout⟩ := h.2.2.1 y hy
    exact ⟨he, hp, fun i => by simpa only [retainedRelabeledFamily_vertices] using hout i⟩
  · intro v he hout hne
    exact h.2.2.2 v he (fun i => by
      simpa only [retainedRelabeledFamily_vertices] using hout i) hne

end Gallai.Composition
