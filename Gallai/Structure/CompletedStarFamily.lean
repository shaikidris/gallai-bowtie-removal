/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtieCompletedStar

/-! # Admissible remaining families in the completed-star auxiliary -/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (hcard : Even (Bs 0).anchors.card)
variable (hcols : ∀ w ∈ (Bs 0).anchors, Odd (G.neighborFinset w ∩ (Bs 0).vertices).card)

/-- The smaller family retains all components except the repaired first bowtie. -/
noncomputable def completedFamily : Fin t → WholeBowtie (Bs 0).completedStar := fun i =>
  (Bs 0).otherCompletedBowtie (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hcard hcols

/-- The remaining family stays pairwise disjoint. -/
theorem completedFamily_disjoint (i j : Fin t) (hij : i ≠ j) :
    Disjoint (completedFamily Bs hd hcard hcols i).vertices
      (completedFamily Bs hd hcard hcols j).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hv' := ((Bs 0).otherCompleted_mem_vertices (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hcard hcols v).mp hv
  have hw' := ((Bs 0).otherCompleted_mem_vertices (Bs j.succ)
    (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hcard hcols v).mp hw
  exact Finset.disjoint_left.mp (hd i.succ j.succ (by simpa using hij)) hv' hw'

/-- All the other supported classes survive. -/
theorem completedFamily_supported (hs : ∀ i, Supported (Bs i)) (i : Fin t) :
    Supported (completedFamily Bs hd hcard hcols i) :=
  (Bs 0).otherCompleted_supported (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hcard hcols (hs i.succ)

/-- The retained hub has zero E-degree and all other residual caps transfer. -/
theorem completedFamily_cap (v : (Bs 0).StarSurvivor)
    (he : Even ((Bs 0).completedStar.degree v))
    (hout : ∀ i, v ∉ (completedFamily Bs hd hcard hcols i).vertices)
    (hcap : (∀ i, v.val ∉ (Bs i).vertices) → eDegree G v.val ≤ 3) :
    eDegree (Bs 0).completedStar v ≤ 3 := by
  by_cases hx : v = (Bs 0).completedHub
  · subst v
    rw [(Bs 0).completedHub_eDegree hcard hcols]
    omega
  · have hxv : v.val ≠ (Bs 0).label 0 := fun h => hx (Subtype.ext h)
    apply ((Bs 0).completedStar_eDegree_le hcard hcols v hxv
      (((Bs 0).completedStar_even_iff hcard hcols v).mp he)).trans
    apply hcap
    intro i
    refine Fin.cases (fun h => hxv ((Bs 0).survivor_mem_vertices v h)) (fun j => ?_) i
    intro hm
    exact hout j (((Bs 0).otherCompleted_mem_vertices (Bs j.succ)
      (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hcard hcols v).mpr hm)

/-- Full undesignated admissibility for the completed auxiliary. -/
theorem completedFamily_admissible_none (h : Admissible Bs none) :
    Admissible (completedFamily Bs hd hcard hcols) none := by
  refine ⟨completedFamily_disjoint Bs hd hcard hcols,
    completedFamily_supported Bs hd hcard hcols h.2.1, by simp, ?_⟩
  intro v he hout _
  apply completedFamily_cap Bs hd hcard hcols v he hout
  intro hv
  exact h.2.2.2 v.val (((Bs 0).completedStar_even_iff hcard hcols v).mp he) hv (by simp)

/-- Full designated admissibility, including actual positive auxiliary degree. -/
theorem completedFamily_admissible_some (hc : G.Connected)
    (y : (Bs 0).StarSurvivor) (h : Admissible Bs (some y.val)) :
    Admissible (completedFamily Bs hd hcard hcols) (some y) := by
  refine ⟨completedFamily_disjoint Bs hd hcard hcols,
    completedFamily_supported Bs hd hcard hcols h.2.1, ?_, ?_⟩
  · intro z hz
    have hz' : z = y := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    subst z
    have hy := h.2.2.1 y.val (by simp)
    have hxy : (Bs 0).completedHub ≠ y := by
      intro he
      have he' : (Bs 0).label 0 = y.val := congrArg Subtype.val he
      exact hy.2.2 0 (he' ▸ ((Bs 0).mem_vertices _).mpr ((Bs 0).label_mem_component 0))
    letI : Nontrivial (Bs 0).StarSurvivor := ⟨⟨(Bs 0).completedHub, y, hxy⟩⟩
    refine ⟨((Bs 0).completedStar_even_iff hcard hcols y).mpr hy.1,
      ((Bs 0).completedStar_connected hc).preconnected.degree_pos_of_nontrivial y, ?_⟩
    intro i hv
    exact hy.2.2 i.succ (((Bs 0).otherCompleted_mem_vertices (Bs i.succ)
      (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hcard hcols y).mp hv)
  · intro v he hout hne
    apply completedFamily_cap Bs hd hcard hcols v he hout
    intro hv
    apply h.2.2.2 v.val (((Bs 0).completedStar_even_iff hcard hcols v).mp he) hv
    intro z hz heq
    have hz' : z = y.val := by
      simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    exact hne y (by simp) (Subtype.ext (heq.trans hz'))

end Gallai.Composition
