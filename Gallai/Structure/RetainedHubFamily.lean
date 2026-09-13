/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedFamilyDegrees
import Gallai.Structure.ComponentAdmissibility

/-! # Full admissibility for retained-hub smaller families

The retained centre is not a member of the smaller bowtie family: its small
surviving row puts it under the residual E-degree cap instead.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (H : SimpleGraph (Bs 0).StarSurvivor) [DecidableRel H.Adj]
variable (hpar : ∀ v : (Bs 0).StarSurvivor, Even (H.degree v) ↔ Even (G.degree v.val))
variable (hadj : ∀ u v : (Bs 0).StarSurvivor, Even (G.degree u.val) →
  (H.Adj u v ↔ G.Adj u.val v.val))

/-- The successor-indexed family omits the now nonexceptional retained hub. -/
noncomputable def retainedFamily : Fin t → WholeBowtie H := fun i =>
  (Bs 0).otherRetainedBowtie (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) H hpar hadj

/-- The surviving whole components remain pairwise disjoint. -/
theorem retainedFamily_disjoint (i j : Fin t) (hij : i ≠ j) :
    Disjoint (retainedFamily Bs hd H hpar hadj i).vertices
      (retainedFamily Bs hd H hpar hadj j).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp (hd i.succ j.succ (by simpa using hij))
    (((Bs 0).otherRetained_mem_vertices (Bs i.succ)
      (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) H hpar hadj v).mp hv)
    (((Bs 0).otherRetained_mem_vertices (Bs j.succ)
      (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) H hpar hadj v).mp hw)

/-- Every surviving local interface remains supported. -/
theorem retainedFamily_supported (hs : ∀ i, Supported (Bs i)) (i : Fin t) :
    Supported (retainedFamily Bs hd H hpar hadj i) :=
  (Bs 0).otherRetained_supported (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) H hpar hadj (hs i.succ)

/-- Full admissibility descends, with the retained centre under the residual cap. -/
theorem retainedFamily_admissible (hr : ((Bs 0).row 0).card ≤ 3)
    (d : Option V) (e : Option (Bs 0).StarSurvivor)
    (h : Admissible Bs d) (he : ∀ v, v ∈ e ↔ v.val ∈ d) :
    Admissible (retainedFamily Bs hd H hpar hadj) e := by
  refine ⟨retainedFamily_disjoint Bs hd H hpar hadj,
    retainedFamily_supported Bs hd H hpar hadj h.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨hev, hpv, hout⟩ := h.2.2.1 v.val ((he v).mp hv)
    refine ⟨(hpar v).mpr hev, ?_, ?_⟩
    · rwa [(Bs 0).retainedAux_degree_even_outside H hadj v hev (hout 0)]
    · intro i hi
      exact hout i.succ (((Bs 0).otherRetained_mem_vertices (Bs i.succ)
        (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) H hpar hadj v).mp hi)
  · intro v hv hout hne
    by_cases hx : v.val = (Bs 0).label 0
    · have heq : v = (Bs 0).completedHub := Subtype.ext hx
      subst v
      exact (Bs 0).retainedAux_hub_cap H hadj hr
    · apply ((Bs 0).retainedAux_eDegree_le H hpar hadj v).trans
      apply h.2.2.2 v.val ((hpar v).mp hv)
      · intro i
        refine Fin.cases (fun hi => hx ((Bs 0).survivor_mem_vertices v hi))
          (fun j => ?_) i
        intro hi
        exact hout j (((Bs 0).otherRetained_mem_vertices (Bs j.succ)
          (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) H hpar hadj v).mpr hi)
      · intro y hy hval
        have hvd : v.val ∈ d := hval ▸ hy
        exact hne v ((he v).mpr hvd) rfl

/-- The undesignated family descends without adding a designation. -/
theorem retainedFamily_admissible_none (hr : ((Bs 0).row 0).card ≤ 3)
    (h : Admissible Bs none) : Admissible (retainedFamily Bs hd H hpar hadj) none :=
  retainedFamily_admissible Bs hd H hpar hadj hr none none h (by simp)

/-- The original outside designated vertex keeps positive even degree. -/
theorem retainedFamily_admissible_some (hr : ((Bs 0).row 0).card ≤ 3)
    (y : (Bs 0).StarSurvivor) (h : Admissible Bs (some y.val)) :
    Admissible (retainedFamily Bs hd H hpar hadj) (some y) := by
  apply retainedFamily_admissible Bs hd H hpar hadj hr (some y.val) (some y) h
  intro v
  simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]

end Gallai.Composition
