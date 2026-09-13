/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtiePrivateDeletion
import Gallai.Structure.PrivateDeletionCap

/-! # Remaining family after an inactive deletion in the first bowtie

This module transports actual whole bowties and their local classes. The
residual E-degree cap is a separate obligation, not a hypothesis hidden here.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (I : Finset (Fin 5)) (hi : ∀ i ∈ I, (Bs 0).row i = ∅)

/-- Delete the first family member from the index, retaining the other whole components. -/
noncomputable def privateFamily :
    Fin t → WholeBowtie ((Bs 0).privateDeletion I) := fun i =>
  (Bs 0).otherPrivateBowtie (Bs i.succ) (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) I hi

/-- Remaining bowtie vertex sets stay pairwise disjoint in the auxiliary. -/
theorem privateFamily_disjoint (i j : Fin t) (hij : i ≠ j) :
    Disjoint (privateFamily Bs hd I hi i).vertices
      (privateFamily Bs hd I hi j).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  have hv' := ((Bs 0).otherPrivate_mem_vertices (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) I hi v).mp hv
  have hw' := ((Bs 0).otherPrivate_mem_vertices (Bs j.succ)
    (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) I hi v).mp hw
  exact Finset.disjoint_left.mp (hd i.succ j.succ (by simpa using hij)) hv' hw'

/-- All manuscript-supported local types remain supported. -/
theorem privateFamily_supported (hs : ∀ i, Supported (Bs i)) (i : Fin t) :
    Supported (privateFamily Bs hd I hi i) :=
  (Bs 0).otherPrivate_supported (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) I hi (hs i.succ)

/-- A surviving designated vertex retains parity, positivity and exclusion from the family. -/
theorem privateFamily_designated
    (y : {v : V // v ∉ I.map (Bs 0).label})
    (he : Even (G.degree y.val)) (hp : 0 < G.degree y.val)
    (hout : ∀ i, y.val ∉ (Bs i).vertices) :
    Even (((Bs 0).privateDeletion I).degree y) ∧
      0 < ((Bs 0).privateDeletion I).degree y ∧
      ∀ i, y ∉ (privateFamily Bs hd I hi i).vertices := by
  rw [(Bs 0).privateDeletion_degree_outside I hi y (hout 0)]
  refine ⟨he, hp, ?_⟩
  intro i hv
  exact hout i.succ (((Bs 0).otherPrivate_mem_vertices (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) I hi y).mp hv)

/-- The residual cap passes to the auxiliary once two inactive vertices are deleted. -/
theorem privateFamily_cap (hcard : 2 ≤ I.card)
    (v : {w : V // w ∉ I.map (Bs 0).label})
    (hout : ∀ i, v ∉ (privateFamily Bs hd I hi i).vertices)
    (hcap : (∀ i, v.val ∉ (Bs i).vertices) → eDegree G v.val ≤ 3) :
    eDegree ((Bs 0).privateDeletion I) v ≤ 3 := by
  by_cases hv : v.val ∈ (Bs 0).vertices
  · have h := (Bs 0).privateDeletion_eDegree_inside I hi v hv
    omega
  · apply ((Bs 0).privateFamilyDeletion_eDegree_le I hi v).trans
    apply hcap
    intro i
    refine Fin.cases hv (fun j => ?_) i
    intro hm
    exact hout j (((Bs 0).otherPrivate_mem_vertices (Bs j.succ)
      (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) I hi v).mpr hm)

/-- The complete undesignated family hypotheses pass to the deletion auxiliary. -/
theorem privateFamily_admissible_none (hcard : 2 ≤ I.card)
    (h : Admissible Bs none) :
    Admissible (privateFamily Bs hd I hi) none := by
  refine ⟨privateFamily_disjoint Bs hd I hi,
    privateFamily_supported Bs hd I hi h.2.1, ?_, ?_⟩
  · simp
  · intro v he hout _
    apply privateFamily_cap Bs hd I hi hcard v hout
    intro hv
    exact h.2.2.2 v.val ((Bs 0).privateFamilyDeletion_even_original I hi v he) hv
      (by simp)

/-- The complete designated hypotheses pass to the same deletion auxiliary. -/
theorem privateFamily_admissible_some (hcard : 2 ≤ I.card)
    (y : {v : V // v ∉ I.map (Bs 0).label})
    (h : Admissible Bs (some y.val)) :
    Admissible (privateFamily Bs hd I hi) (some y) := by
  refine ⟨privateFamily_disjoint Bs hd I hi,
    privateFamily_supported Bs hd I hi h.2.1, ?_, ?_⟩
  · intro z hz
    have hz' : z = y := by simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    subst z
    have hy := h.2.2.1 y.val (by simp)
    exact privateFamily_designated Bs hd I hi y hy.1 hy.2.1 hy.2.2
  · intro v he hout hne
    apply privateFamily_cap Bs hd I hi hcard v hout
    intro hv
    apply h.2.2.2 v.val ((Bs 0).privateFamilyDeletion_even_original I hi v he) hv
    intro z hz heq
    have hz' : z = y.val := by simpa only [Option.mem_def, Option.some.injEq, eq_comm] using hz
    exact hne y (by simp) (Subtype.ext (heq.trans hz'))

end Gallai.Composition
