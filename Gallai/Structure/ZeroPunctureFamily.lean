/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtieZeroPuncture
import Gallai.Structure.ComponentAdmissibility

/-! # Admissible families after zero-syndrome whole deletion

The puncture may be disconnected. These lemmas supply the family hypotheses
before component restriction; no path-budget theorem is assumed here.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (hz : (Bs 0).syndrome = ∅)

/-- The remaining family contains exactly the successors of the deleted bowtie. -/
noncomputable def zeroFamily : Fin t → WholeBowtie (Bs 0).puncture := fun i =>
  (Bs 0).otherZeroBowtie (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hz

/-- Whole deletion preserves pairwise disjointness of the remaining family. -/
theorem zeroFamily_disjoint (i j : Fin t) (hij : i ≠ j) :
    Disjoint (zeroFamily Bs hd hz i).vertices (zeroFamily Bs hd hz j).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp (hd i.succ j.succ (by simpa using hij))
    (((Bs 0).otherZero_mem_vertices (Bs i.succ)
      (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hz v).mp hv)
    (((Bs 0).otherZero_mem_vertices (Bs j.succ)
      (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hz v).mp hw)

/-- The remaining local interfaces keep their supported class. -/
theorem zeroFamily_supported (hs : ∀ i, Supported (Bs i)) (i : Fin t) :
    Supported (zeroFamily Bs hd hz i) :=
  (Bs 0).otherZero_supported (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hz (hs i.succ)

/-- Full admissibility descends to the puncture with exactly the retained designation. -/
theorem zeroFamily_admissible (d : Option V)
    (e : Option {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs d) (he : ∀ v, v ∈ e ↔ v.val ∈ d) :
    Admissible (zeroFamily Bs hd hz) e := by
  refine ⟨zeroFamily_disjoint Bs hd hz, zeroFamily_supported Bs hd hz h.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨hev, hpv, hout⟩ := h.2.2.1 v.val ((he v).mp hv)
    refine ⟨((Bs 0).zero_puncture_even_iff hz v).mpr hev, ?_, ?_⟩
    · rwa [(Bs 0).puncture_degree_of_even v hev]
    · intro i hi
      exact hout i.succ (((Bs 0).otherZero_mem_vertices (Bs i.succ)
        (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) hz v).mp hi)
  · intro v hv hout hne
    apply ((Bs 0).zero_puncture_eDegree_le hz v).trans
    apply h.2.2.2 v.val (((Bs 0).zero_puncture_even_iff hz v).mp hv)
    · intro i
      refine Fin.cases v.property (fun j => ?_) i
      intro hi
      exact hout j (((Bs 0).otherZero_mem_vertices (Bs j.succ)
        (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) hz v).mpr hi)
    · intro y hy hval
      have hvd : v.val ∈ d := hval ▸ hy
      exact hne v ((he v).mpr hvd) rfl

/-- Undesignated admissibility survives zero-syndrome deletion. -/
theorem zeroFamily_admissible_none (h : Admissible Bs none) :
    Admissible (zeroFamily Bs hd hz) none :=
  zeroFamily_admissible Bs hd hz none none h (by simp)

/-- A surviving designated even vertex retains its positive degree and designation. -/
theorem zeroFamily_admissible_some (y : {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs (some y.val)) :
    Admissible (zeroFamily Bs hd hz) (some y) := by
  apply zeroFamily_admissible Bs hd hz (some y.val) (some y) h
  intro v
  simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]

end Gallai.Composition
