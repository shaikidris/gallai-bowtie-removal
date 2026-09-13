/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.OtherBowtiePairPuncture
import Gallai.Structure.ComponentAdmissibility

/-! # Admissible families after syndrome-pair repair

Both repair-edge statuses are allowed. The auxiliary need not be connected;
component restriction and its path budgets are separate consumers.
-/
namespace Gallai.Composition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj]
variable {t : ℕ} (Bs : Fin (t + 1) → WholeBowtie G)
variable (hd : ∀ i j, i ≠ j → Disjoint (Bs i).vertices (Bs j).vertices)
variable (p q : {v : V // v ∉ (Bs 0).vertices}) (hpq : p ≠ q)
variable (hs : (Bs 0).syndrome = {p.val, q.val})

/-- Exactly the successor-indexed bowties survive the repaired puncture. -/
noncomputable def pairFamily : Fin t → WholeBowtie ((Bs 0).pairRepairedPuncture p q) :=
  fun i => (Bs 0).otherPairBowtie (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) p q hpq hs

/-- Pair repair preserves disjointness of the remaining whole components. -/
theorem pairFamily_disjoint (i j : Fin t) (hij : i ≠ j) :
    Disjoint (pairFamily Bs hd p q hpq hs i).vertices
      (pairFamily Bs hd p q hpq hs j).vertices := by
  apply Finset.disjoint_left.mpr
  intro v hv hw
  exact Finset.disjoint_left.mp (hd i.succ j.succ (by simpa using hij))
    (((Bs 0).otherPair_mem_vertices (Bs i.succ)
      (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) p q hpq hs v).mp hv)
    (((Bs 0).otherPair_mem_vertices (Bs j.succ)
      (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) p q hpq hs v).mp hw)

/-- Each surviving bowtie stays in its manuscript-supported class. -/
theorem pairFamily_supported (h : ∀ i, Supported (Bs i)) (i : Fin t) :
    Supported (pairFamily Bs hd p q hpq hs i) :=
  (Bs 0).otherPair_supported (Bs i.succ)
    (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) p q hpq hs (h i.succ)

include hs in
/-- An original even vertex loses no edge in deletion or the odd-odd repair. -/
theorem pair_degree_of_even (v : {v : V // v ∉ (Bs 0).vertices})
    (hv : Even (G.degree v.val)) :
    ((Bs 0).pairRepairedPuncture p q).degree v = G.degree v.val := by
  have hoddp := (Bs 0).odd_degree_anchor ((Bs 0).syndrome_subset_anchors
    (show p.val ∈ (Bs 0).syndrome by simp [hs]))
  have hoddq := (Bs 0).odd_degree_anchor ((Bs 0).syndrome_subset_anchors
    (show q.val ∈ (Bs 0).syndrome by simp [hs]))
  have hnep : v ≠ p := by
    intro he
    subst v
    exact Nat.not_even_iff_odd.mpr hoddp hv
  have hneq : v ≠ q := by
    intro he
    subst v
    exact Nat.not_even_iff_odd.mpr hoddq hv
  exact (toggleEdge_degree_of_ne (Bs 0).puncture p q v hnep hneq).trans
    ((Bs 0).puncture_degree_of_even v hv)

/-- Full family admissibility descends with precisely the retained designation. -/
theorem pairFamily_admissible (d : Option V)
    (e : Option {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs d) (he : ∀ v, v ∈ e ↔ v.val ∈ d) :
    Admissible (pairFamily Bs hd p q hpq hs) e := by
  refine ⟨pairFamily_disjoint Bs hd p q hpq hs,
    pairFamily_supported Bs hd p q hpq hs h.2.1, ?_, ?_⟩
  · intro v hv
    obtain ⟨hev, hpv, hout⟩ := h.2.2.1 v.val ((he v).mp hv)
    refine ⟨((Bs 0).pairRepairedPuncture_even_iff p q hpq hs v).mpr hev, ?_, ?_⟩
    · rwa [pair_degree_of_even Bs p q hs v hev]
    · intro i hi
      exact hout i.succ (((Bs 0).otherPair_mem_vertices (Bs i.succ)
        (hd 0 i.succ (Ne.symm (Fin.succ_ne_zero i))) p q hpq hs v).mp hi)
  · intro v hv hout hne
    apply ((Bs 0).pairRepairedPuncture_eDegree_le p q hpq hs v).trans
    apply h.2.2.2 v.val (((Bs 0).pairRepairedPuncture_even_iff p q hpq hs v).mp hv)
    · intro i
      refine Fin.cases v.property (fun j => ?_) i
      intro hi
      exact hout j (((Bs 0).otherPair_mem_vertices (Bs j.succ)
        (hd 0 j.succ (Ne.symm (Fin.succ_ne_zero j))) p q hpq hs v).mpr hi)
    · intro y hy hval
      have hvd : v.val ∈ d := hval ▸ hy
      exact hne v ((he v).mpr hvd) rfl

/-- Undesignated families descend to either repaired puncture. -/
theorem pairFamily_admissible_none (h : Admissible Bs none) :
    Admissible (pairFamily Bs hd p q hpq hs) none :=
  pairFamily_admissible Bs hd p q hpq hs none none h (by simp)

/-- A retained designated even vertex remains positive and designated. -/
theorem pairFamily_admissible_some (y : {v : V // v ∉ (Bs 0).vertices})
    (h : Admissible Bs (some y.val)) :
    Admissible (pairFamily Bs hd p q hpq hs) (some y) := by
  apply pairFamily_admissible Bs hd p q hpq hs (some y.val) (some y) h
  intro v
  simp only [Option.mem_def, Option.some.injEq, Subtype.ext_iff]

end Gallai.Composition
