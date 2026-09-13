/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarUniverse
import Gallai.Structure.Incidence

/-! # Independent normalized size-two incidence universe

The syndrome is the first two anchors. Four free even rows determine the
fifth. Coverage is derived from column parity, not a catalogue representative
list. These statements do not assert acceptance of reconstruction records.
-/
namespace Gallai.Certificate.SizeTwo
open CompletedStar
open scoped Finset

/-- Even rows with precisely the first two columns of odd incidence. -/
def PairState (s : State) : Prop :=
  (∀ i, Even #(maskSupport (s i))) ∧
    ∀ j : Fin 4, (Odd #{i : Fin 5 | (s i).val.testBit j.val = true} ↔ j.val < 2)

instance (s : State) : Decidable (PairState s) := by unfold PairState; infer_instance

/-- The syndrome mask is 3, independently of anchor adjacency. -/
def pairLastMask (a b c d : Fin 16) : Fin 16 := 3 ^^^ a ^^^ b ^^^ c ^^^ d

/-- Four free even rows and the uniquely forced last row. -/
def pairEncodedState (q : Fin 4 → Fin 8) : State :=
  ![evenMask (q 0), evenMask (q 1), evenMask (q 2), evenMask (q 3),
    pairLastMask (evenMask (q 0)) (evenMask (q 1)) (evenMask (q 2)) (evenMask (q 3))]

private theorem mask_ext (a b : Fin 16)
    (h : ∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) : a = b := by
  have hh : ∀ a b : Fin 16,
      (∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) → a = b := by decide
  exact hh a b h

private theorem parity_five (t a b c d e : Bool) :
    (Odd #{i : Fin 5 | ![a,b,c,d,e] i = true} ↔ t = true) ↔
      e = (t ^^ a ^^ b ^^ c ^^ d) := by
  revert t a b c d e
  decide

private theorem mask_three (j : Fin 4) :
    (3 : Fin 16).val.testBit j.val = true ↔ j.val < 2 := by
  fin_cases j <;> decide

/-- Column parity determines the fifth row uniquely. -/
theorem pairState_last (s : State) (h : PairState s) :
    s 4 = pairLastMask (s 0) (s 1) (s 2) (s 3) := by
  apply mask_ext
  intro j
  have hb := (parity_five ((3 : Fin 16).val.testBit j.val)
    ((s 0).val.testBit j.val) ((s 1).val.testBit j.val)
    ((s 2).val.testBit j.val) ((s 3).val.testBit j.val)
    ((s 4).val.testBit j.val)).mp ((h.2 j).trans (mask_three j).symm)
  simpa only [pairLastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor] using hb

/-- Every normalized admissible state occurs in the independent parametrization. -/
theorem pairState_encoded (s : State) (h : PairState s) :
    ∃ q : Fin 4 → Fin 8, pairEncodedState q = s := by
  have he : ∀ i : Fin 4, ∃ j : Fin 8, evenMask j = s i.castSucc :=
    fun i => (evenMask_complete _).mp (h.1 i.castSucc)
  choose q hq using he
  refine ⟨q, ?_⟩
  funext i
  fin_cases i
  · exact hq 0
  · exact hq 1
  · exact hq 2
  · exact hq 3
  · change pairLastMask _ _ _ _ = s 4
    rw [hq 0,hq 1,hq 2,hq 3]
    exact (pairState_last s h).symm

private theorem even_xor (a b : Fin 16) :
    Even #(maskSupport a) → Even #(maskSupport b) → Even #(maskSupport (a ^^^ b)) := by
  revert a b
  decide

/-- Every encoded state has the required row and column parity. -/
theorem pairEncodedState_pair (q : Fin 4 → Fin 8) : PairState (pairEncodedState q) := by
  constructor
  · intro i
    fin_cases i
    · exact evenMask_even (q 0)
    · exact evenMask_even (q 1)
    · exact evenMask_even (q 2)
    · exact evenMask_even (q 3)
    · exact even_xor _ _ (even_xor _ _ (even_xor _ _ (even_xor _ _ (by decide)
        (evenMask_even (q 0))) (evenMask_even (q 1))) (evenMask_even (q 2)))
        (evenMask_even (q 3))
  · intro j
    apply Iff.trans _ (mask_three j)
    apply (parity_five ((3 : Fin 16).val.testBit j.val)
      ((evenMask (q 0)).val.testBit j.val) ((evenMask (q 1)).val.testBit j.val)
      ((evenMask (q 2)).val.testBit j.val) ((evenMask (q 3)).val.testBit j.val)
      ((pairLastMask (evenMask (q 0)) (evenMask (q 1))
        (evenMask (q 2)) (evenMask (q 3))).val.testBit j.val)).mpr
    simp only [pairLastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor]

/-- Free row choices represent distinct labelled states. -/
theorem pairEncodedState_injective : Function.Injective pairEncodedState := by
  intro q r h
  funext i
  apply evenMask_injective
  have hi := congrFun h i.castSucc
  fin_cases i <;> exact hi

/-- Exact admissible-state equivalence, before imposing activity predicates. -/
noncomputable def pairStateEquiv : (Fin 4 → Fin 8) ≃ {s : State // PairState s} :=
  Equiv.ofBijective (fun q => ⟨pairEncodedState q,pairEncodedState_pair q⟩)
    ⟨fun _ _ h => pairEncodedState_injective (congrArg Subtype.val h), by
      rintro ⟨s,hs⟩
      obtain ⟨q,hq⟩ := pairState_encoded s hs
      exact ⟨q,Subtype.ext hq⟩⟩

/-- The normalized labelled universe has exactly 4096 states. -/
theorem pairState_count : Fintype.card {s : State // PairState s} = 4096 := by
  rw [← Fintype.card_congr pairStateEquiv]
  exact free_row_count

end Gallai.Certificate.SizeTwo

namespace Gallai.WholeBowtie
open Certificate.CompletedStar Certificate.SizeTwo
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Actual graph incidences enter the normalized domain without a catalogue premise. -/
theorem completedStarState_pair (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) :
    PairState (B.completedStarState A) := by
  refine ⟨B.completedStarState_even A, ?_⟩
  intro j
  have hcount : #{i : Fin 5 | ((B.completedStarState A) i).val.testBit j.val = true} =
      B.columnCount (A j).val := by
    congr 1
    ext i
    simp only [Finset.mem_filter,Finset.mem_univ,true_and, B.completedStarState_bit,
      B.mem_row, B.numberedAnchor_not_mem A j, not_false_eq_true, and_true]
  rw [hcount, ← B.mem_syndrome_iff_odd_column, hSigma]
  have heq (k : Fin 4) : (A j).val = (A k).val ↔ j = k :=
    ⟨fun h => A.injective (Subtype.ext h), fun h => congrArg (fun l => (A l).val) h⟩
  simp only [Finset.mem_insert,Finset.mem_singleton,heq]
  fin_cases j <;> decide

/-- The exact state consumed by reconstruction has an exhaustive finite index. -/
theorem completedStarState_pair_encoded (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val}) :
    ∃ q : Fin 4 → Fin 8, pairEncodedState q = B.completedStarState A :=
  pairState_encoded _ (B.completedStarState_pair A hSigma)

end Gallai.WholeBowtie
