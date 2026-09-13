/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarUniverse
import Gallai.Structure.LowActivity
import Gallai.Structure.Incidence

/-! # Independent zero-syndrome incidence universe

Four freely chosen even rows determine the fifth by XOR. Genuine four-anchor
coverage and high private activity are predicates on those original rows,
not properties inferred from the catalogue representative list.
-/

namespace Gallai.Certificate.ZeroSyndrome

open CompletedStar
open scoped Finset

/-- Every row and every column has even incidence. -/
def ZeroState (s : State) : Prop :=
  (∀ i, Even #(maskSupport (s i))) ∧
    ∀ j : Fin 4, Even #{i : Fin 5 | (s i).val.testBit j.val = true}

instance (s : State) : Decidable (ZeroState s) := by unfold ZeroState; infer_instance

/-- Every anchor occurs, and at least three private rows are active. -/
def HighBoundary (s : State) : Prop :=
  (∀ j : Fin 4, ∃ i : Fin 5, (s i).val.testBit j.val = true) ∧
    3 ≤ #{i : Fin 5 | i ≠ 0 ∧ s i ≠ 0}

instance (s : State) : Decidable (HighBoundary s) := by unfold HighBoundary; infer_instance

/-- The exact original-state domain of the zero-syndrome certificate branch. -/
def HighZeroState (s : State) : Prop := ZeroState s ∧ HighBoundary s

instance (s : State) : Decidable (HighZeroState s) := by unfold HighZeroState; infer_instance

/-- Even column parity forces this fifth mask. -/
def zeroLastMask (a b c d : Fin 16) : Fin 16 := a ^^^ b ^^^ c ^^^ d

/-- Four free even row masks with the fifth forced by zero syndrome. -/
def zeroEncodedState (q : Fin 4 → Fin 8) : State :=
  ![evenMask (q 0), evenMask (q 1), evenMask (q 2), evenMask (q 3),
    zeroLastMask (evenMask (q 0)) (evenMask (q 1)) (evenMask (q 2)) (evenMask (q 3))]

private theorem mask_ext (a b : Fin 16)
    (h : ∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) : a = b := by
  have hh : ∀ a b : Fin 16,
      (∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) → a = b := by decide
  exact hh a b h

private theorem even_five (a b c d e : Bool) :
    Even #{i : Fin 5 | ![a, b, c, d, e] i = true} ↔ e = (a ^^ b ^^ c ^^ d) := by
  revert a b c d e
  decide

/-- The graph's column parities determine the remaining row uniquely. -/
theorem zeroState_last (s : State) (h : ZeroState s) :
    s 4 = zeroLastMask (s 0) (s 1) (s 2) (s 3) := by
  apply mask_ext
  intro j
  have hb := (even_five ((s 0).val.testBit j.val) ((s 1).val.testBit j.val)
    ((s 2).val.testBit j.val) ((s 3).val.testBit j.val)
    ((s 4).val.testBit j.val)).mp (h.2 j)
  simpa only [zeroLastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor] using hb

/-- Every zero-syndrome state is parametrized; none can be omitted by a list. -/
theorem zeroState_encoded (s : State) (h : ZeroState s) :
    ∃ q : Fin 4 → Fin 8, zeroEncodedState q = s := by
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
  · change zeroLastMask _ _ _ _ = s 4
    rw [hq 0, hq 1, hq 2, hq 3]
    exact (zeroState_last s h).symm

private theorem even_xor (a b : Fin 16) :
    Even #(maskSupport a) → Even #(maskSupport b) → Even #(maskSupport (a ^^^ b)) := by
  revert a b
  decide

/-- The parametrization introduces no nonzero-syndrome or odd-row states. -/
theorem zeroEncodedState_zero (q : Fin 4 → Fin 8) : ZeroState (zeroEncodedState q) := by
  constructor
  · intro i
    fin_cases i
    · exact evenMask_even (q 0)
    · exact evenMask_even (q 1)
    · exact evenMask_even (q 2)
    · exact evenMask_even (q 3)
    · exact even_xor _ _ (even_xor _ _ (even_xor _ _
        (evenMask_even (q 0)) (evenMask_even (q 1))) (evenMask_even (q 2)))
        (evenMask_even (q 3))
  · intro j
    apply (even_five ((evenMask (q 0)).val.testBit j.val)
      ((evenMask (q 1)).val.testBit j.val) ((evenMask (q 2)).val.testBit j.val)
      ((evenMask (q 3)).val.testBit j.val)
      ((zeroLastMask (evenMask (q 0)) (evenMask (q 1))
        (evenMask (q 2)) (evenMask (q 3))).val.testBit j.val)).mpr
    simp only [zeroLastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor]

/-- The free rows can be recovered from the encoded state. -/
theorem zeroEncodedState_injective : Function.Injective zeroEncodedState := by
  intro q r h
  funext i
  apply evenMask_injective
  have hi := congrFun h i.castSucc
  fin_cases i <;> exact hi

/-- Independently filtered domain for exhaustive high-activity coverage. -/
def highInputs : Finset (Fin 4 → Fin 8) :=
  Finset.univ.filter (fun q => HighBoundary (zeroEncodedState q))

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- The complete original high-activity four-anchor domain has3047 states. -/
theorem highInputs_card : highInputs.card = 3047 := by decide

/-- Four-bit row encoding is zero precisely for an empty external row. -/
theorem maskSupport_empty_iff (m : Fin 16) : maskSupport m = ∅ ↔ m = 0 := by
  revert m
  decide

/-- Every actual high-activity zero state occurs in the filtered domain. -/
theorem highZeroState_encoded (s : State) (h : HighZeroState s) :
    ∃ q ∈ highInputs, zeroEncodedState q = s := by
  obtain ⟨q, hq⟩ := zeroState_encoded s h.1
  exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hq ▸ h.2⟩, hq⟩

end Gallai.Certificate.ZeroSyndrome
