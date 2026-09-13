/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarRows
import Gallai.Transport.CompletedStarAssignment
import Mathlib.Data.Nat.Bitwise

/-! # The literal full-syndrome row universe

The first four even masks determine the last mask. This gives an exhaustive
finite parameter space independently of the catalogue's representative list.
-/

namespace Gallai.Certificate.CompletedStar

open scoped Finset

/-- Even masks, in the original verifier's stated order. -/
def evenMask : Fin 8 → Fin 16 := ![0, 3, 5, 9, 6, 10, 12, 15]

theorem evenMask_injective : Function.Injective evenMask := by decide

theorem evenMask_complete (m : Fin 16) :
    Even #(maskSupport m) ↔ ∃ i : Fin 8, evenMask i = m := by
  revert m
  decide

/-- Literal parity conditions of an actual full-syndrome state. -/
def FullState (s : State) : Prop :=
  (∀ i, Even #(maskSupport (s i))) ∧
    ∀ j : Fin 4, Odd #{i : Fin 5 | (s i).val.testBit j.val = true}

instance (s : State) : Decidable (FullState s) := by unfold FullState; infer_instance

/-- The full syndrome uniquely determines the fifth row from the first four. -/
def lastMask (a b c d : Fin 16) : Fin 16 := 15 ^^^ a ^^^ b ^^^ c ^^^ d

/-- Four free even rows, followed by the forced row. -/
def encodedState (q : Fin 4 → Fin 8) : State :=
  ![evenMask (q 0), evenMask (q 1), evenMask (q 2), evenMask (q 3),
    lastMask (evenMask (q 0)) (evenMask (q 1)) (evenMask (q 2)) (evenMask (q 3))]

private theorem mask_ext (a b : Fin 16)
    (h : ∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) : a = b := by
  have hx : ∀ a b : Fin 16,
      (∀ j : Fin 4, a.val.testBit j.val = b.val.testBit j.val) → a = b := by decide
  exact hx a b h

private theorem odd_five (a b c d e : Bool) :
    Odd #{i : Fin 5 | ![a, b, c, d, e] i = true} ↔
      e = (true ^^ a ^^ b ^^ c ^^ d) := by
  revert a b c d e
  decide

theorem fullState_last (s : State) (h : FullState s) :
    s 4 = lastMask (s 0) (s 1) (s 2) (s 3) := by
  apply mask_ext
  intro j
  have hb := (odd_five ((s 0).val.testBit j.val) ((s 1).val.testBit j.val)
    ((s 2).val.testBit j.val) ((s 3).val.testBit j.val)
    ((s 4).val.testBit j.val)).mp (h.2 j)
  have h15 : (15 : Fin 16).val.testBit j.val = true := by fin_cases j <;> decide
  simpa only [lastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor, h15] using hb

/-- No admissible row state is omitted by the four-free-row parametrization. -/
theorem fullState_encoded (s : State) (h : FullState s) :
    ∃ q : Fin 4 → Fin 8, encodedState q = s := by
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
  · change lastMask _ _ _ _ = s 4
    rw [hq 0, hq 1, hq 2, hq 3]
    exact (fullState_last s h).symm

/-- The four free rows give distinct labelled states. -/
theorem encodedState_injective : Function.Injective encodedState := by
  intro q r h
  funext i
  apply evenMask_injective
  have hi := congrFun h i.castSucc
  fin_cases i <;> exact hi

theorem free_row_count : Fintype.card (Fin 4 → Fin 8) = 4096 := by
  simp

private theorem even_xor (a b : Fin 16) :
    Even #(maskSupport a) → Even #(maskSupport b) → Even #(maskSupport (a ^^^ b)) := by
  revert a b
  decide

theorem evenMask_even (i : Fin 8) : Even #(maskSupport (evenMask i)) :=
  (evenMask_complete _).mpr ⟨i, rfl⟩

private theorem lastMask_even (a b c d : Fin 8) :
    Even #(maskSupport (lastMask (evenMask a) (evenMask b) (evenMask c) (evenMask d))) :=
  even_xor _ _ (even_xor _ _ (even_xor _ _ (even_xor _ _ (by decide)
    (evenMask_even a)) (evenMask_even b)) (evenMask_even c)) (evenMask_even d)

/-- Every choice of four even rows is admissible; the parametrization adds no states. -/
theorem encodedState_full (q : Fin 4 → Fin 8) : FullState (encodedState q) := by
  constructor
  · intro i
    fin_cases i
    · exact evenMask_even (q 0)
    · exact evenMask_even (q 1)
    · exact evenMask_even (q 2)
    · exact evenMask_even (q 3)
    · exact lastMask_even (q 0) (q 1) (q 2) (q 3)
  · intro j
    apply (odd_five ((evenMask (q 0)).val.testBit j.val)
      ((evenMask (q 1)).val.testBit j.val) ((evenMask (q 2)).val.testBit j.val)
      ((evenMask (q 3)).val.testBit j.val)
      ((lastMask (evenMask (q 0)) (evenMask (q 1))
        (evenMask (q 2)) (evenMask (q 3))).val.testBit j.val)).mpr
    have h15 : (15 : Fin 16).val.testBit j.val = true := by fin_cases j <;> decide
    simp only [lastMask, Fin.xor_val_of_two_pow (w := 4), Nat.testBit_xor, h15]

/-- The full admissible universe is exactly four freely chosen even row masks. -/
noncomputable def fullStateEquiv : (Fin 4 → Fin 8) ≃ {s : State // FullState s} :=
  Equiv.ofBijective (fun q => ⟨encodedState q, encodedState_full q⟩)
    ⟨fun _ _ h => encodedState_injective (congrArg Subtype.val h), by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq⟩ := fullState_encoded s hs
      exact ⟨q, Subtype.ext hq⟩⟩

theorem fullState_count : Fintype.card {s : State // FullState s} = 4096 := by
  rw [← Fintype.card_congr fullStateEquiv]
  exact free_row_count

end Gallai.Certificate.CompletedStar

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The actual graph and syndrome supply the literal finite coverage domain. -/
theorem completedStarState_full (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (hfull : B.syndrome = B.anchors) :
    FullState (B.completedStarState (B.carrierAnchorOrder D hfour)) :=
  ⟨B.completedStarState_even _, B.carrier_state_column_odd D hfour hfull⟩

end Gallai.WholeBowtie
