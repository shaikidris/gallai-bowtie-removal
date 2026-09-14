/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.ThreeAnchorZeroOrbits.Core
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block00
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block01
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block02
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block03
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block04
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block05
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block06
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block07
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block08
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block09
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block10
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block11
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block12
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block13
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block14
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block15
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block16
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block17
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block18
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block19
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block20
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block21
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block22
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block23
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block24
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block25
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block26
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block27
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block28
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block29
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block30
import Gallai.Certificates.ThreeAnchorZeroOrbits.Block31
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.ThreeAnchor.ZeroOrbits
open Orbits RetainedOrbits
open scoped Finset
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

private theorem highZero_cards (b : Fin 32) :
    (highZeroBlock b).card =
      (![0, 0, 3, 6, 3, 6, 3, 6, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8] : Fin 32 → ℕ) b := by
  fin_cases b
  · exact highZero_card_0
  · exact highZero_card_1
  · exact highZero_card_2
  · exact highZero_card_3
  · exact highZero_card_4
  · exact highZero_card_5
  · exact highZero_card_6
  · exact highZero_card_7
  · exact highZero_card_8
  · exact highZero_card_9
  · exact highZero_card_10
  · exact highZero_card_11
  · exact highZero_card_12
  · exact highZero_card_13
  · exact highZero_card_14
  · exact highZero_card_15
  · exact highZero_card_16
  · exact highZero_card_17
  · exact highZero_card_18
  · exact highZero_card_19
  · exact highZero_card_20
  · exact highZero_card_21
  · exact highZero_card_22
  · exact highZero_card_23
  · exact highZero_card_24
  · exact highZero_card_25
  · exact highZero_card_26
  · exact highZero_card_27
  · exact highZero_card_28
  · exact highZero_card_29
  · exact highZero_card_30
  · exact highZero_card_31

private theorem pack32_inj (b : Fin 32) :
    Function.Injective fun r : Fin 32 =>
      (⟨b.val * 32 + r.val, by omega⟩ : Fin 1024) := by
  intro r s h
  apply Fin.ext
  have := congrArg Fin.val h
  simp at this
  omega

private theorem reconstruct (b : Fin 32) (n : Fin 1024)
    (hb : n.val / 32 = b.val) :
    (⟨b.val * 32 + n.val % 32, by omega⟩ : Fin 1024) = n := by
  apply Fin.ext
  change b.val * 32 + n.val % 32 = n.val
  rw [← hb, mul_comm]
  exact Nat.div_add_mod n.val 32

private theorem highZero_fiber (b : Fin 32) :
    (Finset.univ.filter fun n : Fin 1024 =>
      (⟨n.val / 32, by omega⟩ : Fin 32) = b ∧ HighZero n).card =
      (highZeroBlock b).card := by
  refine (Finset.card_nbij'
      (fun r : Fin 32 => (⟨b.val * 32 + r.val, by omega⟩ : Fin 1024))
      (fun n : Fin 1024 => (⟨n.val % 32, Nat.mod_lt _ (by decide)⟩ : Fin 32))
      ?_ ?_ ?_ ?_).symm
  · intro r hr
    have hb := (Finset.mem_filter.mp hr).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ⟨?eq, hb⟩⟩
    apply Fin.ext
    change (b.val * 32 + r.val) / 32 = b.val
    omega
  · intro n hn
    have h := (Finset.mem_filter.mp hn).2
    have hbval : n.val / 32 = b.val := congrArg Fin.val h.1
    have hnp := reconstruct b n hbval
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _, ?_⟩
    simpa [hnp] using h.2
  · intro r _hr
    apply Fin.ext
    change (b.val * 32 + r.val) % 32 = r.val
    omega
  · intro n hn
    exact reconstruct b n (congrArg Fin.val (Finset.mem_filter.mp hn).2.1)

theorem highZero_card : (Finset.univ.filter HighZero).card = 189 := by
  have hi (b : Fin 32) :
      #{n ∈ Finset.univ.filter HighZero |
          (⟨n.val / 32, by omega⟩ : Fin 32) = b} =
        (![0, 0, 3, 6, 3, 6, 3, 6, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8] : Fin 32 → ℕ) b := by
    have : (Finset.univ.filter HighZero).filter
        (fun n => (⟨n.val / 32, by omega⟩ : Fin 32) = b) =
        Finset.univ.filter (fun n : Fin 1024 =>
          (⟨n.val / 32, by omega⟩ : Fin 32) = b ∧ HighZero n) := by
      simp [Finset.filter_filter, and_comm]
    rw [this, highZero_fiber, highZero_cards]
  rw [Finset.card_eq_sum_card_fiberwise
      (f := fun n : Fin 1024 => (⟨n.val / 32, by omega⟩ : Fin 32))
      (t := (Finset.univ : Finset (Fin 32))) (fun _ _ => Finset.mem_univ _)]
  trans ∑ b : Fin 32, (![0, 0, 3, 6, 3, 6, 3, 6, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8, 3, 6, 7, 8, 7, 8, 7, 8] : Fin 32 → ℕ) b
  · exact Finset.sum_congr rfl fun b _ => hi b
  · decide

private theorem zero_checked (q rem : Fin 32) :
    HighZero (⟨q.val * 32 + rem.val, by omega⟩ : Fin 1024) →
      NormalizesZero (decode (⟨q.val * 32 + rem.val, by omega⟩))
        (normalizationWitness (⟨q.val * 32 + rem.val, by omega⟩)).1
        (normalizationWitness (⟨q.val * 32 + rem.val, by omega⟩)).2.1
        (normalizationWitness (⟨q.val * 32 + rem.val, by omega⟩)).2.2 := by
  fin_cases q
  · exact zero_check_0 rem
  · exact zero_check_1 rem
  · exact zero_check_2 rem
  · exact zero_check_3 rem
  · exact zero_check_4 rem
  · exact zero_check_5 rem
  · exact zero_check_6 rem
  · exact zero_check_7 rem
  · exact zero_check_8 rem
  · exact zero_check_9 rem
  · exact zero_check_10 rem
  · exact zero_check_11 rem
  · exact zero_check_12 rem
  · exact zero_check_13 rem
  · exact zero_check_14 rem
  · exact zero_check_15 rem
  · exact zero_check_16 rem
  · exact zero_check_17 rem
  · exact zero_check_18 rem
  · exact zero_check_19 rem
  · exact zero_check_20 rem
  · exact zero_check_21 rem
  · exact zero_check_22 rem
  · exact zero_check_23 rem
  · exact zero_check_24 rem
  · exact zero_check_25 rem
  · exact zero_check_26 rem
  · exact zero_check_27 rem
  · exact zero_check_28 rem
  · exact zero_check_29 rem
  · exact zero_check_30 rem
  · exact zero_check_31 rem

theorem normalizationWitness_checked : ∀ n : Fin 1024, HighZero n →
    NormalizesZero (decode n) (normalizationWitness n).1
      (normalizationWitness n).2.1 (normalizationWitness n).2.2 := by
  intro n
  let q : Fin 32 := ⟨n.val / 32, by omega⟩
  let r : Fin 32 := ⟨n.val % 32, by omega⟩
  have h := zero_checked q r
  have heq : (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [q, r]
    omega
  simpa only [heq] using h

theorem zero_coverage (n : Fin 1024) (hn : HighZero n) :
    ∃ r : Fin 10, ∃ c : Fin 8, ∃ a : Fin 6, NormalizesZero (decode n) r c a :=
  ⟨_,_,_,normalizationWitness_checked n hn⟩

theorem state_coverage (s : State)
    (ha : 3 ≤ (Finset.univ.filter fun j : Fin 5 => j ≠ 0 ∧ s j ≠ 0).card)
    (hz : syndrome s = ∅) :
    ∃ r : Fin 10, ∃ c : Fin 8, ∃ a : Fin 6, NormalizesZero s r c a := by
  have hn : HighZero (encode s) := by simpa only [HighZero,decode_encode] using And.intro ha hz
  simpa only [decode_encode] using zero_coverage (encode s) hn

end Gallai.Certificate.ThreeAnchor.ZeroOrbits
