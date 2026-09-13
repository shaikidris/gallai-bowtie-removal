/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Operations.FamilyReplace
import Lean.Elab.Tactic.Omega

/-! # Sum exact gains and losses at distinct carrier slots

Unlike a nonnegative-increment formula, this balance permits merging or
dropping old carriers. It applies to edge counts, endpoint counts and path
counts without identifying the old and new graph-dependent carrier types.
-/
namespace Gallai
variable {n k : ℕ}

/-- Local conservation at injectively selected slots implies global conservation.
No subtraction of natural numbers and no monotonicity assumption are needed. -/
theorem sum_local_balance (old new : Fin n → ℕ) (j : Fin k ↪ Fin n)
    (loss gain : Fin k → ℕ)
    (hlocal : ∀ l, new (j l) + loss l = old (j l) + gain l)
    (hother : ∀ i, (∀ l, j l ≠ i) → new i = old i) :
    (∑ i, new i) + (∑ l, loss l) = (∑ i, old i) + ∑ l, gain l := by
  classical
  have hp (i : Fin n) : new i + (∑ l, if j l = i then loss l else 0) =
      old i + ∑ l, if j l = i then gain l else 0 := by
    by_cases hi : ∃ l, j l = i
    · obtain ⟨l,rfl⟩ := hi
      simpa only [j.injective.eq_iff,Finset.sum_ite_eq',Finset.mem_univ,if_true] using hlocal l
    · have hn : ∀ l, j l ≠ i := fun l hl => hi ⟨l,hl⟩
      simp only [hn,if_false,Finset.sum_const_zero,Nat.add_zero,hother i hn]
  have hs (f : Fin k → ℕ) : (∑ i : Fin n, ∑ l, if j l = i then f l else 0) = ∑ l, f l := by
    rw [Finset.sum_comm]
    simp
  have hall := Finset.sum_congr (s₁ := Finset.univ) rfl (fun i _ => hp i)
  simpa only [Finset.sum_add_distrib,hs] using hall

/-- A merged group need only balance in aggregate; individual new carriers
may contain pieces of several old carriers. This lifts that group balance
to the entire family, provided all unselected scalar contributions agree. -/
theorem sum_grouped_balance (old new : Fin n → ℕ) (j : Fin k ↪ Fin n)
    (loss gain : ℕ)
    (hgroup : (∑ l, new (j l)) + loss = (∑ l, old (j l)) + gain)
    (hother : ∀ i, (∀ l, j l ≠ i) → new i = old i) :
    (∑ i, new i) + loss = (∑ i, old i) + gain := by
  have hswap := sum_local_balance old new j (fun l => old (j l))
    (fun l => new (j l)) (fun l => Nat.add_comm _ _) hother
  omega

end Gallai
