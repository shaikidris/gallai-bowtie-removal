/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoRichFamilyCounts

/-! # Endpoint conservation on the actual rich through family

The two merged paths retain all non-reserve endpoints of their three old
carriers. The third reserve path's tail must not end at the observed vertex.
Untouched paths preserve their endpoints by the same original-graph mapping.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The same indexed family used for edge conservation preserves each endpoint
count away from the reserve and the optional tail's new endpoint. -/
theorem sizeTwo_rich_through_family_endpoints (D : Decomposition B.syndromeStar)
    (j : Fin 4 ↪ Fin D.size) (w : B.StarSurvivor)
    (hw : ∀ l : Fin 3, (D.path (j l.succ)).finish = w)
    (N₀ N₁ N₂ : NonemptyPath G) (F : Fin D.size → Option (NonemptyPath G))
    (hselected : ∀ l, F (j l) = ![some N₀,none,some N₁,some N₂] l)
    (hother : ∀ k, (∀ l, j l ≠ k) →
      ∃ hk : B.completedHub ∉ (D.path k).walk.support,
        F k = some (B.syndromeAvoidingPath (D.path k) hk))
    (hs₀ : N₀.start = (D.path (j 0)).start.val)
    (ht₀ : N₀.finish = (D.path (j 1)).start.val)
    (hs₁ : N₁.start = (D.path (j 0)).finish.val)
    (ht₁ : N₁.finish = (D.path (j 2)).start.val)
    (hs₂ : N₂.start = (D.path (j 3)).start.val)
    (v : V) (hvw : w.val ≠ v) (hv₂ : N₂.finish ≠ v) :
    (∑ k, ((F k).map (fun P => (if P.start = v then 1 else 0) +
      (if P.finish = v then 1 else 0 : ℕ))).getD 0) =
      ∑ k, ((if (D.path k).start.val = v then 1 else 0) +
        (if (D.path k).finish.val = v then 1 else 0 : ℕ)) := by
  classical
  let old : Fin D.size → ℕ := fun k => (if (D.path k).start.val = v then 1 else 0) +
    (if (D.path k).finish.val = v then 1 else 0)
  let new : Fin D.size → ℕ := fun k => ((F k).map (fun P =>
    (if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0 : ℕ))).getD 0
  have hgroup : (∑ l, new (j l)) + 0 = (∑ l, old (j l)) + 0 := by
    have four (f : Fin 4 → ℕ) : (∑ l, f l) = f 0 + f 1 + f 2 + f 3 := by
      simp only [Fin.sum_univ_succ,Fin.sum_univ_zero]
      change f 0 + (f 1 + (f 2 + (f 3 + 0))) = _
      omega
    have hr₁ : (D.path (j 1)).finish.val ≠ v := fun he =>
      hvw ((congrArg Subtype.val (hw 0)).symm.trans he)
    have hr₂ : (D.path (j 2)).finish.val ≠ v := fun he =>
      hvw ((congrArg Subtype.val (hw 1)).symm.trans he)
    have hr₃ : (D.path (j 3)).finish.val ≠ v := fun he =>
      hvw ((congrArg Subtype.val (hw 2)).symm.trans he)
    rw [four,four]
    simp [new,old,hselected,hs₀,ht₀,hs₁,ht₁,hs₂,hv₂,hr₁,hr₂,hr₃,Nat.add_assoc]
    omega
  have ho : ∀ k, (∀ l, j l ≠ k) → new k = old k := by
    intro k hk
    obtain ⟨hfree,hF⟩ := hother k hk
    simp only [new,hF,Option.map_some,Option.getD_some]
    rfl
  simpa only [Nat.add_zero] using sum_grouped_balance old new j 0 0 hgroup ho

end Gallai.WholeBowtie
