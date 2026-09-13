/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Expansion.Coverage
import Gallai.Certificates.EndpointProfiles
import Mathlib.Data.Fintype.BigOperators

/-!
# Endpoint preservation in the actual star expansion

Each restored old carrier preserves its endpoint contribution away from the
hub and has no hub endpoint. The two added paths supply the checked output
profile. Summing at the actual family indices preserves these facts under
the finite reindexing used by the constructed decomposition.
-/

namespace Gallai.Star

universe u

variable {V : Type u} {H : SimpleGraph V} [DecidableEq V]
variable [Fintype V] [DecidableRel H.Adj]

/-- The actual terminal replacement finishes at a private, not old, vertex. -/
theorem assignedTerminal_finish_ne_old (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : D.TerminalIndex x) (w : V) :
    (assignedTerminal D x hd i).finish ≠ Sum.inl w := by
  let p := profileOf D x
  let n := terminalNumber D x hd i
  obtain ⟨v, hv, hl⟩ := p.terminalWord_last_private n
  have hm := p.terminalWord_mem n
  have hc := p.valid.2.2.1 _ hm
  have hf := realizeWord_finish H x (D.fourNeighborEquiv x hd) (p.terminalWord n)
    hc.1 hc.2 (p.valid.word_edges _ hm) v hl
  change (assignedTerminal D x hd i).finish = label H x (D.fourNeighborEquiv x hd) v at hf
  rw [hf]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> simp [label]

/-- Each restored old carrier preserves its contribution at every other old vertex. -/
theorem restoredOldCarrier_endpoint_contribution (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) (w : V) (hw : w ≠ x) :
    ((if (restoredOldCarrier D x hd i).start = Sum.inl w then 1 else 0) +
      (if (restoredOldCarrier D x hd i).finish = Sum.inl w then 1 else 0 : ℕ)) =
      ((if (D.path i).start = w then 1 else 0) +
        (if (D.path i).finish = w then 1 else 0)) := by
  by_cases ht : i ∈ D.terminalCarriers x
  · rw [restoredOldCarrier_of_terminal D x hd i ht, assignedTerminal_start]
    have hf := assignedTerminal_finish_ne_old D x hd ⟨i, ht⟩ w
    have htf := (D.path i).toward_finish x (Finset.mem_filter.mp ht).2
    have he := (D.path i).toward_endpoint_contribution x w
    simpa only [Sum.inl.injEq, if_neg hf, htf, if_neg hw.symm, add_zero] using he
  by_cases hp : i ∈ D.throughCarriers x
  · rw [restoredOldCarrier_of_through D x hd i ht hp]
    rw [(assignedThrough_endpoints D x hd ⟨i, hp⟩).1,
      (assignedThrough_endpoints D x hd ⟨i, hp⟩).2]
    simp only [Sum.inl.injEq]
  · rw [restoredOldCarrier_of_unaffected D x hd i ht hp]
    change ((if Sum.inl (D.path i).start = (Sum.inl w : V ⊕ Fin 4) then 1 else 0) +
      (if Sum.inl (D.path i).finish = (Sum.inl w : V ⊕ Fin 4) then 1 else 0 : ℕ)) = _
    simp only [Sum.inl.injEq]

/-- None of the restored old carriers ends at the released hub. -/
theorem restoredOldCarrier_hub_endpoints (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) :
    (restoredOldCarrier D x hd i).start ≠ Sum.inl x ∧
      (restoredOldCarrier D x hd i).finish ≠ Sum.inl x := by
  by_cases ht : i ∈ D.terminalCarriers x
  · rw [restoredOldCarrier_of_terminal D x hd i ht]
    refine ⟨?_, assignedTerminal_finish_ne_old D x hd ⟨i, ht⟩ x⟩
    rw [assignedTerminal_start]
    have hf := (D.path i).toward_finish x (Finset.mem_filter.mp ht).2
    intro he
    exact ((D.path i).toward x).start_ne_finish H ((Sum.inl.inj he).trans hf.symm)
  by_cases hp : i ∈ D.throughCarriers x
  · rw [restoredOldCarrier_of_through D x hd i ht hp]
    have hi := (Finset.mem_filter.mp hp).2
    simpa only [(assignedThrough_endpoints D x hd ⟨i, hp⟩).1,
      (assignedThrough_endpoints D x hd ⟨i, hp⟩).2, ne_eq, Sum.inl.injEq] using hi.2
  · rw [restoredOldCarrier_of_unaffected D x hd i ht hp]
    have hi : (D.path i).start ≠ x ∧ (D.path i).finish ≠ x := by
      simpa only [Decomposition.terminalCarriers, Finset.mem_filter, Finset.mem_univ,
        true_and, not_or] using ht
    exact ⟨fun h => hi.1 (Sum.inl.inj h), fun h => hi.2 (Sum.inl.inj h)⟩

/-- Added carriers have exactly the endpoint symbols of their checked words. -/
theorem addedCarrier_endpoints (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin 2) :
    (addedCarrier D x hd i).start =
        label H x (D.fourNeighborEquiv x hd) ((profileOf D x).addedEnds i).1 ∧
      (addedCarrier D x hd i).finish =
        label H x (D.fourNeighborEquiv x hd) ((profileOf D x).addedEnds i).2 := by
  let p := profileOf D x
  let word := p.added[i.val]'(by rw [p.valid.2.1]; exact i.isLt)
  have hm : word ∈ p.replacements ++ p.added :=
    List.mem_append_right _ (List.getElem_mem _)
  have hc := p.valid.2.2.1 _ hm
  exact ⟨realizeWord_start H x (D.fourNeighborEquiv x hd) word hc.1 hc.2
    (p.valid.word_edges _ hm) _ (p.addedEnds_correct i).1,
    realizeWord_finish H x (D.fourNeighborEquiv x hd) word hc.1 hc.2
      (p.valid.word_edges _ hm) _ (p.addedEnds_correct i).2⟩

/-- Added paths supply no endpoint at an old vertex other than the hub. -/
theorem addedCarrier_old_contribution (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin 2) (w : V) (hw : w ≠ x) :
    ((if (addedCarrier D x hd i).start = Sum.inl w then 1 else 0) +
      (if (addedCarrier D x hd i).finish = Sum.inl w then 1 else 0 : ℕ)) = 0 := by
  rw [(addedCarrier_endpoints D x hd i).1, (addedCarrier_endpoints D x hd i).2]
  cases profileOf D x <;> fin_cases i <;> simp [Profile.addedEnds, label, hw.symm]

/-- Each added path ends at the hub exactly in the two-terminal input profile. -/
theorem addedCarrier_hub_contribution (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin 2) :
    ((if (addedCarrier D x hd i).start = Sum.inl x then 1 else 0) +
      (if (addedCarrier D x hd i).finish = Sum.inl x then 1 else 0 : ℕ)) =
      if profileOf D x = .two then 1 else 0 := by
  rw [(addedCarrier_endpoints D x hd i).1, (addedCarrier_endpoints D x hd i).2]
  cases profileOf D x <;> fin_cases i <;> simp [Profile.addedEnds, label]

/-- Each old carrier has zero endpoint contribution at the released hub. -/
theorem restoredOldCarrier_hub_contribution (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (i : Fin D.size) :
    ((if (restoredOldCarrier D x hd i).start = Sum.inl x then 1 else 0) +
      (if (restoredOldCarrier D x hd i).finish = Sum.inl x then 1 else 0 : ℕ)) = 0 := by
  simp only [if_neg (restoredOldCarrier_hub_endpoints D x hd i).1,
    if_neg (restoredOldCarrier_hub_endpoints D x hd i).2, add_zero]

/-- The actual expanded decomposition preserves every other old endpoint count. -/
theorem expandDecomposition_endpointCount_old (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) (w : V) (hw : w ≠ x) :
    (expandDecomposition D x hd).endpointCount (Sum.inl w) = D.endpointCount w := by
  rw [expandDecomposition, Decomposition.ofFamily_endpointCount, Fintype.sum_sum_type]
  dsimp only [expansionFamily]
  calc
    _ = D.endpointCount w + 0 := congrArg₂ Nat.add
      (Finset.sum_congr rfl (fun i _ =>
        restoredOldCarrier_endpoint_contribution D x hd i w hw))
      (Finset.sum_eq_zero (fun i _ => addedCarrier_old_contribution D x hd i w hw))
    _ = D.endpointCount w := Nat.add_zero _

/-- The actual expanded decomposition has the exact hub output of the chosen profile. -/
theorem expandDecomposition_endpointCount_hub (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) :
    (expandDecomposition D x hd).endpointCount (Sum.inl x) = (profileOf D x).output := by
  rw [expandDecomposition, Decomposition.ofFamily_endpointCount, Fintype.sum_sum_type]
  dsimp only [expansionFamily]
  calc
    _ = 0 + ∑ _i : Fin 2, (if profileOf D x = .two then 1 else 0 : ℕ) :=
      congrArg₂ Nat.add
        (Finset.sum_eq_zero (fun i _ => restoredOldCarrier_hub_contribution D x hd i))
        (Finset.sum_congr rfl (fun i _ => addedCarrier_hub_contribution D x hd i))
    _ = (profileOf D x).output := by
      cases profileOf D x <;> simp [Profile.output]

/-- A literal input endpoint count of zero, two or four yields output zero, two or zero. -/
theorem expandDecomposition_endpointCount_profiles (D : Decomposition H) (x : V)
    (hd : H.degree x = 4) :
    (D.endpointCount x = 0 → (expandDecomposition D x hd).endpointCount (Sum.inl x) = 0) ∧
      (D.endpointCount x = 2 → (expandDecomposition D x hd).endpointCount (Sum.inl x) = 2) ∧
      (D.endpointCount x = 4 → (expandDecomposition D x hd).endpointCount (Sum.inl x) = 0) := by
  simp only [expandDecomposition_endpointCount_hub]
  constructor
  · intro h; simp [profileOf, h, Profile.output]
  constructor
  · intro h; simp [profileOf, h, Profile.output]
  · intro h; simp [profileOf, h, Profile.output]

end Gallai.Star
