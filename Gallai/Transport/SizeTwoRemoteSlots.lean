/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoTerminalSelection
import Mathlib.Data.Option.Basic

/-! # Unique actual endpoint slots for the two ordinary remote roles -/
namespace Gallai.Certificate.SizeTwo

/-- The two remote words follow the one through role or the two terminal roles. -/
def remoteRole (i : Fin 13) (r : Fin 2) : Fin 4 :=
  if through i then ⟨r.val + 1,by omega⟩ else ⟨r.val + 2,by omega⟩

theorem remoteRole_injective (i : Fin 13) : Function.Injective (remoteRole i) := by
  intro r s he
  unfold remoteRole at he
  split at he <;> apply Fin.ext <;> have hv := congrArg Fin.val he <;> dsimp at hv <;> omega

theorem remoteRole_boundary : ∀ i : Fin 13, ∀ r : Fin 2,
    boundary i (remoteRole i r) = [CompletedStar.anchor ⟨r.val + 2,by omega⟩] := by decide

end Gallai.Certificate.SizeTwo

namespace Gallai.Decomposition
variable {V : Type*} [DecidableEq V] {H : SimpleGraph V}
variable (D : Decomposition H) (marks : Fin 2 ↪ V) (f : Fin 2 → Fin D.size)
variable (hf : ∀ r, (D.path (f r)).start = marks r ∨ (D.path (f r)).finish = marks r)

/-- False is the start slot and true the finish slot of the actual old path. -/
def remoteSlotVertex (slot : Fin D.size × Bool) : V :=
  if slot.2 then (D.path slot.1).finish else (D.path slot.1).start

def remoteSlot (r : Fin 2) : Fin D.size × Bool :=
  (f r, if (D.path (f r)).start = marks r then false else true)

include hf in
theorem remoteSlot_vertex (r : Fin 2) :
    D.remoteSlotVertex (D.remoteSlot marks f r) = marks r := by
  unfold remoteSlot remoteSlotVertex
  by_cases he : (D.path (f r)).start = marks r
  · simp only [if_pos he,Bool.false_eq_true,ite_false]
    exact he
  · simp only [if_neg he,ite_true]
    exact (hf r).resolve_left he

include hf in
/-- Even when both remote roles use one carrier, they use distinct end slots. -/
theorem remoteSlot_injective : Function.Injective (D.remoteSlot marks f) := by
  intro r s he
  apply marks.injective
  exact (D.remoteSlot_vertex marks f hf r).symm.trans
    ((congrArg D.remoteSlotVertex he).trans (D.remoteSlot_vertex marks f hf s))

/-- An endpoint slot either receives its unique remote role or receives none. -/
noncomputable def remoteAt (slot : Fin D.size × Bool) : Option (Fin 2) :=
  if h : ∃ r, D.remoteSlot marks f r = slot then some h.choose else none

include hf in
theorem remoteAt_mem (slot : Fin D.size × Bool) (r : Fin 2) :
    r ∈ D.remoteAt marks f slot ↔ D.remoteSlot marks f r = slot := by
  classical
  unfold remoteAt
  split
  · rename_i he
    constructor
    · intro hr
      have her : he.choose = r := by simpa only [Option.mem_some_iff] using hr
      exact her ▸ he.choose_spec
    · intro hr
      have her := D.remoteSlot_injective marks f hf (he.choose_spec.trans hr.symm)
      simpa only [Option.mem_some_iff] using her
  · rename_i he
    simp only [Option.not_mem_none, false_iff]
    exact fun hr => he ⟨r,hr⟩

include hf in
theorem remoteAt_weight (slot : Fin D.size × Bool) (weight : Fin 2 → ℕ) :
    ((D.remoteAt marks f slot).map weight).getD 0 =
      ∑ r : Fin 2, if D.remoteSlot marks f r = slot then weight r else 0 := by
  classical
  cases ho : D.remoteAt marks f slot with
  | none =>
    have hn (r : Fin 2) : D.remoteSlot marks f r ≠ slot := by
      intro hr
      have hm := (D.remoteAt_mem marks f hf slot r).mpr hr
      rw [ho] at hm
      simp at hm
    simp [hn]
  | some r =>
    have hr : D.remoteSlot marks f r = slot :=
      (D.remoteAt_mem marks f hf slot r).mp (by rw [ho]; simp)
    have he (s : Fin 2) : D.remoteSlot marks f s = slot ↔ s = r :=
      ⟨fun hs => D.remoteSlot_injective marks f hf (hs.trans hr.symm),fun hs => hs ▸ hr⟩
    simp only [Option.map_some,Option.getD_some,he,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

include hf in
/-- Each carrier consumes exactly its selected remote words once, independent
of which of its two ends supplies their attachment. -/
theorem remoteAt_carrier_sum (k : Fin D.size) (weight : Fin 2 → ℕ) :
    (∑ side : Bool, ((D.remoteAt marks f (k,side)).map weight).getD 0) =
      ∑ r : Fin 2, if f r = k then weight r else 0 := by
  simp_rw [D.remoteAt_weight marks f hf]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro r _
  simp only [remoteSlot,Prod.mk.injEq]
  by_cases he : f r = k
  · by_cases hs : (D.path k).start = marks r <;> simp [he,hs]
  · simp [he]

/-- Translate the two actual remote slots to the four-role catalogue indices. -/
noncomputable def remoteRecordSlot (i : Fin 13) (slot : Fin D.size × Bool) : Option (Fin 4) :=
  (D.remoteAt marks f slot).map (Certificate.SizeTwo.remoteRole i)

include hf in
/-- A selected catalogue role carries its actual slot and remote-vertex witness. -/
theorem remoteRecordSlot_mem (i : Fin 13) (slot : Fin D.size × Bool) (j : Fin 4) :
    j ∈ D.remoteRecordSlot marks f i slot ↔
      ∃ r : Fin 2, Certificate.SizeTwo.remoteRole i r = j ∧ D.remoteSlot marks f r = slot := by
  unfold remoteRecordSlot
  constructor
  · intro hj
    obtain ⟨r,hr,he⟩ := Option.mem_map.mp hj
    exact ⟨r,he,(D.remoteAt_mem marks f hf slot r).mp hr⟩
  · rintro ⟨r,he,hr⟩
    exact Option.mem_map.mpr ⟨r,(D.remoteAt_mem marks f hf slot r).mpr hr,he⟩

include hf in
/-- The catalogue-indexed slots preserve the per-carrier word accounting. -/
theorem remoteRecordSlot_carrier_sum (i : Fin 13) (k : Fin D.size) (weight : Fin 4 → ℕ) :
    (∑ side : Bool, ((D.remoteRecordSlot marks f i (k,side)).map weight).getD 0) =
      ∑ r : Fin 2, if f r = k then weight (Certificate.SizeTwo.remoteRole i r) else 0 := by
  simpa only [remoteRecordSlot,Option.map_map,Function.comp_def] using
    D.remoteAt_carrier_sum marks f hf k (fun r => weight (Certificate.SizeTwo.remoteRole i r))

include hf in
/-- No remote word can be consumed at both ends of one old carrier. -/
theorem remoteRecordSlot_ends_disjoint (i : Fin 13) (k : Fin D.size) (j l : Fin 4)
    (hj : j ∈ D.remoteRecordSlot marks f i (k,false))
    (hl : l ∈ D.remoteRecordSlot marks f i (k,true)) : j ≠ l := by
  intro he
  obtain ⟨r,hr,hrs⟩ := (D.remoteRecordSlot_mem marks f hf i (k,false) j).mp hj
  obtain ⟨s,hs,hss⟩ := (D.remoteRecordSlot_mem marks f hf i (k,true) l).mp hl
  have hrs' := Certificate.SizeTwo.remoteRole_injective i (hr.trans (he.trans hs.symm))
  subst s
  have hbad := congrArg Prod.snd (hrs.symm.trans hss)
  cases hbad

end Gallai.Decomposition
