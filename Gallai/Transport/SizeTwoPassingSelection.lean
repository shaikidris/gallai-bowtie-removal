/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoTerminalSelection

/-! # Actual through-hub carrier selection for a degree-two auxiliary hub -/
namespace Gallai.Decomposition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Degree two permits just the through or two-terminal interface. -/
theorem degree_two_carrier_profiles (D : Decomposition H) (x : V)
    (hd : H.degree x = 2) :
    (D.endpointCount x = 0 ∧ D.throughCount x = 1) ∨
    (D.endpointCount x = 2 ∧ D.throughCount x = 0) := by
  have h := D.degree_eq_endpoint_add_twice_through x
  omega

/-- In the through case, select the unique internal hub carrier and endpoint
carriers at r,s, with their exact coincidence pattern. The fourth slot is
inactive and deliberately excluded from the partition comparison. -/
theorem sizeTwo_passing_selection (D : Decomposition H) (x r s : V)
    (hd : H.degree x = 2) (hx : D.endpointCount x = 0)
    (hr : 0 < D.endpointCount r) (hs : 0 < D.endpointCount s) :
    ∃ f : Fin 4 → Fin D.size, ∃ i : Fin 13,
      Certificate.SizeTwo.through i = true ∧
      x ∈ (D.path (f 0)).walk.support ∧
      (D.path (f 0)).start ≠ x ∧ (D.path (f 0)).finish ≠ x ∧
      ((D.path (f 1)).start = r ∨ (D.path (f 1)).finish = r) ∧
      ((D.path (f 2)).start = s ∨ (D.path (f 2)).finish = s) ∧
      (∀ j k, j ≠ 3 → k ≠ 3 →
        (f j = f k ↔ Certificate.SizeTwo.owner i j = Certificate.SizeTwo.owner i k)) ∧
      (∀ t : Fin D.size, x ∈ (D.path t).walk.support → t = f 0) := by
  classical
  have hc : D.throughCount x = 1 := by
    have h := D.degree_eq_endpoint_add_twice_through x
    omega
  have hcard : (D.throughCarriers x).card = 1 := by rw [D.card_throughCarriers,hc]
  obtain ⟨a,ha⟩ := Finset.card_eq_one.mp hcard
  have ham : a ∈ D.throughCarriers x := by rw [ha]; simp
  obtain ⟨hax,has,haf⟩ := (Finset.mem_filter.mp ham).2
  have select (v : V) (hv : 0 < D.endpointCount v) :
      ∃ c : Fin D.size, (D.path c).start = v ∨ (D.path c).finish = v := by
    have ht : 0 < (D.terminalCarriers v).card := by rwa [D.card_terminalCarriers]
    obtain ⟨c,hc⟩ := Finset.card_pos.mp ht
    exact ⟨c,(Finset.mem_filter.mp hc).2⟩
  obtain ⟨b,hb⟩ := select r hr
  obtain ⟨c,hc'⟩ := select s hs
  let f : Fin 4 → Fin D.size := ![a,b,c,a]
  obtain ⟨g,hg⟩ := Gallai.four_owner_code f
  obtain ⟨i,hi,hpart⟩ := Certificate.SizeTwo.owner_partition_complete true g (Or.inl rfl)
  refine ⟨f,i,hi,hax,has,haf,hb,hc',?_,?_⟩
  · intro j k hj hk
    exact (hg j k).symm.trans (hpart j k (fun _ => ⟨hj,hk⟩))
  · intro t ht
    have hterminal : D.terminalCarriers x = ∅ := by
      apply Finset.card_eq_zero.mp
      rw [D.card_terminalCarriers,hx]
    have hsx : (D.path t).start ≠ x := by
      intro he
      have hm : t ∈ D.terminalCarriers x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inl he⟩
      simp [hterminal] at hm
    have hfx : (D.path t).finish ≠ x := by
      intro he
      have hm : t ∈ D.terminalCarriers x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,Or.inr he⟩
      simp [hterminal] at hm
    have hm : t ∈ D.throughCarriers x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,ht,hsx,hfx⟩
    rw [ha] at hm
    exact Finset.mem_singleton.mp hm

end Gallai.Decomposition
