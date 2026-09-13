/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.DegreeTwoCarriers
import Gallai.Operations.SpokeMembership

/-! # Normalize and identify the actual two terminal spoke carriers -/
namespace Gallai.Decomposition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- At a degree-two hub with two endpoints, the two adjacent edges select
distinct carriers. Uniform orientation makes their final neighbours exactly
p and q, not an unspecified permutation. No other path contains the hub. -/
theorem degree_two_terminal_spoke_selection (D : Decomposition H) (x p q : V)
    (hd : H.degree x = 2) (he : D.endpointCount x = 2)
    (hp : H.Adj x p) (hq : H.Adj x q) (hpq : p ≠ q) :
    ∃ ip iq : Fin D.size, ip ≠ iq ∧
      ((D.orientToward x).path ip).finish = x ∧
      ((D.orientToward x).path ip).walk.reverse.snd = p ∧
      ((D.orientToward x).path iq).finish = x ∧
      ((D.orientToward x).path iq).walk.reverse.snd = q ∧
      ∀ k : Fin D.size, k ≠ ip → k ≠ iq → x ∉ (D.path k).walk.support := by
  have hb := D.degree_eq_endpoint_add_twice_through x
  have hz : D.throughCarriers x = ∅ := Finset.card_eq_zero.mp (by
    rw [D.card_throughCarriers]
    omega)
  have terminal (k : Fin D.size) (hk : x ∈ (D.path k).walk.support) :
      (D.path k).start = x ∨ (D.path k).finish = x := by
    have h := (D.mem_support_iff_terminal_or_through x k).mp hk
    rw [hz] at h
    have hmem : k ∈ D.terminalCarriers x := h.resolve_right (Finset.notMem_empty k)
    exact (Finset.mem_filter.mp hmem).2
  obtain ⟨ip,hip,_⟩ := D.covers s(x,p) hp
  obtain ⟨iq,hiq,_⟩ := D.covers s(x,q) hq
  have htp := terminal ip ((D.path ip).walk.fst_mem_support_of_mem_edges hip)
  have htq := terminal iq ((D.path iq).walk.fst_mem_support_of_mem_edges hiq)
  have hsp : p = ((D.orientToward x).path ip).walk.reverse.snd :=
    ((D.path ip).terminal_spoke_iff x p htp).mp hip
  have hsq : q = ((D.orientToward x).path iq).walk.reverse.snd :=
    ((D.path iq).terminal_spoke_iff x q htq).mp hiq
  have hneq : ip ≠ iq := by
    intro h
    subst iq
    exact hpq (hsp.trans hsq.symm)
  have hsub : ({ip,iq} : Finset (Fin D.size)) ⊆ D.terminalCarriers x := by
    intro k hk
    rcases Finset.mem_insert.mp hk with hk | hk
    · subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htp⟩
    · have hk' := Finset.mem_singleton.mp hk
      subst k
      exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,htq⟩
  have hset : ({ip,iq} : Finset (Fin D.size)) = D.terminalCarriers x :=
    Finset.eq_of_subset_of_card_le hsub (by rw [D.card_terminalCarriers,he,Finset.card_pair hneq])
  refine ⟨ip,iq,hneq,D.orientToward_terminal x ip htp,hsp.symm,
    D.orientToward_terminal x iq htq,hsq.symm,?_⟩
  intro k hkp hkq hk
  have hkt := terminal k hk
  have hkm : k ∈ D.terminalCarriers x := Finset.mem_filter.mpr ⟨Finset.mem_univ _,hkt⟩
  rw [← hset,Finset.mem_insert,Finset.mem_singleton] at hkm
  exact hkm.elim hkp hkq

end Gallai.Decomposition
