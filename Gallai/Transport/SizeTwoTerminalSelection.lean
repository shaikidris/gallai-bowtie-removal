/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoPartitions
import Gallai.Operations.DoubleMerge
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Data.Set.Finite.Range
import Mathlib.Tactic.FinCases

/-! # Actual terminal carrier selection for the ordinary size-two interface -/
namespace Gallai

/-- Four selected carriers admit a four-label code preserving exactly equality. -/
theorem four_owner_code {I : Type*} (f : Fin 4 → I) :
    ∃ g : Fin 4 → Fin 4, ∀ i j, g i = g j ↔ f i = f j := by
  classical
  obtain ⟨e⟩ := Function.Embedding.nonempty_of_card_le
    (show Fintype.card (Set.range f) ≤ Fintype.card (Fin 4) from Fintype.card_range_le f)
  refine ⟨fun i => e ⟨f i,⟨i,rfl⟩⟩, ?_⟩
  intro i j
  exact ⟨fun h => congrArg Subtype.val (e.injective h),fun h => congrArg e (Subtype.ext h)⟩

namespace Decomposition
variable {V : Type*} [DecidableEq V] {H : SimpleGraph V}

omit [DecidableEq V] in
/-- A path with endpoint x cannot also have two different non-x endpoints. -/
theorem terminal_not_two_remote (D : Decomposition H) (i : Fin D.size)
    (x r s : V) (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hx : (D.path i).start = x ∨ (D.path i).finish = x)
    (hr : (D.path i).start = r ∨ (D.path i).finish = r)
    (hs : (D.path i).start = s ∨ (D.path i).finish = s) : False := by
  rcases hx with hx | hx <;> rcases hr with hr | hr <;> rcases hs with hs | hs
  all_goals first
    | exact hxr (hx.symm.trans hr)
    | exact hxs (hx.symm.trans hs)
    | exact hrs (hr.symm.trans hs)

/-- Classify remote carriers while preserving the two already identified
hub-spoke carriers and their order. No mutual disjointness is assumed. -/
theorem sizeTwo_terminal_selection_fixed (D : Decomposition H) (x r s : V)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (a b : Fin D.size) (hab : a ≠ b)
    (ha : (D.path a).start = x ∨ (D.path a).finish = x)
    (hb : (D.path b).start = x ∨ (D.path b).finish = x)
    (hr : 0 < D.endpointCount r)
    (hs : 0 < D.endpointCount s) :
    ∃ f : Fin 4 → Fin D.size, ∃ i : Fin 13,
      f 0 = a ∧ f 1 = b ∧
      Certificate.SizeTwo.through i = false ∧
      (∀ j, (D.path (f j)).start = (![x,x,r,s] j) ∨
        (D.path (f j)).finish = (![x,x,r,s] j)) ∧
      (∀ j k, f j = f k ↔ Certificate.SizeTwo.owner i j = Certificate.SizeTwo.owner i k) := by
  classical
  have select (v : V) (hv : 0 < D.endpointCount v) :
      ∃ c : Fin D.size, (D.path c).start = v ∨ (D.path c).finish = v := by
    have ht : 0 < (D.terminalCarriers v).card := by rwa [D.card_terminalCarriers]
    obtain ⟨c,hc⟩ := Finset.card_pos.mp ht
    exact ⟨c,(Finset.mem_filter.mp hc).2⟩
  obtain ⟨c,hc⟩ := select r hr
  obtain ⟨d,hd⟩ := select s hs
  let f : Fin 4 → Fin D.size := ![a,b,c,d]
  obtain ⟨g,hg⟩ := four_owner_code f
  have valid : Certificate.SizeTwo.ValidOwners false g := by
    right
    refine ⟨fun h => hab ((hg 0 1).mp h), ?_, ?_⟩
    · rintro ⟨hca,hda⟩
      have hca' : c = a := (hg 2 0).mp hca
      have hda' : d = a := (hg 3 0).mp hda
      exact D.terminal_not_two_remote a x r s hxr hxs hrs ha (hca' ▸ hc) (hda' ▸ hd)
    · rintro ⟨hcb,hdb⟩
      have hcb' : c = b := (hg 2 1).mp hcb
      have hdb' : d = b := (hg 3 1).mp hdb
      exact D.terminal_not_two_remote b x r s hxr hxs hrs hb (hcb' ▸ hc) (hdb' ▸ hd)
  obtain ⟨i,hi,hpart⟩ := Certificate.SizeTwo.owner_partition_complete false g valid
  refine ⟨f,i,rfl,rfl,hi,?_,?_⟩
  · intro j
    fin_cases j <;> assumption
  · intro j k
    exact (hg j k).symm.trans (hpart j k (by simp))

/-- Select actual hub/remote endpoint carriers and classify their equality
pattern. This retains the original interface for existing consumers. -/
theorem sizeTwo_terminal_selection (D : Decomposition H) (x r s : V)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hx : 2 ≤ D.endpointCount x) (hr : 0 < D.endpointCount r)
    (hs : 0 < D.endpointCount s) :
    ∃ f : Fin 4 → Fin D.size, ∃ i : Fin 13,
      Certificate.SizeTwo.through i = false ∧
      (∀ j, (D.path (f j)).start = (![x,x,r,s] j) ∨
        (D.path (f j)).finish = (![x,x,r,s] j)) ∧
      (∀ j k, f j = f k ↔ Certificate.SizeTwo.owner i j = Certificate.SizeTwo.owner i k) := by
  obtain ⟨a,b,hab,ha,hb⟩ := D.two_terminal_carriers x hx
  obtain ⟨f,i,_,_,hi,hends,howner⟩ := D.sizeTwo_terminal_selection_fixed x r s hxr hxs hrs
    a b hab ha hb hr hs
  exact ⟨f,i,hi,hends,howner⟩

end Decomposition
end Gallai
