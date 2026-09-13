/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.RetainedRemoteSeparation
import Gallai.Foundations.DegreeTwoCarriers

/-! # Distinct actual carrier indices for cheap retained reconstruction -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Component separation forbids a remote endpoint on any hub-containing carrier. -/
theorem retained_remote_index_ne (H : SimpleGraph B.StarSurvivor)
    (r : B.StarSurvivor) (hr : ¬ H.Reachable B.completedHub r)
    (D : Decomposition H) (i j : Fin D.size)
    (hi : B.completedHub ∈ (D.path i).walk.support)
    (hj : (D.path j).start = r ∨ (D.path j).finish = r) : i ≠ j := by
  intro he
  subst j
  apply B.retained_hub_walk_avoids_remote H r hr (D.path i).walk hi
  rcases hj with hs | ht
  · exact hs ▸ (D.path i).walk.start_mem_support
  · exact ht ▸ (D.path i).walk.end_mem_support

/-- Select the through index and a different remote endpoint index directly
from degree two, zero hub endpoints and positive remote endpoint supply. -/
theorem retainedCheap_passing_selection (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj] (r : B.StarSurvivor)
    (hr : ¬ H.Reachable B.completedHub r) (D : Decomposition H)
    (hd : H.degree B.completedHub = 2) (hz : D.endpointCount B.completedHub = 0)
    (hpos : 0 < D.endpointCount r) :
    ∃ i j : Fin D.size, i ≠ j ∧ B.completedHub ∈ (D.path i).walk.support ∧
      (D.path i).start ≠ B.completedHub ∧ B.completedHub ≠ (D.path i).finish ∧
      ((D.path j).start = r ∨ (D.path j).finish = r) := by
  obtain ⟨i, hi, hs, ht, _⟩ := D.degree_two_through_carrier B.completedHub hd hz
  have hp : 0 < (D.terminalCarriers r).card := by rw [D.card_terminalCarriers]; exact hpos
  obtain ⟨j, hj⟩ := Finset.card_pos.mp hp
  have hj' := (Finset.mem_filter.mp hj).2
  exact ⟨i,j,B.retained_remote_index_ne H r hr D i j hi hj',hi,hs,ht,hj'⟩

/-- Select both hub-terminal indices and one remote index. All three are
distinct even if the two hub carriers intersect at other old vertices. -/
theorem retainedCheap_ending_selection (H : SimpleGraph B.StarSurvivor)
    [DecidableRel H.Adj] (r : B.StarSurvivor)
    (hr : ¬ H.Reachable B.completedHub r) (D : Decomposition H)
    (hd : H.degree B.completedHub = 2) (hz : 0 < D.endpointCount B.completedHub)
    (hpos : 0 < D.endpointCount r) :
    ∃ i j k : Fin D.size, i ≠ j ∧ i ≠ k ∧ j ≠ k ∧
      ((D.path i).start = B.completedHub ∨ (D.path i).finish = B.completedHub) ∧
      ((D.path j).start = B.completedHub ∨ (D.path j).finish = B.completedHub) ∧
      ((D.path k).start = r ∨ (D.path k).finish = r) := by
  have hb := D.degree_eq_endpoint_add_twice_through B.completedHub
  have hc : (D.terminalCarriers B.completedHub).card = 2 := by
    rw [D.card_terminalCarriers]
    omega
  obtain ⟨i,j,hij,hset⟩ := Finset.card_eq_two.mp hc
  have terminal (k : Fin D.size) (hk : k ∈ ({i,j} : Finset _)) :
      (D.path k).start = B.completedHub ∨ (D.path k).finish = B.completedHub := by
    have hm : k ∈ D.terminalCarriers B.completedHub := hset.symm ▸ hk
    exact (Finset.mem_filter.mp hm).2
  have hi := terminal i (by simp)
  have hj := terminal j (by simp)
  have support (k : Fin D.size)
      (h : (D.path k).start = B.completedHub ∨ (D.path k).finish = B.completedHub) :
      B.completedHub ∈ (D.path k).walk.support := by
    rcases h with hs | ht
    · exact hs ▸ (D.path k).walk.start_mem_support
    · exact ht ▸ (D.path k).walk.end_mem_support
  have hp : 0 < (D.terminalCarriers r).card := by rw [D.card_terminalCarriers]; exact hpos
  obtain ⟨k, hk⟩ := Finset.card_pos.mp hp
  have hk' := (Finset.mem_filter.mp hk).2
  exact ⟨i,j,k,hij,B.retained_remote_index_ne H r hr D i k (support i hi) hk',
    B.retained_remote_index_ne H r hr D j k (support j hj) hk',hi,hj,hk'⟩

end Gallai.WholeBowtie
