/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Foundations.HubProfiles
import Gallai.Structure.SyndromeStar
import Mathlib.Data.Fintype.EquivFin

/-! # Three distinct reserve carriers separated from the hub component

The one-credit reconstruction uses three endpoint occurrences at one remote
anchor. This selects actual distinct carrier indices and proves full support
disjointness from every hub-containing path, without requiring the three
reserve carriers to be mutually vertex-disjoint.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The exact supply needed by the one-credit merging schemes. -/
theorem sizeTwo_rich_carrier_selection (D : Decomposition B.syndromeStar)
    (w : B.StarSurvivor) (hsep : ¬ B.syndromeStar.Reachable B.completedHub w)
    (hw : 3 ≤ D.endpointCount w) :
    ∃ f : Fin 3 ↪ Fin D.size, ∀ l,
      ((D.path (f l)).start = w ∨ (D.path (f l)).finish = w) ∧
      ∀ k, B.completedHub ∈ (D.path k).walk.support →
        k ≠ f l ∧ Disjoint (D.path k).walk.support.toFinset
          (D.path (f l)).walk.support.toFinset := by
  classical
  have hcount : 3 ≤ (D.terminalCarriers w).card := by rwa [D.card_terminalCarriers]
  obtain ⟨T,hT,hcard⟩ := Finset.exists_subset_card_eq hcount
  let e : Fin 3 ≃ {k // k ∈ T} :=
    (Fintype.equivFinOfCardEq (by simpa only [Fintype.card_coe] using hcard)).symm
  let f : Fin 3 ↪ Fin D.size := e.toEmbedding.trans (Function.Embedding.subtype _)
  have hend (l : Fin 3) : (D.path (f l)).start = w ∨ (D.path (f l)).finish = w :=
    (Finset.mem_filter.mp (hT (e l).property)).2
  refine ⟨f,?_⟩
  intro l
  refine ⟨hend l,?_⟩
  intro k hk
  have hd : Disjoint (D.path k).walk.support.toFinset
      (D.path (f l)).walk.support.toFinset := by
    apply Finset.disjoint_left.mpr
    intro v hvk hvl
    have hvk' := List.mem_toFinset.mp hvk
    have hvl' := List.mem_toFinset.mp hvl
    have hxv : B.syndromeStar.Reachable B.completedHub v :=
      ((D.path k).walk.takeUntil B.completedHub hk).reachable.symm.trans
        ((D.path k).walk.takeUntil v hvk').reachable
    apply hsep
    apply hxv.trans
    rcases hend l with hs | ht
    · exact hs ▸ ((D.path (f l)).walk.takeUntil v hvl').reachable.symm
    · exact ht ▸ ((D.path (f l)).walk.dropUntil v hvl').reachable
  refine ⟨?_,hd⟩
  intro he
  have hk' : B.completedHub ∈ (D.path (f l)).walk.support.toFinset := by
    rw [← he]
    exact List.mem_toFinset.mpr hk
  exact Finset.disjoint_left.mp hd (List.mem_toFinset.mpr hk) hk'

end Gallai.WholeBowtie
