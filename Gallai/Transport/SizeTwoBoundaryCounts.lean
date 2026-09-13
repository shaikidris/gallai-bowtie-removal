/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeBoundary
import Gallai.Transport.SyndromeStarCarrier

/-! # Exact auxiliary/local edge cancellation for the size-two syndrome

Auxiliary spokes may be synthetic. Their mapped multiplicity is accounted
for separately from the original local target, never assumed to embed in G.
-/
namespace Gallai.WholeBowtie
open Certificate Certificate.CompletedStar
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Injective survivor mapping transports an auxiliary decomposition's total
edge multiplicity exactly, even for synthetic edges. -/
theorem syndrome_mapped_count (D : Decomposition B.syndromeStar) (e : Sym2 V) :
    (∑ k : Fin D.size, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) =
      if ∃ f ∈ B.syndromeStar.edgeSet, Sym2.map Subtype.val f = e then 1 else 0 := by
  classical
  by_cases he : ∃ f ∈ B.syndromeStar.edgeSet, Sym2.map Subtype.val f = e
  · rw [if_pos he]
    obtain ⟨f,hf,rfl⟩ := he
    simp only [List.count_map_of_injective _ _ (Sym2.map.injective Subtype.val_injective)]
    exact (D.sum_edge_count f).trans (if_pos hf)
  · rw [if_neg he]
    apply Finset.sum_eq_zero
    intro k _
    apply List.count_eq_zero.mpr
    intro hm
    obtain ⟨f,hf,hfe⟩ := List.mem_map.mp hm
    exact he ⟨f,(D.path k).walk.edges_subset_edgeSet hf,hfe⟩

/-- Every auxiliary hub edge maps to exactly one of the two syndrome spokes. -/
theorem sizeTwo_auxiliary_spoke_image (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (f : Sym2 B.StarSurvivor) (hf : f ∈ B.syndromeStar.edgeSet)
    (hx : B.completedHub ∈ f) :
    Sym2.map Subtype.val f = s(B.label 0,(A 0).val) ∨
      Sym2.map Subtype.val f = s(B.label 0,(A 1).val) := by
  induction f using Sym2.inductionOn with
  | hf u v =>
    rcases Sym2.mem_iff.mp hx with hu | hv
    · subst u
      have hs := (B.syndromeStar_hub_adj v).mp hf
      rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with hs | hs
      · exact Or.inl (by change s(B.label 0,v.val) = _; rw [hs])
      · exact Or.inr (by change s(B.label 0,v.val) = _; rw [hs])
    · subst v
      have hs := (B.syndromeStar_hub_adj u).mp hf.symm
      rw [hSigma,Finset.mem_insert,Finset.mem_singleton] at hs
      rcases hs with hs | hs
      · exact Or.inl (by change s(u.val,B.label 0) = _; rw [hs]; exact Sym2.eq_swap)
      · exact Or.inr (by change s(u.val,B.label 0) = _; rw [hs]; exact Sym2.eq_swap)

/-- Both normalized spokes actually belong to the auxiliary, whether or not
they were present in the original graph. -/
theorem sizeTwo_spoke_has_preimage (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (j : Fin 4) (hj : j = 0 ∨ j = 1) :
    ∃ f ∈ B.syndromeStar.edgeSet, Sym2.map Subtype.val f = s(B.label 0,(A j).val) := by
  let v := B.completedOutside (A j).val (B.numberedAnchor_not_mem A j)
  refine ⟨s(B.completedHub,v),?_,rfl⟩
  apply (B.syndromeStar_hub_adj v).mpr
  rcases hj with rfl | rfl <;> simp [hSigma,v,completedOutside]

/-- A local target edge is an auxiliary edge exactly when it is one of the
two normalized spokes. All other local edges were deleted with the core. -/
theorem sizeTwo_local_auxiliary_iff (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (q : Sym2 Star.Vertex) (hq : q ∈ targetEdges (B.completedStarState A)) :
    (∃ f ∈ B.syndromeStar.edgeSet, Sym2.map Subtype.val f = Sym2.map (B.completedLabel A) q) ↔
      Sym2.map (B.completedLabel A) q = s(B.label 0,(A 0).val) ∨
      Sym2.map (B.completedLabel A) q = s(B.label 0,(A 1).val) := by
  constructor
  · rintro ⟨f,hf,hfe⟩
    obtain ⟨v,hv,hvB⟩ := B.completed_target_incident A q hq
    rw [← hfe] at hv
    obtain ⟨w,hw,rfl⟩ := Sym2.mem_map.mp hv
    have hwx : w = B.completedHub := Subtype.ext (B.survivor_mem_vertices w hvB)
    rw [← hfe]
    exact B.sizeTwo_auxiliary_spoke_image A hSigma f hf (hwx ▸ hw)
  · intro he
    rcases he with he | he
    · rw [he]
      exact B.sizeTwo_spoke_has_preimage A hSigma 0 (Or.inl rfl)
    · rw [he]
      exact B.sizeTwo_spoke_has_preimage A hSigma 1 (Or.inr rfl)

/-- The auxiliary's entire contribution on a local target is cancelled by
the released two-spoke list, with exact multiplicity. -/
theorem sizeTwo_auxiliary_local_count (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar)
    (q : Sym2 Star.Vertex) (hq : q ∈ targetEdges (B.completedStarState A)) :
    (∑ k : Fin D.size, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count
      (Sym2.map (B.completedLabel A) q)) =
      ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count
        (Sym2.map (B.completedLabel A) q) := by
  classical
  have hne : s(B.label 0,(A 0).val) ≠ s(B.label 0,(A 1).val) := by
    intro he
    have hv := Sym2.eq_iff.mp he
    have ha : (A 0).val = (A 1).val := by
      rcases hv with hv | hv
      · exact hv.2
      · exact hv.2.trans hv.1
    exact (by decide : (0 : Fin 4) ≠ 1) (A.injective (Subtype.ext ha))
  rw [B.syndrome_mapped_count]
  simp only [B.sizeTwo_local_auxiliary_iff A hSigma q hq]
  by_cases hp : Sym2.map (B.completedLabel A) q = s(B.label 0,(A 0).val)
  · simp [hp,hne,Ne.symm hne]
  by_cases hr : Sym2.map (B.completedLabel A) q = s(B.label 0,(A 1).val)
  · simp [hr,hne,Ne.symm hne]
  · simp [hp,hr,Ne.symm hp,Ne.symm hr]

/-- Retained nonspokes belong to the syndrome auxiliary, not just the completed star. -/
theorem syndrome_contains_retained_nonspoke (f : Sym2 B.StarSurvivor)
    (hf : f ∈ B.completedStar.edgeSet) (hx : B.completedHub ∉ f) :
    f ∈ B.syndromeStar.edgeSet := by
  induction f using Sym2.inductionOn with
  | hf u v =>
    have hu : u.val ≠ B.label 0 := by
      intro he
      have hh : u = B.completedHub := Subtype.ext he
      exact hx (by simp [hh])
    have hv : v.val ≠ B.label 0 := by
      intro he
      have hh : v = B.completedHub := Subtype.ext he
      exact hx (by simp [hh])
    exact (B.syndromeStar_away_adj u v hu hv).mpr
      ((B.completedStar_adj_off_hub u v hu hv).mp hf)

/-- A mapped retained nonspoke cannot coincide with any hub spoke. -/
theorem syndrome_nonspoke_ne_spoke (f : Sym2 B.StarSurvivor)
    (hx : B.completedHub ∉ f) (v : V) :
    Sym2.map Subtype.val f ≠ s(B.label 0,v) := by
  intro he
  have hm : B.label 0 ∈ Sym2.map Subtype.val f := by rw [he]; simp
  obtain ⟨w,hw,hwv⟩ := Sym2.mem_map.mp hm
  have hh : w = B.completedHub := Subtype.ext hwv
  exact hx (hh ▸ hw)

/-- The exact original-edge balance: adding the local target to the mapped
auxiliary counts each original edge once, plus precisely the released spokes.
This includes original spokes and synthetic spokes without conflating them. -/
theorem sizeTwo_original_edge_balance (A : B.AnchorNumbering)
    (hSigma : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (e : Sym2 V) (he : e ∈ G.edgeSet) :
    (∑ k : Fin D.size, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count e) +
      ((targetEdges (B.completedStarState A)).val.map (Sym2.map (B.completedLabel A))).count e =
      1 + ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count e := by
  classical
  rcases B.completed_edge_cases A e he with ⟨q,hq,hx,rfl⟩ | ⟨q,hq,rfl⟩
  · have haux : (∑ k : Fin D.size, ((D.path k).walk.edges.map (Sym2.map Subtype.val)).count
        (Sym2.map Subtype.val q)) = 1 := by
      rw [B.syndrome_mapped_count,if_pos]
      exact ⟨q,B.syndrome_contains_retained_nonspoke q hq hx,rfl⟩
    have hlocal : ((targetEdges (B.completedStarState A)).val.map (Sym2.map (B.completedLabel A))).count
        (Sym2.map Subtype.val q) = 0 := by
      apply Multiset.count_eq_zero.mpr
      intro hm
      obtain ⟨t,ht,htq⟩ := Multiset.mem_map.mp hm
      exact B.completed_retained_ne_target A q hx t ht htq.symm
    have hsp : ([s(B.label 0,(A 0).val),s(B.label 0,(A 1).val)] : List (Sym2 V)).count
        (Sym2.map Subtype.val q) = 0 := by
      apply List.count_eq_zero.mpr
      intro hm
      have hm' : Sym2.map Subtype.val q = s(B.label 0,(A 0).val) ∨
          Sym2.map Subtype.val q = s(B.label 0,(A 1).val) := by
        simpa using hm
      exact hm'.elim (B.syndrome_nonspoke_ne_spoke q hx (A 0).val)
        (B.syndrome_nonspoke_ne_spoke q hx (A 1).val)
    rw [haux,hlocal,hsp]
  · rw [B.sizeTwo_auxiliary_local_count A hSigma D q hq,B.zero_local_count_target A q hq]
    omega

end Gallai.WholeBowtie
