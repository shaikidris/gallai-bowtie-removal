/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.CompletedStarRows
import Gallai.Structure.InactiveBowtieDeletion

/-! # The actual retained-star auxiliary

Complete the centre to every original anchor and delete all four private
vertices. Connectivity does not assume connected deletion or full syndrome.
The syndrome will be needed for parity, not for this graph construction.
-/

namespace Gallai.WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- An external anchor is outside the original whole bowtie. -/
theorem anchor_not_mem_vertices {v : V} (hv : v ∈ B.anchors) : v ∉ B.vertices := by
  obtain ⟨i, hi⟩ := (B.mem_anchors v).mp hv
  exact ((B.mem_row i v).mp hi).2

/-- The hub cannot itself be an external anchor. -/
theorem hub_not_mem_anchors : B.label 0 ∉ B.anchors := by
  intro h
  exact B.anchor_not_mem_vertices h (Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)

/-- All spokes between the hub and the actual anchor set. -/
def anchorSpokes : SimpleGraph V where
  Adj u v := (u = B.label 0 ∧ v ∈ B.anchors) ∨ (v = B.label 0 ∧ u ∈ B.anchors)
  symm.symm u v h := h.symm
  loopless.irrefl v := by
    intro h
    rcases h with ⟨rfl, h⟩ | ⟨rfl, h⟩ <;> exact B.hub_not_mem_anchors h

instance : DecidableRel B.anchorSpokes.Adj :=
  inferInstanceAs (DecidableRel (fun u v =>
    (u = B.label 0 ∧ v ∈ B.anchors) ∨ (v = B.label 0 ∧ u ∈ B.anchors)))

/-- Complete spokes on the original vertex set, prior to private deletion. -/
abbrev starCompletion : SimpleGraph V := G ⊔ B.anchorSpokes

/-- The survivor type excludes exactly the four private vertices. -/
abbrev StarSurvivor := {v : V // v ∉ (Finset.univ.erase 0).map B.label}

/-- The completed-star auxiliary on four fewer vertices. -/
abbrev completedStar : SimpleGraph B.StarSurvivor :=
  B.starCompletion.induce {v | v ∉ (Finset.univ.erase 0).map B.label}

instance : DecidableRel B.completedStar.Adj := fun u v =>
  inferInstanceAs (Decidable (G.Adj u.val v.val ∨
    ((u.val = B.label 0 ∧ v.val ∈ B.anchors) ∨
      (v.val = B.label 0 ∧ u.val ∈ B.anchors))))

/-- The retained hub as a vertex of the auxiliary. -/
def completedHub : B.StarSurvivor := ⟨B.label 0, by simp⟩

/-- Every original anchor survives private deletion. -/
theorem anchor_survives {v : V} (hv : v ∈ B.anchors) :
    v ∉ (Finset.univ.erase 0).map B.label := by
  intro h
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp h
  exact B.anchor_not_mem_vertices hv (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)

omit [DecidableEq V] in
/-- The only original bowtie vertex surviving is its centre. -/
theorem survivor_mem_vertices (v : B.StarSurvivor) (hv : v.val ∈ B.vertices) :
    v.val = B.label 0 := by
  obtain ⟨i, _, hi⟩ := Finset.mem_map.mp hv
  have hz : i = 0 := by
    by_contra hn
    exact v.property (Finset.mem_map.mpr ⟨i, by simp [hn], hi⟩)
  simpa [hz] using hi.symm

/-- Completion reconnects every attachment through the retained hub. -/
theorem completedStar_connected (hc : G.Connected) : B.completedStar.Connected := by
  apply connected_induce_of_deleted_dominated B.starCompletion _ (B.label 0)
  · exact B.completedHub.property
  · exact hc.mono le_sup_left
  · intro u hu v hv huv
    have hu' : u ∈ (Finset.univ.erase 0).map B.label := by simpa using hu
    obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hu'
    rcases huv with ha | ha
    · by_cases hvB : v ∈ B.vertices
      · exact Or.inl (B.survivor_mem_vertices ⟨v, hv⟩ hvB)
      · have hA := (B.mem_anchors v).mpr ⟨i, (B.mem_row i v).mpr ⟨ha, hvB⟩⟩
        exact Or.inr (Or.inr (Or.inl ⟨rfl, hA⟩))
    · rcases ha with ⟨h, _⟩ | ⟨h, _⟩
      · have he := B.label.injective h
        exact ((Finset.mem_erase.mp hi).1 he).elim
      · exact Or.inl h

/-- The completed hub's neighbours are exactly the surviving original anchors. -/
theorem completedHub_adj (v : B.StarSurvivor) :
    B.completedStar.Adj B.completedHub v ↔ v.val ∈ B.anchors := by
  change G.Adj (B.label 0) v.val ∨ B.anchorSpokes.Adj (B.label 0) v.val ↔ _
  constructor
  · rintro (ha | ha)
    · have hout : v.val ∉ B.vertices := by
        intro h
        exact ha.ne (B.survivor_mem_vertices v h).symm
      exact (B.mem_anchors _).mpr ⟨0, (B.mem_row 0 _).mpr ⟨ha, hout⟩⟩
    · rcases ha with ⟨_, h⟩ | ⟨_, h⟩
      · exact h
      · exact (B.hub_not_mem_anchors h).elim
  · intro h
    exact Or.inr (Or.inl ⟨rfl, h⟩)

/-- Exactly four vertices are deleted, independently of incidence masks. -/
theorem completedStar_card : Fintype.card B.StarSurvivor + 4 = Fintype.card V := by
  have h := B.privateDeletion_card (Finset.univ.erase 0)
  have hc : (Finset.univ.erase (0 : Fin 5)).card = 4 := by decide
  rw [hc] at h
  exact h

/-- The completed hub has one neighbour for every original anchor. -/
def completedNeighborEquiv : B.completedStar.neighborSet B.completedHub ≃
    {v // v ∈ B.anchors} where
  toFun v := ⟨v.val.val, (B.completedHub_adj v.val).mp v.property⟩
  invFun v := ⟨⟨v.val, B.anchor_survives v.property⟩,
    (B.completedHub_adj _).mpr v.property⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- In the four-anchor branch this is a genuine degree-four hub. -/
theorem completedHub_degree : B.completedStar.degree B.completedHub = #B.anchors := by
  rw [← SimpleGraph.card_neighborSet_eq_degree]
  exact (Fintype.card_congr B.completedNeighborEquiv).trans (Fintype.card_coe _)

/-- Completion leaves every edge between non-hub survivors untouched. -/
theorem completedStar_adj_off_hub (u v : B.StarSurvivor)
    (hu : u.val ≠ B.label 0) (hv : v.val ≠ B.label 0) :
    B.completedStar.Adj u v ↔ G.Adj u.val v.val := by
  change G.Adj u.val v.val ∨
    ((u.val = B.label 0 ∧ v.val ∈ B.anchors) ∨
      (v.val = B.label 0 ∧ u.val ∈ B.anchors)) ↔ _
  simp only [hu, hv, false_and, or_false]

/-- A non-hub survivor keeps all old outside neighbours and exactly one hub
neighbour when it is an anchor. No anchor-anchor edges are toggled. -/
theorem completedStar_neighbors (v : B.StarSurvivor) (hv : v.val ≠ B.label 0) :
    (B.completedStar.neighborFinset v).map (Function.Embedding.subtype _) =
      (G.neighborFinset v.val \ B.vertices) ∪
        (if v.val ∈ B.anchors then {B.label 0} else ∅) := by
  ext w
  constructor
  · intro hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    have ha := (B.completedStar.mem_neighborFinset v q).mp hq
    by_cases hq0 : q.val = B.label 0
    · have hhub : q = B.completedHub := Subtype.ext hq0
      have hA := (B.completedHub_adj v).mp (hhub ▸ ha.symm)
      exact Finset.mem_union_right _ (by simp [hA, hq0])
    · apply Finset.mem_union_left
      apply Finset.mem_sdiff.mpr
      refine ⟨(G.mem_neighborFinset _ _).mpr
        ((B.completedStar_adj_off_hub v q hv hq0).mp ha), ?_⟩
      exact fun h => hq0 (B.survivor_mem_vertices q h)
  · intro hw
    rcases Finset.mem_union.mp hw with hw | hw
    · obtain ⟨ha, hout⟩ := Finset.mem_sdiff.mp hw
      have hs : w ∉ (Finset.univ.erase 0).map B.label := by
        intro h
        obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp h
        exact hout (Finset.mem_map.mpr ⟨i, Finset.mem_univ _, rfl⟩)
      refine Finset.mem_map.mpr ⟨⟨w, hs⟩, ?_, rfl⟩
      exact (B.completedStar.mem_neighborFinset _ _).mpr
        (Or.inl ((G.mem_neighborFinset _ _).mp ha))
    · split_ifs at hw with hA
      · have hw0 : w = B.label 0 := Finset.mem_singleton.mp hw
        subst w
        exact Finset.mem_map.mpr ⟨B.completedHub,
          (B.completedStar.mem_neighborFinset _ _).mpr
            ((B.completedHub_adj v).mpr hA).symm, rfl⟩
      · exact (Finset.notMem_empty _ hw).elim

/-- Exact parity-restoring degree accounting at every non-hub survivor. -/
theorem completedStar_degree_balance (v : B.StarSurvivor) (hv : v.val ≠ B.label 0) :
    B.completedStar.degree v + #(G.neighborFinset v.val ∩ B.vertices) =
      G.degree v.val + if v.val ∈ B.anchors then 1 else 0 := by
  have hd : Disjoint (G.neighborFinset v.val \ B.vertices)
      (if v.val ∈ B.anchors then {B.label 0} else ∅) := by
    apply Finset.disjoint_left.mpr
    intro w hw hw'
    split_ifs at hw' with hA
    · have hw0 := Finset.mem_singleton.mp hw'
      exact (Finset.mem_sdiff.mp hw).2 (hw0 ▸
        Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩)
    · exact Finset.notMem_empty _ hw'
  have h := congrArg Finset.card (B.completedStar_neighbors v hv)
  rw [Finset.card_map, Finset.card_union_of_disjoint hd] at h
  have hp := Finset.card_sdiff_add_card_inter (G.neighborFinset v.val) B.vertices
  have hs : #(if v.val ∈ B.anchors then {B.label 0} else ∅) =
      if v.val ∈ B.anchors then 1 else 0 := by split_ifs <;> simp
  rw [hs] at h
  rw [SimpleGraph.card_neighborFinset_eq_degree] at h hp
  omega

/-- Outside the anchor set no old bowtie incidence is lost. -/
theorem no_anchor_incidence (v : B.StarSurvivor) (hv : v.val ≠ B.label 0)
    (ha : v.val ∉ B.anchors) : G.neighborFinset v.val ∩ B.vertices = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  obtain ⟨he, hb⟩ := Finset.mem_inter.mp hw
  obtain ⟨i, _, rfl⟩ := Finset.mem_map.mp hb
  exact ha ((B.mem_anchors _).mpr ⟨i, (B.mem_row i _).mpr
    ⟨((G.mem_neighborFinset _ _).mp he).symm,
      fun h => hv (B.survivor_mem_vertices v h)⟩⟩)

/-- Under full syndrome and even anchor count, all survivor parities agree
with their original parities. This is not claimed for other syndromes. -/
theorem completedStar_even_iff (hcard : Even #B.anchors)
    (hfull : ∀ w ∈ B.anchors, Odd #(G.neighborFinset w ∩ B.vertices))
    (v : B.StarSurvivor) :
    Even (B.completedStar.degree v) ↔ Even (G.degree v.val) := by
  by_cases hv : v.val = B.label 0
  · have hhub : v = B.completedHub := Subtype.ext hv
    rw [hhub, B.completedHub_degree]
    exact iff_of_true hcard (B.even_degree_label 0)
  · have h := B.completedStar_degree_balance v hv
    by_cases ha : v.val ∈ B.anchors
    · have ho := hfull v.val ha
      rw [if_pos ha] at h
      simp only [Nat.even_iff]
      have ho' := Nat.odd_iff.mp ho
      omega
    · rw [if_neg ha, B.no_anchor_incidence v hv ha, Finset.card_empty] at h
      exact (congrArg Even (by simpa only [Nat.add_zero] using h)).to_iff

/-- All completed-hub neighbours stay odd, so the hub has E-degree zero. -/
theorem completedHub_eDegree (hcard : Even #B.anchors)
    (hfull : ∀ w ∈ B.anchors, Odd #(G.neighborFinset w ∩ B.vertices)) :
    eDegree B.completedStar B.completedHub = 0 := by
  apply Finset.card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro v hv
  obtain ⟨ha, he⟩ := (mem_evenNeighbors _ _).mp hv
  have hA := (B.completedHub_adj v).mp ha
  exact (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hA))
    ((B.completedStar_even_iff hcard hfull v).mp he)

/-- No retained even vertex other than the hub gains an even neighbour. -/
theorem completedStar_eDegree_le (hcard : Even #B.anchors)
    (hfull : ∀ w ∈ B.anchors, Odd #(G.neighborFinset w ∩ B.vertices))
    (v : B.StarSurvivor) (hv : v.val ≠ B.label 0) (he : Even (G.degree v.val)) :
    eDegree B.completedStar v ≤ eDegree G v.val := by
  have hs : (evenNeighbors B.completedStar v).map (Function.Embedding.subtype _) ⊆
      evenNeighbors G v.val := by
    intro w hw
    obtain ⟨q, hq, rfl⟩ := Finset.mem_map.mp hw
    obtain ⟨ha, hqEven⟩ := (mem_evenNeighbors _ _).mp hq
    apply (mem_evenNeighbors _ _).mpr
    refine ⟨?_, (B.completedStar_even_iff hcard hfull q).mp hqEven⟩
    rcases ha with ha | ha
    · exact ha
    · rcases ha with ⟨hx, _⟩ | ⟨_, hA⟩
      · exact (hv hx).elim
      · exact ((Nat.not_even_iff_odd.mpr (B.odd_degree_anchor hA)) he).elim
  have h := Finset.card_le_card hs
  simpa only [Finset.card_map, eDegree] using h

end Gallai.WholeBowtie
