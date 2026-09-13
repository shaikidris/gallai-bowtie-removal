/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.LowActivity
import Gallai.Structure.DominatedDeletion

/-! # Actual auxiliaries obtained by deleting inactive bowtie vertices

Connectivity is derived from the original connected graph and empty deleted
rows. Exact vertex and degree accounting are independent of the anchor count.
-/

namespace Gallai.WholeBowtie

open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Induced auxiliary after deleting exactly the specified bowtie labels. -/
abbrev privateDeletion (I : Finset (Fin 5)) :
    SimpleGraph {v : V // v ∉ I.map B.label} :=
  G.induce {v | v ∉ I.map B.label}

/-- Any set of inactive private vertices may be deleted while the hub survives. -/
theorem privateDeletion_connected (I : Finset (Fin 5)) (h0 : 0 ∉ I)
    (hi : ∀ i ∈ I, B.row i = ∅) (hc : G.Connected) :
    (B.privateDeletion I).Connected := by
  apply connected_induce_of_deleted_dominated G _ (B.label 0)
  · simpa using h0
  · exact hc
  · intro u hu v _ huv
    have hu' : u ∈ I.map B.label := by simpa using hu
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_map.mp hu'
    have hvB : v ∈ B.vertices := by
      by_contra hout
      have hr := (B.mem_row i v).mpr ⟨huv, hout⟩
      simp only [hi i hiI, Finset.notMem_empty] at hr
    obtain ⟨j, _, rfl⟩ := Finset.mem_map.mp hvB
    by_cases hj : j = 0
    · exact Or.inl (congrArg B.label hj)
    · exact Or.inr ((B.adj_iff 0 j).mpr
        ((by decide : ∀ j : Fin 5, j ≠ 0 → bowtieGraph.Adj 0 j) j hj))

/-- Deleting distinct labels removes exactly their number of original vertices. -/
theorem privateDeletion_card (I : Finset (Fin 5)) :
    Fintype.card {v : V // v ∉ I.map B.label} + #I = Fintype.card V := by
  have hs : #(I.map B.label) ≤ Fintype.card V := Finset.card_le_univ _
  simp only [Finset.card_map] at hs
  simp only [Fintype.card_subtype_compl, Fintype.card_coe, Finset.card_map]
  omega

/-- Exact incident-edge loss for every retained vertex of a partial deletion. -/
theorem privateDeletion_degree_add_deleted (I : Finset (Fin 5))
    (v : {v : V // v ∉ I.map B.label}) :
    (B.privateDeletion I).degree v + #(G.neighborFinset v.val ∩ I.map B.label) =
      G.degree v.val := by
  have hmap := congrArg Finset.card
    (G.map_neighborFinset_induce (s := {v | v ∉ I.map B.label}) v)
  have hset : G.neighborFinset v.val ∩ ({v | v ∉ I.map B.label} : Set V).toFinset =
      G.neighborFinset v.val \ I.map B.label := by
    ext w
    simp
  rw [hset] at hmap
  have hdegree : (B.privateDeletion I).degree v =
      #(G.neighborFinset v.val \ I.map B.label) := by simpa using hmap
  rw [hdegree]
  simp

/-- No vertex outside the bowtie loses an edge when the deleted rows are empty. -/
theorem privateDeletion_degree_outside (I : Finset (Fin 5))
    (hi : ∀ i ∈ I, B.row i = ∅)
    (v : {v : V // v ∉ I.map B.label}) (hv : v.val ∉ B.vertices) :
    (B.privateDeletion I).degree v = G.degree v.val := by
  have hz : G.neighborFinset v.val ∩ I.map B.label = ∅ := by
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro w hw
    obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hw
    obtain ⟨i, hiI, rfl⟩ := Finset.mem_map.mp hm
    have hr := (B.mem_row i v.val).mpr
      ⟨((G.mem_neighborFinset _ _).mp ha).symm, hv⟩
    simp only [hi i hiI, Finset.notMem_empty] at hr
  have h := B.privateDeletion_degree_add_deleted I v
  simpa only [hz, Finset.card_empty, Nat.add_zero] using h

/-- Deleted incidences at a labelled survivor are counted entirely in the fixed bowtie. -/
theorem privateDeletion_label_degree (I : Finset (Fin 5)) (j : Fin 5) (hj : j ∉ I) :
    (B.privateDeletion I).degree ⟨B.label j, by simpa using hj⟩ +
      #(bowtieGraph.neighborFinset j ∩ I) = G.degree (B.label j) := by
  have hset : G.neighborFinset (B.label j) ∩ I.map B.label =
      (bowtieGraph.neighborFinset j ∩ I).map B.label := by
    ext w
    constructor
    · intro hw
      obtain ⟨ha, hm⟩ := Finset.mem_inter.mp hw
      obtain ⟨i, hiI, rfl⟩ := Finset.mem_map.mp hm
      exact Finset.mem_map.mpr ⟨i, Finset.mem_inter.mpr
        ⟨(bowtieGraph.mem_neighborFinset j i).mpr
          ((B.adj_iff j i).mp ((G.mem_neighborFinset _ _).mp ha)), hiI⟩, rfl⟩
    · intro hw
      obtain ⟨i, hi, rfl⟩ := Finset.mem_map.mp hw
      obtain ⟨ha, hiI⟩ := Finset.mem_inter.mp hi
      exact Finset.mem_inter.mpr
        ⟨(G.mem_neighborFinset _ _).mpr ((B.adj_iff j i).mpr
          ((bowtieGraph.mem_neighborFinset _ _).mp ha)), Finset.mem_map.mpr ⟨i, hiI, rfl⟩⟩
  have h := B.privateDeletion_degree_add_deleted I ⟨B.label j, by simpa using hj⟩
  simpa only [hset, Finset.card_map] using h

end Gallai.WholeBowtie
