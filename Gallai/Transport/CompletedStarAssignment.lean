/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Inputs.CompletedStarBudget
import Gallai.Certificates.CompletedStarRoles
import Gallai.Expansion.Assignment

/-! # Actual completed-star carrier assignment

Anchor coordinates are selected by the input decomposition. The original
incidence masks are then encoded in those same coordinates. Terminal and
through role attachments are proved equal to the actual released attachments.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Carrier slots, rather than a favourable-labelling premise, number anchors. -/
noncomputable def carrierAnchorOrder (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) : B.AnchorNumbering :=
  (D.fourNeighborEquiv B.completedHub (B.completedHub_degree.trans hfour)).trans
    B.completedNeighborEquiv

/-- Numbered original anchor equals the underlying auxiliary neighbour. -/
theorem carrierAnchorOrder_val (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (j : Fin 4) :
    (B.carrierAnchorOrder D hfour j).val =
      (D.fourNeighborEquiv B.completedHub (B.completedHub_degree.trans hfour) j).val.val := rfl

/-- Terminal coordinates agree with the actual terminal carrier's attachment. -/
theorem carrierAnchorOrder_terminal (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.TerminalIndex B.completedHub) :
    (B.carrierAnchorOrder D hfour
      ((Star.profileOf D B.completedHub).terminalAnchor
        (Star.terminalNumber D B.completedHub (B.completedHub_degree.trans hfour) i))).val =
      (D.runNeighbor B.completedHub (.inl i)).val := by
  rw [B.carrierAnchorOrder_val]
  have h := D.fourNeighborEquiv_terminal B.completedHub (B.completedHub_degree.trans hfour)
    (D.terminalIndexEquivFin B.completedHub i)
  simp only [Equiv.symm_apply_apply] at h
  exact congrArg Subtype.val h

/-- Through coordinates retain the ownership and orientation of both sides. -/
theorem carrierAnchorOrder_through (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.ThroughIndex B.completedHub) (b : Fin 2) :
    (B.carrierAnchorOrder D hfour
      ((Star.profileOf D B.completedHub).throughAnchor
        (Star.throughNumber D B.completedHub (B.completedHub_degree.trans hfour) i) b)).val =
      (D.runNeighbor B.completedHub (.inr (i, finTwoEquiv b))).val := by
  have h := Star.through_attachment D B.completedHub (B.completedHub_degree.trans hfour) i b
  rw [Star.label_anchor] at h
  exact congrArg Subtype.val (Sum.inl_injective h)

/-- Actual old carrier indices biject with the certificate's ordered roles. -/
noncomputable def completedCarrierRoleEquiv (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) :
    D.TerminalIndex B.completedHub ⊕ D.ThroughIndex B.completedHub ≃
      Fin (boundaries (profileInterface (Star.profileOf D B.completedHub))).length :=
  (Equiv.sumCongr
    ((D.terminalIndexEquivFin B.completedHub).trans
      (finCongr (Star.profileOf_counts D B.completedHub (B.completedHub_degree.trans hfour)).1))
    ((D.throughIndexEquivFin B.completedHub).trans
      (finCongr (Star.profileOf_counts D B.completedHub (B.completedHub_degree.trans hfour)).2))).trans
    (roleEquiv (Star.profileOf D B.completedHub))

/-- The owner-to-role equivalence preserves each terminal's numbered position. -/
theorem completedCarrierRoleEquiv_terminal (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.TerminalIndex B.completedHub) :
    B.completedCarrierRoleEquiv D hfour (.inl i) =
      terminalRole (Star.profileOf D B.completedHub)
        (Star.terminalNumber D B.completedHub (B.completedHub_degree.trans hfour) i) := by
  apply Fin.ext
  rfl

/-- The owner-to-role equivalence preserves each through carrier as one role. -/
theorem completedCarrierRoleEquiv_through (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : D.ThroughIndex B.completedHub) :
    B.completedCarrierRoleEquiv D hfour (.inr i) =
      throughRole (Star.profileOf D B.completedHub)
        (Star.throughNumber D B.completedHub (B.completedHub_degree.trans hfour) i) := by
  apply Fin.ext
  rfl

/-- This assignment preserves original graph adjacency in every row bit. -/
theorem carrier_state_bit (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (i : Fin 5) (j : Fin 4) :
    (B.completedStarState (B.carrierAnchorOrder D hfour) i).val.testBit j.val = true ↔
      G.Adj (B.label i) (B.carrierAnchorOrder D hfour j).val :=
  B.completedStarState_bit _ i j

/-- Carrier-selected coordinates preserve full original syndrome, not just
evenness of each row. -/
theorem carrier_state_column_odd (D : Decomposition B.completedStar)
    (hfour : #B.anchors = 4) (hfull : B.syndrome = B.anchors) (j : Fin 4) :
    Odd #{i : Fin 5 |
      (B.completedStarState (B.carrierAnchorOrder D hfour) i).val.testBit j.val = true} := by
  let A := B.carrierAnchorOrder D hfour
  have ho := (B.mem_syndrome_iff_odd_column (A j).val).mp
    (by rw [hfull]; exact (A j).property)
  have hs : (Finset.univ.filter fun i : Fin 5 =>
      (B.completedStarState A i).val.testBit j.val = true) =
      Finset.univ.filter (fun i : Fin 5 => (A j).val ∈ B.row i) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and,
      B.completedStarState_bit, B.mem_row, B.numberedAnchor_not_mem A j, not_false_eq_true,
      and_true]
  change Odd (Finset.card (Finset.univ.filter _))
  rw [hs]
  exact ho

end Gallai.WholeBowtie
