/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarRestore
import Gallai.Certificates.CompletedStarRecord
import Gallai.Expansion.Edges

/-! # Assigning a sparse accepted record to every actual completed-star run

The record is in the carrier-selected anchor coordinates. Its role contract
supplies the word compatibility, while the input decomposition supplies the
attachment equalities. Neither is a free ambient-splicing premise.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
open scoped Finset
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (D : Decomposition B.completedStar) (hfour : #B.anchors = 4)
variable {replacements added : List (List Star.Vertex)}
variable (h : AcceptedRecord (B.completedStarState (B.carrierAnchorOrder D hfour))
  (profileInterface (Star.profileOf D B.completedHub)) replacements added)

private theorem completedThroughHyp {W : Type*} [DecidableEq W] {J : SimpleGraph W}
    (E : Decomposition J) (x : W) (i : E.ThroughIndex x) :
    x ∈ (E.path i.val).walk.support ∧
      (E.path i.val).start ≠ x ∧ (E.path i.val).finish ≠ x :=
  (Finset.mem_filter.mp i.property).2

/-- The actual owner selects one replacement occurrence of the accepted word list. -/
noncomputable def completedAssignedIndex
    (i : D.TerminalIndex B.completedHub ⊕ D.ThroughIndex B.completedHub) :
    Fin (replacements ++ added).length := h.wordIndex (B.completedCarrierRoleEquiv D hfour i)

theorem completedAssignedIndex_injective : Function.Injective (B.completedAssignedIndex D hfour h) :=
  h.wordIndex_injective.comp (B.completedCarrierRoleEquiv D hfour).injective

theorem completedAssigned_terminal_compatible (i : D.TerminalIndex B.completedHub) :
    Certificate.Compatible
      [anchor ((Star.profileOf D B.completedHub).terminalAnchor
        (Star.terminalNumber D B.completedHub (B.completedHub_degree.trans hfour) i))]
      Star.fresh.toFinset (replacements ++ added)[B.completedAssignedIndex D hfour h (.inl i)] := by
  have hc := h.wordIndex_compatible (B.completedCarrierRoleEquiv D hfour (.inl i))
  simpa only [B.completedCarrierRoleEquiv_terminal, terminalRole_boundary,
    completedAssignedIndex] using hc

theorem completedAssigned_through_compatible (i : D.ThroughIndex B.completedHub) :
    Certificate.Compatible
      [anchor ((Star.profileOf D B.completedHub).throughAnchor
        (Star.throughNumber D B.completedHub (B.completedHub_degree.trans hfour) i) 0),
       anchor ((Star.profileOf D B.completedHub).throughAnchor
        (Star.throughNumber D B.completedHub (B.completedHub_degree.trans hfour) i) 1)]
      Star.fresh.toFinset (replacements ++ added)[B.completedAssignedIndex D hfour h (.inr i)] := by
  have hc := h.wordIndex_compatible (B.completedCarrierRoleEquiv D hfour (.inr i))
  simpa only [B.completedCarrierRoleEquiv_through, throughRole_boundary,
    completedAssignedIndex] using hc

/-- Restore each terminal from the single supplied record, with no word choice premise. -/
noncomputable def completedAssignedTerminal (i : D.TerminalIndex B.completedHub) : NonemptyPath G :=
  B.completedRestoreTerminal (D.path i.val) (Finset.mem_filter.mp i.property).2
    (B.carrierAnchorOrder D hfour) (replacements ++ added) h.1
    (B.completedAssignedIndex D hfour h (.inl i))
    ((Star.profileOf D B.completedHub).terminalAnchor
      (Star.terminalNumber D B.completedHub (B.completedHub_degree.trans hfour) i))
    (by simpa only [Decomposition.runNeighbor] using B.carrierAnchorOrder_terminal D hfour i)
    (B.completedAssigned_terminal_compatible D hfour h i)

/-- Restore each through carrier without separating its two role attachments. -/
noncomputable def completedAssignedThrough (i : D.ThroughIndex B.completedHub) : NonemptyPath G := by
  have hi := completedThroughHyp D B.completedHub i
  let n := Star.throughNumber D B.completedHub (B.completedHub_degree.trans hfour) i
  exact B.completedRestoreThrough (D.path i.val) hi.1 hi.2.1 hi.2.2.symm
    (B.carrierAnchorOrder D hfour) (replacements ++ added) h.1
    (B.completedAssignedIndex D hfour h (.inr i))
    ((Star.profileOf D B.completedHub).throughAnchor n 0)
    ((Star.profileOf D B.completedHub).throughAnchor n 1)
    (B.carrierAnchorOrder_through D hfour i 0) (B.carrierAnchorOrder_through D hfour i 1)
    (B.completedAssigned_through_compatible D hfour h i)

/-- The terminal's old contribution is exactly its original nonspoke multiset. -/
theorem completedAssignedTerminal_edge_partition (i : D.TerminalIndex B.completedHub) :
    (B.completedAssignedTerminal D hfour h i).walk.edges.Perm
      (((D.path i.val).walk.edges.filter (fun e => decide (B.completedHub ∉ e))).map
        (Sym2.map Subtype.val) ++
      (Certificate.wordEdges (replacements ++ added)[B.completedAssignedIndex D hfour h (.inl i)]).map
        (Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour)))) := by
  unfold completedAssignedTerminal
  erw [B.completedRestoreTerminal_edges]
  exact ((Star.terminal_nonspoke_edges (D.path i.val) B.completedHub
    (Finset.mem_filter.mp i.property).2).symm.map _).append_right _

/-- The through carrier contributes its retained edges and exactly its assigned word. -/
theorem completedAssignedThrough_edge_partition (i : D.ThroughIndex B.completedHub) :
    (B.completedAssignedThrough D hfour h i).walk.edges.Perm
      (((D.path i.val).walk.edges.filter (fun e => decide (B.completedHub ∉ e))).map
        (Sym2.map Subtype.val) ++
      (Certificate.wordEdges (replacements ++ added)[B.completedAssignedIndex D hfour h (.inr i)]).map
        (Sym2.map (B.completedLabel (B.carrierAnchorOrder D hfour)))) := by
  have hi := completedThroughHyp D B.completedHub i
  unfold completedAssignedThrough
  erw [B.completedRestoreThrough_edges]
  rw [
    Star.through_nonspoke_edges _ B.completedHub hi.1 hi.2.1 hi.2.2.symm,
    List.map_append, List.append_assoc, List.append_assoc]
  exact List.perm_append_comm.append_left _

theorem completedAssignedTerminal_endpoint_contribution (i : D.TerminalIndex B.completedHub)
    (w : B.StarSurvivor) (hw : w.val ∉ B.vertices) :
    ((if (B.completedAssignedTerminal D hfour h i).start = w.val then 1 else 0) +
      (if (B.completedAssignedTerminal D hfour h i).finish = w.val then 1 else 0 : ℕ)) =
      ((if (D.path i.val).start = w then 1 else 0) +
        (if (D.path i.val).finish = w then 1 else 0)) := by
  unfold completedAssignedTerminal
  exact B.completedRestoreTerminal_endpoint_contribution _ _ _ _ _ _ _ _ _ w hw

theorem completedAssignedThrough_endpoint_contribution (i : D.ThroughIndex B.completedHub)
    (w : B.StarSurvivor) :
    ((if (B.completedAssignedThrough D hfour h i).start = w.val then 1 else 0) +
      (if (B.completedAssignedThrough D hfour h i).finish = w.val then 1 else 0 : ℕ)) =
      ((if (D.path i.val).start = w then 1 else 0) +
        (if (D.path i.val).finish = w then 1 else 0)) := by
  unfold completedAssignedThrough
  exact B.completedRestoreThrough_endpoint_contribution _ _ _ _ _ _ _ _ _ _ _ _ _ w

end Gallai.WholeBowtie
