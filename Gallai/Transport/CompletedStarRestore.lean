/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarCarrier

/-! # Splicing accepted sparse words into actual completed-star carriers

These operations release the hub themselves. They derive all old-piece
disjointness from the original simple carrier and all connector avoidance
from the checked word. Word selection and global family accounting remain
separate obligations.
-/

namespace Gallai.WholeBowtie

open Certificate.CompletedStar
universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

theorem realizeCompletedWord_start (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (v : Star.Vertex) (hv : words[i].head? = some v) :
    (B.realizeCompletedWord A words h i).start = B.completedLabel A v := by
  change B.completedLabel A (words[i].head _) = B.completedLabel A v
  apply congrArg (B.completedLabel A)
  exact Option.some.inj ((List.head?_eq_some_head _).symm.trans hv)

theorem realizeCompletedWord_finish (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (v : Star.Vertex) (hv : words[i].getLast? = some v) :
    (B.realizeCompletedWord A words h i).finish = B.completedLabel A v := by
  change B.completedLabel A (words[i].getLast _) = B.completedLabel A v
  apply congrArg (B.completedLabel A)
  exact Option.some.inj ((List.getLast?_eq_some_getLast _).symm.trans hv)

/-- A nonempty terminal word ends at a local vertex, not its old attachment. -/
theorem realizeCompletedWord_terminal_finish_mem (A : B.AnchorNumbering)
    (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i]) :
    (B.realizeCompletedWord A words h i).finish ∈ B.vertices := by
  let M := B.realizeCompletedWord A words h i
  have hmem := M.walk.end_mem_support
  rw [B.realizeCompletedWord_support] at hmem
  obtain ⟨v, hv, he⟩ := List.mem_map.mp hmem
  rcases Certificate.compatible_single_support hr hv with rfl | hf
  · exact False.elim (M.start_ne_finish _
      ((B.realizeCompletedWord_start A words h i _ hr.1).trans he))
  · exact he ▸ B.completedLabel_fresh A v hf

/-- Replace a genuine through run by its accepted original-edge connector. -/
noncomputable def completedRestoreThrough (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j k : Fin 4)
    (hj : (A j).val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val)
    (hk : (A k).val = (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hr : Certificate.Compatible [anchor j, anchor k] Star.fresh.toFinset words[i]) :
    NonemptyPath G := by
  let M := B.realizeCompletedWord A words h i
  have hstart : M.start = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val :=
    (B.realizeCompletedWord_start A words h i _ hr.1).trans
      ((B.completedLabel_anchor A j).trans hj)
  have hfinish : M.finish = (P.dropFrom B.completedHub hx ht).walk.snd.val :=
    (B.realizeCompletedWord_finish A words h i _ hr.2.1).trans
      ((B.completedLabel_anchor A k).trans hk)
  exact B.completedThroughCarrier (P.releaseLeft B.completedHub hx hs)
    (P.releaseRight B.completedHub hx ht) (M.walk.copy hstart hfinish)
    (P.releaseLeft_isPath B.completedHub hx hs) (P.releaseRight_isPath B.completedHub hx ht)
    ((M.walk.isPath_copy hstart hfinish).mpr M.isPath)
    (SimpleGraph.Walk.not_nil_of_ne (fun he =>
      M.start_ne_finish _ (hstart.trans (he.trans hfinish.symm))))
    (P.release_supports_disjoint B.completedHub hx hs ht)
    (P.hub_notMem_releaseLeft B.completedHub hx hs)
    (P.hub_notMem_releaseRight B.completedHub hx ht)
    (by
      intro v hv
      have hv' : v.val ∈ M.walk.support := by
        simpa only [SimpleGraph.Walk.support_copy] using hv
      simpa only [hj, hk] using B.realizeCompletedWord_through_old A words h i j k hr v hv')

/-- A through replacement preserves both original outside endpoints. -/
theorem completedRestoreThrough_endpoints (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j k : Fin 4)
    (hj : (A j).val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val)
    (hk : (A k).val = (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hr : Certificate.Compatible [anchor j, anchor k] Star.fresh.toFinset words[i]) :
    (B.completedRestoreThrough P hx hs ht A words h i j k hj hk hr).start = P.start.val ∧
      (B.completedRestoreThrough P hx hs ht A words h i j k hj hk hr).finish = P.finish.val :=
  ⟨rfl, rfl⟩

theorem completedRestoreThrough_edges (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j k : Fin 4)
    (hj : (A j).val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val)
    (hk : (A k).val = (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hr : Certificate.Compatible [anchor j, anchor k] Star.fresh.toFinset words[i]) :
    (B.completedRestoreThrough P hx hs ht A words h i j k hj hk hr).walk.edges =
      ((P.releaseLeft B.completedHub hx hs).edges.map (Sym2.map Subtype.val) ++
        (Certificate.wordEdges words[i]).map (Sym2.map (B.completedLabel A))) ++
          (P.releaseRight B.completedHub hx ht).edges.map (Sym2.map Subtype.val) := by
  unfold completedRestoreThrough
  rw [B.completedThroughCarrier_edges, SimpleGraph.Walk.edges_copy,
    B.realizeCompletedWord_edges]

/-- Replace a terminal spoke after orienting and trimming its actual carrier. -/
noncomputable def completedRestoreTerminal (P : NonemptyPath B.completedStar)
    (hx : P.start = B.completedHub ∨ P.finish = B.completedHub)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hj : (A j).val = (P.toward B.completedHub).walk.reverse.snd.val)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i]) : NonemptyPath G := by
  let Q := P.toward B.completedHub
  let M := B.realizeCompletedWord A words h i
  have hstart : M.start = Q.walk.reverse.snd.val :=
    (B.realizeCompletedWord_start A words h i _ hr.1).trans
      ((B.completedLabel_anchor A j).trans hj)
  have hfinish : Q.finish = B.completedHub := P.toward_finish B.completedHub hx
  have hhub : B.completedHub ∉ Q.walk.reverse.tail.reverse.support :=
    hfinish ▸ Star.released_terminal_hub_absent Q
  exact B.completedTerminalCarrier Q.walk.reverse.tail.reverse (M.walk.copy hstart rfl)
    Q.isPath.reverse.tail.reverse ((M.walk.isPath_copy hstart rfl).mpr M.isPath)
    (SimpleGraph.Walk.not_nil_of_ne (fun he => M.start_ne_finish _ (hstart.trans he))) hhub
    (by
      intro v hv
      have hv' : v.val ∈ M.walk.support := by
        simpa only [SimpleGraph.Walk.support_copy] using hv
      simpa only [hj] using B.realizeCompletedWord_terminal_old A words h i j hr v hv')

/-- Terminal replacement keeps the outside endpoint and the word's final vertex. -/
theorem completedRestoreTerminal_endpoints (P : NonemptyPath B.completedStar)
    (hx : P.start = B.completedHub ∨ P.finish = B.completedHub)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hj : (A j).val = (P.toward B.completedHub).walk.reverse.snd.val)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i]) :
    (B.completedRestoreTerminal P hx A words h i j hj hr).start =
        (P.toward B.completedHub).start.val ∧
      (B.completedRestoreTerminal P hx A words h i j hj hr).finish =
        (B.realizeCompletedWord A words h i).finish := ⟨rfl, rfl⟩

theorem completedRestoreTerminal_edges (P : NonemptyPath B.completedStar)
    (hx : P.start = B.completedHub ∨ P.finish = B.completedHub)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hj : (A j).val = (P.toward B.completedHub).walk.reverse.snd.val)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i]) :
    (B.completedRestoreTerminal P hx A words h i j hj hr).walk.edges =
      ((P.toward B.completedHub).walk.reverse.tail.reverse.edges.map
        (Sym2.map Subtype.val)) ++
          (Certificate.wordEdges words[i]).map (Sym2.map (B.completedLabel A)) := by
  unfold completedRestoreTerminal
  rw [B.completedTerminalCarrier_edges, SimpleGraph.Walk.edges_copy,
    B.realizeCompletedWord_edges]

/-- Every surviving endpoint outside the bowtie is preserved by terminal restoration. -/
theorem completedRestoreTerminal_endpoint_contribution (P : NonemptyPath B.completedStar)
    (hx : P.start = B.completedHub ∨ P.finish = B.completedHub)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j : Fin 4)
    (hj : (A j).val = (P.toward B.completedHub).walk.reverse.snd.val)
    (hr : Certificate.Compatible [anchor j] Star.fresh.toFinset words[i])
    (w : B.StarSurvivor) (hw : w.val ∉ B.vertices) :
    ((if (B.completedRestoreTerminal P hx A words h i j hj hr).start = w.val then 1 else 0) +
      (if (B.completedRestoreTerminal P hx A words h i j hj hr).finish = w.val then 1 else 0 : ℕ)) =
      ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) := by
  have hnew : (B.realizeCompletedWord A words h i).finish ≠ w.val := by
    intro he
    exact hw (he ▸ B.realizeCompletedWord_terminal_finish_mem A words h i j hr)
  have hhub : B.completedHub ≠ w := by
    intro he
    apply hw
    rw [← he]
    exact Finset.mem_map.mpr ⟨0, Finset.mem_univ _, rfl⟩
  have hfinish : (P.toward B.completedHub).finish ≠ w := by
    rw [P.toward_finish B.completedHub hx]
    exact hhub
  have he := P.toward_endpoint_contribution B.completedHub w
  change ((if (P.toward B.completedHub).start.val = w.val then 1 else 0) +
    (if (B.realizeCompletedWord A words h i).finish = w.val then 1 else 0 : ℕ)) = _
  simpa only [Subtype.val_inj, if_neg hnew, if_neg hfinish] using he

/-- Through restoration preserves the endpoint contribution at every old vertex. -/
theorem completedRestoreThrough_endpoint_contribution (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∈ P.walk.support)
    (hs : P.start ≠ B.completedHub) (ht : B.completedHub ≠ P.finish)
    (A : B.AnchorNumbering) (words : List (List Star.Vertex))
    (h : Certificate.Accepted (targetEdges (B.completedStarState A)) words)
    (i : Fin words.length) (j k : Fin 4)
    (hj : (A j).val = (P.takeTo B.completedHub hx hs).walk.reverse.snd.val)
    (hk : (A k).val = (P.dropFrom B.completedHub hx ht).walk.snd.val)
    (hr : Certificate.Compatible [anchor j, anchor k] Star.fresh.toFinset words[i])
    (w : B.StarSurvivor) :
    ((if (B.completedRestoreThrough P hx hs ht A words h i j k hj hk hr).start = w.val
        then 1 else 0) +
      (if (B.completedRestoreThrough P hx hs ht A words h i j k hj hk hr).finish = w.val
        then 1 else 0 : ℕ)) =
      ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) := by
  change ((if P.start.val = w.val then 1 else 0) +
    (if P.finish.val = w.val then 1 else 0 : ℕ)) = _
  simp only [Subtype.val_inj]

end Gallai.WholeBowtie
