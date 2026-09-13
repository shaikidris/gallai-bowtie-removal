/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CompletedStarWords

/-! # Original-graph carriers after releasing the completed star

Only hub-free old walks are mapped from the auxiliary: a completed spoke
need not be an edge of the original graph. The local connectors are already
walks in the original graph. Nil old pieces are allowed.
-/

namespace Gallai.WholeBowtie

universe u
variable {V : Type u} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- A surviving vertex in a hub-free walk is not the original hub. -/
theorem completed_support_ne_hub {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support)
    {v : B.StarSurvivor} (hv : v ∈ P.support) : v.val ≠ B.label 0 := by
  intro he
  have he' : v = B.completedHub := Subtype.ext he
  exact hx (he' ▸ hv)

/-- Map an old walk after all occurrences of the completed hub are removed. -/
def completedMapWalk {a b : B.StarSurvivor} (P : B.completedStar.Walk a b)
    (hx : B.completedHub ∉ P.support) : G.Walk a.val b.val := by
  match P with
  | .nil => exact .nil
  | @SimpleGraph.Walk.cons _ _ a b c hab P =>
    have hp : B.completedHub ∉ P.support := fun h =>
      hx (by simpa only [SimpleGraph.Walk.support_cons, List.mem_cons] using Or.inr h)
    exact .cons ((B.completedStar_adj_off_hub a b
      (B.completed_support_ne_hub (.cons hab P) hx
        (SimpleGraph.Walk.start_mem_support (.cons hab P)))
      (B.completed_support_ne_hub P hp P.start_mem_support)).mp hab)
      (completedMapWalk P hp)

theorem completedMapWalk_support {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support) :
    (B.completedMapWalk P hx).support = P.support.map Subtype.val := by
  induction P with
  | nil => rfl
  | cons hab P ih =>
    simp only [completedMapWalk, SimpleGraph.Walk.support_cons, List.map_cons, ih]

theorem completedMapWalk_edges {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support) :
    (B.completedMapWalk P hx).edges = P.edges.map (Sym2.map Subtype.val) := by
  induction P with
  | nil => rfl
  | cons hab P ih =>
    simp only [completedMapWalk, SimpleGraph.Walk.edges_cons, List.map_cons, ih, Sym2.map_mk]

theorem completedMapWalk_isPath {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support)
    (hp : P.IsPath) : (B.completedMapWalk P hx).IsPath := by
  apply SimpleGraph.Walk.IsPath.mk'
  rw [B.completedMapWalk_support]
  exact hp.support_nodup.map Subtype.val_injective

theorem completedMapWalk_nil_iff {a b : B.StarSurvivor}
    (P : B.completedStar.Walk a b) (hx : B.completedHub ∉ P.support) :
    (B.completedMapWalk P hx).Nil ↔ P.Nil := by
  cases P with
  | nil => exact ⟨fun _ => .nil, fun _ => .nil⟩
  | cons hab P => simp only [completedMapWalk, SimpleGraph.Walk.not_nil_cons]

/-- Carriers avoiding the hub keep all their original edges and endpoints. -/
def completedAvoidingPath (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∉ P.walk.support) : NonemptyPath G where
  start := P.start.val
  finish := P.finish.val
  walk := B.completedMapWalk P.walk hx
  isPath := B.completedMapWalk_isPath P.walk hx P.isPath
  nonempty := fun hn => P.nonempty ((B.completedMapWalk_nil_iff P.walk hx).mp hn)

theorem completedAvoidingPath_edges (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∉ P.walk.support) :
    (B.completedAvoidingPath P hx).walk.edges = P.walk.edges.map (Sym2.map Subtype.val) :=
  B.completedMapWalk_edges P.walk hx

theorem completedAvoidingPath_endpoint_contribution (P : NonemptyPath B.completedStar)
    (hx : B.completedHub ∉ P.walk.support) (w : B.StarSurvivor) :
    ((if (B.completedAvoidingPath P hx).start = w.val then 1 else 0) +
      (if (B.completedAvoidingPath P hx).finish = w.val then 1 else 0 : ℕ)) =
      ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0)) := by
  change ((if P.start.val = w.val then 1 else 0) +
    (if P.finish.val = w.val then 1 else 0 : ℕ)) = _
  simp only [Subtype.val_inj]

/-- Append an original-graph tail to a hub-free auxiliary prefix. -/
def completedTerminalCarrier {a b : B.StarSurvivor} {c : V}
    (L : B.completedStar.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hMne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0) : NonemptyPath G where
  start := a.val
  finish := c
  walk := (B.completedMapWalk L hx).append M
  isPath := by
    apply isPath_append_of_intersection _ _ (B.completedMapWalk_isPath L hx hL) hM
    intro w hw hwM
    rw [B.completedMapWalk_support] at hw
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hw
    exact (hm v hwM).resolve_right (B.completed_support_ne_hub L hx hv)
  nonempty := fun hn => hMne (SimpleGraph.Walk.nil_append_iff.mp hn).2

theorem completedTerminalCarrier_edges {a b : B.StarSurvivor} {c : V}
    (L : B.completedStar.Walk a b) (M : G.Walk b.val c)
    (hL : L.IsPath) (hM : M.IsPath) (hMne : ¬ M.Nil)
    (hx : B.completedHub ∉ L.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = B.label 0) :
    (B.completedTerminalCarrier L M hL hM hMne hx hm).walk.edges =
      L.edges.map (Sym2.map Subtype.val) ++ M.edges := by
  exact (SimpleGraph.Walk.edges_append _ _).trans
    (congrArg (· ++ M.edges) (B.completedMapWalk_edges L hx))

/-- Join the two released pieces of one carrier with an original-graph connector. -/
def completedThroughCarrier {a b c d : B.StarSurvivor}
    (L : B.completedStar.Walk a b) (R : B.completedStar.Walk c d)
    (M : G.Walk b.val c.val) (hL : L.IsPath) (hR : R.IsPath)
    (hM : M.IsPath) (hMne : ¬ M.Nil) (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0) : NonemptyPath G := by
  refine NonemptyPath.splice (B.completedMapWalk L hxL) M (B.completedMapWalk R hxR)
    (B.completedMapWalk_isPath L hxL hL) hM (B.completedMapWalk_isPath R hxR hR)
    hMne ?_ ?_ ?_
  · intro w hwL hwR
    rw [B.completedMapWalk_support] at hwL hwR
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hwL
    obtain ⟨v', hv', he⟩ := List.mem_map.mp hwR
    exact hLR hv ((Subtype.val_injective he) ▸ hv')
  · intro w hwL hwM
    rw [B.completedMapWalk_support] at hwL
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hwL
    rcases hm v hwM with h | h | h
    · exact h
    · exact False.elim (hLR ((Subtype.val_injective h) ▸ hv) R.start_mem_support)
    · exact False.elim (B.completed_support_ne_hub L hxL hv h)
  · intro w hwM hwR
    rw [B.completedMapWalk_support] at hwR
    obtain ⟨v, hv, rfl⟩ := List.mem_map.mp hwR
    rcases hm v hwM with h | h | h
    · exact False.elim (hLR L.end_mem_support ((Subtype.val_injective h) ▸ hv))
    · exact h
    · exact False.elim (B.completed_support_ne_hub R hxR hv h)

theorem completedThroughCarrier_edges {a b c d : B.StarSurvivor}
    (L : B.completedStar.Walk a b) (R : B.completedStar.Walk c d)
    (M : G.Walk b.val c.val) (hL : L.IsPath) (hR : R.IsPath)
    (hM : M.IsPath) (hMne : ¬ M.Nil) (hLR : L.support.Disjoint R.support)
    (hxL : B.completedHub ∉ L.support) (hxR : B.completedHub ∉ R.support)
    (hm : ∀ v : B.StarSurvivor, v.val ∈ M.support →
      v.val = b.val ∨ v.val = c.val ∨ v.val = B.label 0) :
    (B.completedThroughCarrier L R M hL hR hM hMne hLR hxL hxR hm).walk.edges =
      (L.edges.map (Sym2.map Subtype.val) ++ M.edges) ++
        R.edges.map (Sym2.map Subtype.val) := by
  change (((B.completedMapWalk L hxL).append M).append
    (B.completedMapWalk R hxR)).edges = _
  rw [SimpleGraph.Walk.edges_append, SimpleGraph.Walk.edges_append,
    B.completedMapWalk_edges, B.completedMapWalk_edges]

end Gallai.WholeBowtie
