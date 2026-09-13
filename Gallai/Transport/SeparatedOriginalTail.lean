/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.ThreeAnchorSeparation
import Gallai.Transport.OriginalPairExtension

/-! # Original carriers may receive tails through other separated anchors -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)
variable (p q : {v : V // v ∉ B.vertices}) (hpq : G.Adj p.val q.val)
variable (hs : B.syndrome = {p.val, q.val}) (hc : G.Connected)
variable (hA : B.anchors.card ≤ 3)
variable (hC : Fintype.card (B.pairRepairedPuncture p q).ConnectedComponent = 3)

include hs hc hA hC in
/-- The only anchor on a carrier ending at an anchor is that ending anchor. -/
theorem originalCarrier_anchor_eq_finish
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (ha : P.finish.val ∈ B.anchors)
    (v : V) (hv : v ∈ (B.originalPairCarrier p q hpq P).walk.support)
    (hvA : v ∈ B.anchors) : v = P.finish.val := by
  classical
  change v ∈ (P.walk.map (B.originalPairHom p q hpq)).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, hu, rfl⟩ := List.mem_map.mp hv
  have he := B.pairRepaired_reachable_anchors_eq p q hs hc hA hC u P.finish
    hvA ha (P.walk.dropUntil u hu).reachable
  exact congrArg Subtype.val he

/-- Separation permits arbitrary anchor visits inside the new tail, not only
fresh core vertices; each original carrier still intersects it only at the join. -/
def separatedOriginalExtension
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (ha : P.finish.val ∈ B.anchors)
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v ∈ B.vertices ∨ v ∈ B.anchors) : NonemptyPath G :=
  (B.originalPairCarrier p q hpq P).append T hj (by
    intro v hv ht
    rcases hf v ht with hB | hanchor
    · exact (B.originalPairCarrier_outside p q hpq P v hv hB).elim
    · exact B.originalCarrier_anchor_eq_finish p q hpq hs hc hA hC P ha v hv hanchor)

/-- The separated extension has exactly the concatenated old and tail edges. -/
theorem separatedOriginalExtension_edges
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (ha : P.finish.val ∈ B.anchors)
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v ∈ B.vertices ∨ v ∈ B.anchors) :
    (B.separatedOriginalExtension p q hpq hs hc hA hC P ha T hj hf).walk.edges =
      P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  change ((P.walk.map (B.originalPairHom p q hpq)).append
    (T.walk.copy hj.symm rfl)).edges = _
  rw [SimpleGraph.Walk.edges_append]
  exact congrArg₂ List.append (SimpleGraph.Walk.edges_map (B.originalPairHom p q hpq) P.walk)
    (SimpleGraph.Walk.edges_copy T.walk hj.symm rfl)

/-- Every even retained vertex preserves its endpoint contribution through a
separated tail: all possible tail endpoints are core vertices or odd anchors. -/
theorem separatedOriginalExtension_even_endpoints
    (P : NonemptyPath (B.pairRepairedPuncture p q)) (ha : P.finish.val ∈ B.anchors)
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v ∈ B.vertices ∨ v ∈ B.anchors)
    (w : {v // v ∉ B.vertices}) (hw : Even (G.degree w.val)) :
    ((if (B.separatedOriginalExtension p q hpq hs hc hA hC P ha T hj hf).start = w.val
      then 1 else 0) +
      (if (B.separatedOriginalExtension p q hpq hs hc hA hC P ha T hj hf).finish = w.val
      then 1 else 0)) =
    ((if P.start.val = w.val then 1 else 0) +
      (if P.finish.val = w.val then 1 else 0) : ℕ) := by
  have hnot : w.val ∉ B.anchors := fun h =>
    (Nat.not_even_iff_odd.mpr (B.odd_degree_anchor h)) hw
  have hpw : P.finish.val ≠ w.val := fun he => hnot (he ▸ ha)
  have htw : T.finish ≠ w.val := by
    intro he
    rcases hf T.finish T.walk.end_mem_support with hB | hanchor
    · exact w.property (he ▸ hB)
    · exact hnot (he ▸ hanchor)
  change ((if P.start.val = w.val then 1 else 0) +
    (if T.finish = w.val then 1 else 0)) = _
  simp only [if_neg htw, if_neg hpw]

end Gallai.WholeBowtie
