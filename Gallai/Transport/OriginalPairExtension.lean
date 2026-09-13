/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.OriginalPairCarriers
import Gallai.Operations.Concatenate

/-! # Fresh endpoint extensions of original-repair carriers -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Old carrier support is disjoint from every deleted bowtie vertex. -/
theorem originalPairCarrier_outside (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (P : NonemptyPath (B.pairRepairedPuncture p q))
    (v : V) (hv : v ∈ (B.originalPairCarrier p q hpq P).walk.support) :
    v ∉ B.vertices := by
  change v ∈ (P.walk.map (B.originalPairHom p q hpq)).support at hv
  rw [SimpleGraph.Walk.support_map] at hv
  obtain ⟨u, _, rfl⟩ := List.mem_map.mp hv
  exact u.property

/-- A core-only tail joins the selected terminal carrier without a new path. -/
def originalPairExtension (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (P : NonemptyPath (B.pairRepairedPuncture p q))
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) : NonemptyPath G :=
  (B.originalPairCarrier p q hpq P).append T hj (by
    intro v hv ht
    rcases hf v ht with hs | hB
    · exact hs.trans hj.symm
    · exact (B.originalPairCarrier_outside p q hpq P v hv hB).elim)

/-- Extension adds exactly the tail edges, in order. -/
theorem originalPairExtension_edges (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (P : NonemptyPath (B.pairRepairedPuncture p q))
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices) :
    (B.originalPairExtension p q hpq P T hj hf).walk.edges =
      P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  change ((P.walk.map (B.originalPairHom p q hpq)).append
    (T.walk.copy hj.symm rfl)).edges = _
  rw [SimpleGraph.Walk.edges_append]
  exact congrArg₂ List.append (SimpleGraph.Walk.edges_map (B.originalPairHom p q hpq) P.walk)
    (SimpleGraph.Walk.edges_copy T.walk hj.symm rfl)

/-- Every retained vertex except the spent attachment keeps its endpoint contribution. -/
theorem originalPairExtension_endpoints (p q : {v : V // v ∉ B.vertices})
    (hpq : G.Adj p.val q.val) (P : NonemptyPath (B.pairRepairedPuncture p q))
    (T : NonemptyPath G) (hj : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    (w : {v : V // v ∉ B.vertices}) (hw : w.val ≠ T.start) :
    ((if (B.originalPairExtension p q hpq P T hj hf).start = w.val then 1 else 0) +
      (if (B.originalPairExtension p q hpq P T hj hf).finish = w.val then 1 else 0)) =
    ((if P.start.val = w.val then 1 else 0) +
      (if P.finish.val = w.val then 1 else 0) : ℕ) := by
  have ht : T.finish ∈ B.vertices :=
    (hf T.finish T.walk.end_mem_support).resolve_left T.start_ne_finish.symm
  have htw : T.finish ≠ w.val := fun h => w.property (h ▸ ht)
  have hpw : P.finish.val ≠ w.val := fun h => hw (h.symm.trans hj)
  change ((if P.start.val = w.val then 1 else 0) + (if T.finish = w.val then 1 else 0)) = _
  simp only [if_neg htw, if_neg hpw]

end Gallai.WholeBowtie
