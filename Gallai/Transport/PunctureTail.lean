/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ZeroSyndromeTails
import Gallai.Operations.Concatenate

/-! # Component-safe extensions without an auxiliary repair edge -/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- The tail may enter deleted vertices or other puncture components, but
cannot revisit the old carrier except at its terminal attachment. -/
def punctureSeparatedTail (P : NonemptyPath B.puncture) (T : NonemptyPath G)
    (ht : P.finish.val = T.start)
    (hf : ∀ v : {v : V // v ∉ B.vertices}, v.val ∈ T.walk.support →
      v = P.finish ∨ ¬ B.puncture.Reachable P.finish v) : NonemptyPath G :=
  (B.punctureCarrier P).append T ht (by
    intro v hv hT
    rw [B.punctureCarrier_support] at hv
    obtain ⟨u,hu,rfl⟩ := List.mem_map.mp hv
    rcases hf u hT with he | hn
    · exact congrArg Subtype.val he
    · exact (hn ((P.walk.dropUntil u hu).reachable.symm)).elim)

theorem punctureSeparatedTail_edges (P : NonemptyPath B.puncture) (T : NonemptyPath G)
    (ht : P.finish.val = T.start)
    (hf : ∀ v : {v : V // v ∉ B.vertices}, v.val ∈ T.walk.support →
      v = P.finish ∨ ¬ B.puncture.Reachable P.finish v) :
    (B.punctureSeparatedTail P T ht hf).walk.edges =
      P.walk.edges.map (Sym2.map Subtype.val) ++ T.walk.edges := by
  unfold punctureSeparatedTail
  exact (NonemptyPath.append_edges _ _ _ _).trans
    (congrArg (fun es => es ++ T.walk.edges)
      (SimpleGraph.Walk.edges_map _ P.walk))

omit [DecidableEq V] in
/-- A core-only tail is automatically component-safe. -/
theorem puncture_core_tail_safe (P : NonemptyPath B.puncture) (T : NonemptyPath G)
    (ht : P.finish.val = T.start)
    (hf : ∀ v ∈ T.walk.support, v = T.start ∨ v ∈ B.vertices)
    (v : {v : V // v ∉ B.vertices}) (hv : v.val ∈ T.walk.support) :
    v = P.finish ∨ ¬ B.puncture.Reachable P.finish v := by
  rcases hf v.val hv with he | hm
  · exact Or.inl (Subtype.ext (he.trans ht.symm))
  · exact (v.property hm).elim

/-- Off-attachment endpoint reserves cannot decrease under the extension. -/
theorem punctureSeparatedTail_endpoint (P : NonemptyPath B.puncture) (T : NonemptyPath G)
    (ht : P.finish.val = T.start)
    (hf : ∀ v : {v : V // v ∉ B.vertices}, v.val ∈ T.walk.support →
      v = P.finish ∨ ¬ B.puncture.Reachable P.finish v)
    (w : {v : V // v ∉ B.vertices}) (hw : w ≠ P.finish) :
    ((if P.start = w then 1 else 0) + (if P.finish = w then 1 else 0) : ℕ) ≤
      (if (B.punctureSeparatedTail P T ht hf).start = w.val then 1 else 0) +
      (if (B.punctureSeparatedTail P T ht hf).finish = w.val then 1 else 0) := by
  change _ ≤ (if P.start.val = w.val then 1 else 0) + (if T.finish = w.val then 1 else 0)
  simp only [Subtype.val_inj,if_neg hw.symm,Nat.add_zero]
  exact Nat.le_add_right _ _

end Gallai.WholeBowtie
