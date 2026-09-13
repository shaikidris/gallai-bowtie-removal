/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.PairRepairedPuncture

/-! # Independently selected syndrome pairs define the same repaired graph -/

namespace Gallai.WholeBowtie

variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Ordering choices in certificate selectors do not change the auxiliary. -/
theorem pairRepaired_eq_of_pair_eq (p q r t : {v : V // v ∉ B.vertices})
    (he : ({p.val,q.val} : Finset V) = {r.val,t.val}) :
    B.pairRepairedPuncture p q = B.pairRepairedPuncture r t := by
  have hset : ({p.val,q.val} : Set V) = {r.val,t.val} := by
    simpa using congrArg (fun s : Finset V => (s : Set V)) he
  rcases Set.pair_eq_pair_iff.mp hset with ⟨hp, hq⟩ | ⟨hp, hq⟩
  · have hp' : p = r := Subtype.ext hp
    have hq' : q = t := Subtype.ext hq
    subst p q
    rfl
  · have hp' : p = t := Subtype.ext hp
    have hq' : q = r := Subtype.ext hq
    subst p q
    exact toggleEdge_comm B.puncture t r

end Gallai.WholeBowtie
