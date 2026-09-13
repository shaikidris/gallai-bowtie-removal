/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.CarrierSplice

/-! # Two compatible endpoint tails on one old carrier

The tails point outwards from the old endpoints. Only their post-attachment
vertices must avoid the old carrier and each other. Nil tails are allowed,
so the same operator handles zero, one, or two extended endpoints.
-/

namespace Gallai

variable {V : Type*} {G : SimpleGraph V}

/-- A walk support consists of its start followed by its post-start support. -/
theorem support_eq_start_or_tail {a b : V} (P : G.Walk a b) {v : V}
    (hv : v ∈ P.support) : v = a ∨ v ∈ P.support.tail := by
  rw [← P.cons_tail_support] at hv
  exact List.mem_cons.mp hv

namespace NonemptyPath

/-- Compatible outward tails have disjoint full supports: neither may return
to the old carrier, and the old endpoints are distinct. -/
theorem endpoint_tails_disjoint (P : NonemptyPath G) {a b : V}
    (L : G.Walk P.start a) (R : G.Walk P.finish b)
    (hL : L.support.tail.Disjoint P.walk.support)
    (hR : R.support.tail.Disjoint P.walk.support)
    (hLR : L.support.tail.Disjoint R.support.tail) :
    L.reverse.support.Disjoint R.support := by
  intro v hvL hvR
  rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvL
  rcases support_eq_start_or_tail L hvL with hs | ht
  · rcases support_eq_start_or_tail R hvR with hs' | ht'
    · exact P.start_ne_finish G (hs.symm.trans hs')
    · exact hR ht' (hs ▸ P.walk.start_mem_support)
  · rcases support_eq_start_or_tail R hvR with hs' | ht'
    · exact hL ht (hs' ▸ P.walk.end_mem_support)
    · exact hLR ht ht'

/-- Attach zero, one, or two compatible tails to an arbitrary old carrier. -/
def endpointTails (P : NonemptyPath G) {a b : V}
    (L : G.Walk P.start a) (R : G.Walk P.finish b)
    (hLp : L.IsPath) (hRp : R.IsPath)
    (hL : L.support.tail.Disjoint P.walk.support)
    (hR : R.support.tail.Disjoint P.walk.support)
    (hLR : L.support.tail.Disjoint R.support.tail) : NonemptyPath G :=
  NonemptyPath.splice L.reverse P.walk R hLp.reverse P.isPath hRp P.nonempty
    (P.endpoint_tails_disjoint L R hL hR hLR)
    (by
      intro v hvL hvP
      rw [SimpleGraph.Walk.support_reverse, List.mem_reverse] at hvL
      exact (support_eq_start_or_tail L hvL).elim id (fun ht => (hL ht hvP).elim))
    (by
      intro v hvP hvR
      exact (support_eq_start_or_tail R hvR).elim id (fun ht => (hR ht hvP).elim))

/-- Exact edge accounting, including both old-carrier and tail edges. -/
theorem endpointTails_edges (P : NonemptyPath G) {a b : V}
    (L : G.Walk P.start a) (R : G.Walk P.finish b)
    (hLp : L.IsPath) (hRp : R.IsPath)
    (hL : L.support.tail.Disjoint P.walk.support)
    (hR : R.support.tail.Disjoint P.walk.support)
    (hLR : L.support.tail.Disjoint R.support.tail) :
    (P.endpointTails L R hLp hRp hL hR hLR).walk.edges =
      (L.reverse.edges ++ P.walk.edges) ++ R.edges := by
  apply NonemptyPath.splice_edges

/-- Endpoints unaffected by the tail replacements keep their incidence count. -/
theorem endpointTails_endpoint_contribution [DecidableEq V]
    (P : NonemptyPath G) {a b : V}
    (L : G.Walk P.start a) (R : G.Walk P.finish b)
    (hLp : L.IsPath) (hRp : R.IsPath)
    (hL : L.support.tail.Disjoint P.walk.support)
    (hR : R.support.tail.Disjoint P.walk.support)
    (hLR : L.support.tail.Disjoint R.support.tail)
    (v : V) (ha : a = v ↔ P.start = v) (hb : b = v ↔ P.finish = v) :
    (if (P.endpointTails L R hLp hRp hL hR hLR).start = v then 1 else 0) +
      (if (P.endpointTails L R hLp hRp hL hR hLR).finish = v then 1 else 0) =
    (if P.start = v then 1 else 0) + (if P.finish = v then 1 else 0 : ℕ) := by
  change (if a = v then 1 else 0) + (if b = v then 1 else 0) = _
  simp only [ha, hb]

end NonemptyPath
end Gallai
