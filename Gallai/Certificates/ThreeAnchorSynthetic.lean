/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.WordFamily
import Mathlib.Data.Fin.VecNotation

/-! # Three-anchor whole-deletion synthetic records

The eight symbols are x,a,b,c,d,p,q,r. Row values 0,1,2,3 denote the
empty set, pq, pr, qr. This schema does not assert orbit coverage.
-/

namespace Gallai.Certificate.ThreeAnchor

abbrev Vertex := Fin 8
abbrev State := Fin 5 → Fin 4

/-- Anchor symbols follow the five core symbols. -/
def anchor (j : Fin 3) : Vertex := ⟨5 + j.val, by omega⟩

/-- The three pair masks and the empty mask. -/
def rowMask (c : Fin 4) : Fin 8 := ![0, 3, 5, 6] c

/-- The original bowtie edges and actual row incidences. -/
def targetEdges (s : State) : Finset (Sym2 Vertex) :=
  {s(0, 1), s(0, 2), s(1, 2), s(0, 3), s(0, 4), s(3, 4)} ∪
    (Finset.univ.filter (fun ij : Fin 5 × Fin 3 =>
      (rowMask (s ij.1)).val.testBit ij.2.val)).image
      (fun ij => s(ij.1.castAdd 3, anchor ij.2))

/-- Anchor incidence parity of the whole-deletion rows. -/
def syndrome (s : State) : Finset (Fin 3) :=
  Finset.univ.filter fun j => Odd ((Finset.univ.filter fun i : Fin 5 =>
    (rowMask (s i)).val.testBit j.val).card)

/-- Literal finite contract: correct pair, simple fresh connector, exact cover,
and at most two new paths. The unused third label need not occur in any word. -/
def SyntheticAccepted (s : State) (p q : Fin 3)
    (connector : List Vertex) (added : List (List Vertex)) : Prop :=
  syndrome s = {p, q} ∧ p ≠ q ∧
    connector.head? = some (anchor p) ∧ connector.getLast? = some (anchor q) ∧
    (∀ v ∈ connector, v = anchor p ∨ v = anchor q ∨ v.val < 5) ∧
    Accepted (targetEdges s) (connector :: added) ∧ added.length ≤ 2

instance (s : State) (p q : Fin 3) (connector : List Vertex)
    (added : List (List Vertex)) : Decidable (SyntheticAccepted s p q connector added) := by
  unfold SyntheticAccepted
  infer_instance

/-- Extract the exact connector-plus-new-path count consumed by global transport. -/
theorem SyntheticAccepted.edge_count {s : State} {p q : Fin 3}
    {connector : List Vertex} {added : List (List Vertex)}
    (h : SyntheticAccepted s p q connector added) (e : Sym2 Vertex) :
    (wordEdges connector).count e +
      (∑ j : Fin added.length, (wordEdges added[j]).count e) =
      if e ∈ targetEdges s then 1 else 0 := by
  have hc := h.2.2.2.2.2.1.edge_count e
  simpa [Fin.sum_univ_succ] using hc

end Gallai.Certificate.ThreeAnchor
