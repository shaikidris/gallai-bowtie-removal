/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.ThreeAnchorZeroTransport

/-! # Automatic endpoint supply for ordinary zero-syndrome records -/
namespace Gallai.WholeBowtie
open Certificate Certificate.ThreeAnchor
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Empty syndrome keeps the used anchor odd in the puncture. Hence ordinary
restoration needs no caller-supplied endpoint reserve and preserves every even
survivor's reserve. -/
theorem zeroThree_reconstruction_of_parity
    (A : Fin 3 ↪ {v : V // v ∉ B.vertices}) (s : State)
    (hrows : ∀ i v, v ∈ B.row i ↔
      ∃ j, (rowMask (s i)).val.testBit j.val = true ∧ (A j).val = v)
    (a : Fin 3) (tail : List Vertex) (added : List (List Vertex))
    (h : ZeroTwoAccepted s a tail added) (D : Decomposition B.puncture) :
    ∃ E : Decomposition G, E.size = D.size + added.length ∧
      E.size ≤ D.size + 2 ∧ ∀ w : {v // v ∉ B.vertices}, Even (G.degree w.val) →
        D.endpointCount w ≤ E.endpointCount w.val := by
  obtain ⟨i, hi⟩ := h.2.1
  have ha : (A a).val ∈ B.anchors := B.row_subset_anchors i
    ((hrows i _).mpr ⟨a, hi, rfl⟩)
  have hodd := B.odd_degree_anchor ha
  have hn : (A a).val ∉ B.syndrome := by
    intro hm
    have hh := (B.threeAnchor_mem_syndrome A s hrows a).mpr hm
    simp [h.1] at hh
  have haux : Odd (B.puncture.degree (A a)) :=
    Nat.not_even_iff_odd.mp (fun he => hn ((B.anchor_even_puncture_iff (A a) ha).mp he))
  obtain ⟨E, hsize, hbound, hends⟩ := B.zeroThree_reconstruction A s hrows a tail added h D
    (D.endpointCount_pos_of_odd_degree (A a) haux)
  refine ⟨E, hsize, hbound, ?_⟩
  intro w hw
  apply hends w
  intro he
  subst w
  exact (Nat.not_even_iff_odd.mpr hodd) hw

end Gallai.WholeBowtie
