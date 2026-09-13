/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Structure.Bowtie
import Mathlib.Tactic.FinCases

/-! # Constructing a whole bowtie from its shape and even-neighbour closure

Reduction consumers must prove that all five labels remain even and no even
neighbour leaves their range. Ordinary-degree preservation alone is not enough.
-/
namespace Gallai.WholeBowtie
variable {V : Type*} [Fintype V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- An embedded bowtie is a whole even component when closed under even neighbours. -/
noncomputable def ofClosedEmbedding (l : Fin 5 ↪ V)
    (he : ∀ i, Even (H.degree (l i)))
    (ha : ∀ i j, H.Adj (l i) (l j) ↔ bowtieGraph.Adj i j)
    (hc : ∀ i v, H.Adj (l i) v → Even (H.degree v) → v ∈ Set.range l) :
    WholeBowtie H := by
  let e : Fin 5 → evenVertices H := fun i => ⟨l i, he i⟩
  let K := (evenSubgraph H).connectedComponentMk (e 0)
  have closed : ∀ {u v : evenVertices H}, (evenSubgraph H).Walk u v →
      u.val ∈ Set.range l → v.val ∈ Set.range l := by
    intro u v p
    induction p with
    | nil => exact id
    | @cons u v w huv p ih =>
      rintro ⟨i, hi⟩
      apply ih
      apply hc i v.val
      · change H.Adj u.val v.val at huv
        simpa only [hi] using huv
      · exact v.property
  have hin (i : Fin 5) : e i ∈ K.supp := by
    have hr : (evenSubgraph H).Reachable (e 0) (e i) := by
      by_cases hi : i = 0
      · subst i; exact SimpleGraph.Reachable.refl _
      · have hadj : bowtieGraph.Adj 0 i := by
          fin_cases i <;> first | contradiction | decide
        exact (show (evenSubgraph H).Adj (e 0) (e i) from (ha 0 i).mpr hadj).reachable
    exact SimpleGraph.ConnectedComponent.sound hr.symm
  refine { label := l, component := K, adj_iff := ha, component_vertices := ?_ }
  ext v
  constructor
  · rintro ⟨w, hw, rfl⟩
    have hr := K.reachable_of_mem_supp (hin 0) hw
    obtain ⟨p⟩ := hr
    exact closed p ⟨0, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, hin i, rfl⟩

end Gallai.WholeBowtie
