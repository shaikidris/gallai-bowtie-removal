/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.RunSlots
import Gallai.Certificates.Star

/-!
# The actual full-incidence star expansion

Old vertices are retained, four private vertices are added, and no old edge
is changed. This graph is defined without choosing a decomposition. The
decomposition is used only to label its four old neighbours compatibly with
the three checked local identities.
-/

namespace Gallai.Star

universe u

variable {V : Type u}

/-- The two disjoint private edges, indexed by the pairs (0,1) and (2,3). -/
def privateAdj (i j : Fin 4) : Prop := i.val / 2 = j.val / 2 ∧ i ≠ j

/-- Add the full-incidence bowtie to a hub, leaving every old edge unchanged. -/
def expansion (H : SimpleGraph V) (x : V) : SimpleGraph (V ⊕ Fin 4) where
  Adj
    | .inl v, .inl w => H.Adj v w
    | .inl v, .inr _ => v = x ∨ H.Adj x v
    | .inr _, .inl w => w = x ∨ H.Adj x w
    | .inr i, .inr j => privateAdj i j
  symm := by
    constructor
    intro v w h
    cases v <;> cases w
    · exact H.adj_symm h
    · exact h
    · exact h
    · exact ⟨h.1.symm, h.2.symm⟩
  loopless := by
    constructor
    intro v
    cases v with
    | inl v => exact H.irrefl
    | inr i => exact fun h => h.2 rfl

instance (H : SimpleGraph V) (x : V) [DecidableEq V] [DecidableRel H.Adj] :
    DecidableRel (expansion H x).Adj := by
  intro v w
  cases v <;> cases w <;> dsimp [expansion, privateAdj] <;> infer_instance

/-- Every retained edge is present, and no new old-old edge is introduced. -/
@[simp] theorem expansion_old_adj (H : SimpleGraph V) (x v w : V) :
    (expansion H x).Adj (.inl v) (.inl w) ↔ H.Adj v w := Iff.rfl

/-- Private vertices see precisely the hub and its old neighbours. -/
@[simp] theorem expansion_mixed_adj (H : SimpleGraph V) (x v : V) (i : Fin 4) :
    (expansion H x).Adj (.inl v) (.inr i) ↔ v = x ∨ H.Adj x v := Iff.rfl

/-- The private-private edges are exactly the prescribed two pairs. -/
@[simp] theorem expansion_private_adj (H : SimpleGraph V) (x : V) (i j : Fin 4) :
    (expansion H x).Adj (.inr i) (.inr j) ↔ privateAdj i j := Iff.rfl

/-- The old graph embeds without changing any of its adjacency relations. -/
def oldHom (H : SimpleGraph V) (x : V) : H →g expansion H x where
  toFun := Sum.inl
  map_rel' h := h

/-- Old-vertex inclusion identifies no two vertices. -/
theorem oldHom_injective (H : SimpleGraph V) (x : V) :
    Function.Injective (oldHom H x) := Sum.inl_injective

/-- Interpret the nine local labels using a bijection onto the hub neighbours. -/
def label (H : SimpleGraph V) (x : V) (A : Fin 4 ≃ H.neighborSet x) :
    Vertex → V ⊕ Fin 4
  | .x => .inl x
  | .a => .inr 0
  | .b => .inr 1
  | .c => .inr 2
  | .d => .inr 3
  | .p => .inl (A 0).val
  | .q => .inl (A 1).val
  | .r => .inl (A 2).val
  | .s => .inl (A 3).val

/-- The hub is different from every old anchor. -/
theorem hub_ne_anchor (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (i : Fin 4) : x ≠ (A i).val := by
  exact (A i).property.ne

/-- The four anchor labels are distinct actual old vertices. -/
theorem anchors_injective (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) : Function.Injective (fun i => (A i).val) :=
  Subtype.val_injective.comp A.injective

/-- Nine symbolic local vertices remain distinct in the actual graph. -/
theorem label_injective (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) : Function.Injective (label H x A) := by
  have h0 := hub_ne_anchor H x A 0
  have h1 := hub_ne_anchor H x A 1
  have h2 := hub_ne_anchor H x A 2
  have h3 := hub_ne_anchor H x A 3
  have ha := anchors_injective H x A
  intro v w h
  cases v <;> cases w <;>
    simp_all only [label, Sum.inl.injEq, Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl]
  all_goals first | rfl | contradiction | exact False.elim (by omega) |
    exact False.elim (by have he := ha h; omega)

/-- Every edge of the checked local universe is present in the actual expansion. -/
theorem active_edge_mem (H : SimpleGraph V) (x : V)
    (A : Fin 4 ≃ H.neighborSet x) (e : Sym2 Vertex) (he : e ∈ activeEdges) :
    Sym2.map (label H x A) e ∈ (expansion H x).edgeSet := by
  have h0 : H.Adj x (A 0).val := (A 0).property
  have h1 : H.Adj x (A 1).val := (A 1).property
  have h2 : H.Adj x (A 2).val := (A 2).property
  have h3 : H.Adj x (A 3).val := (A 3).property
  simp only [activeEdges, fresh, anchors, List.flatMap_cons, List.flatMap_nil,
    List.map_cons, List.map_nil, List.cons_append, List.nil_append,
    List.mem_cons, List.not_mem_nil, or_false] at he
  rcases he with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl |
    rfl | rfl | rfl | rfl
  all_goals simp [label, expansion, privateAdj, h0, h1, h2, h3]

end Gallai.Star
