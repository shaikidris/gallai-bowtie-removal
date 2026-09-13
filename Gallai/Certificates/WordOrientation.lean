/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.WordRelabel

/-! # Reorienting and reordering certificate words

Reversal preserves unordered edge occurrences and endpoint counts. Roles
are checked separately: terminal tails cannot in general be reversed while
retaining their attachment. The consumer is canonical-interface normalization.
-/

namespace Gallai.Certificate

variable {V : Type*}

private theorem wordEdges_snoc (word : List V) (v : V) :
    wordEdges (word ++ [v]) = wordEdges word ++
      (match word.getLast? with | none => [] | some u => [s(u, v)]) := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    cases rest with
    | nil => rfl
    | cons b rest => simpa [wordEdges] using congrArg (List.cons s(a, b)) ih

/-- Reversing a word reverses its unordered edge-occurrence list exactly. -/
theorem wordEdges_reverse (word : List V) :
    wordEdges word.reverse = (wordEdges word).reverse := by
  induction word with
  | nil => rfl
  | cons a rest ih =>
    rw [List.reverse_cons, wordEdges_snoc, List.getLast?_reverse, ih]
    cases rest with
    | nil => rfl
    | cons b rest => simp [wordEdges, Sym2.eq_swap]

/-- Pointwise reversals preserve all edge occurrences as a multiset. -/
theorem familyEdges_reorient {old new : List (List V)}
    (h : List.Forall₂ (fun a b => b = a ∨ b = a.reverse) old new) :
    (familyEdges new : Multiset (Sym2 V)) = (familyEdges old : Multiset (Sym2 V)) := by
  induction h with
  | nil => rfl
  | @cons a b old new hab _ ih =>
    have he : (wordEdges b : Multiset (Sym2 V)) = (wordEdges a : Multiset (Sym2 V)) := by
      rcases hab with rfl | rfl
      · rfl
      · simp only [wordEdges_reverse, Multiset.coe_reverse]
    change (wordEdges b : Multiset (Sym2 V)) + familyEdges new =
      (wordEdges a : Multiset (Sym2 V)) + familyEdges old
    rw [he, ih]

/-- Reversal does not change the endpoint vector of a word family. -/
theorem endpoints_reorient [DecidableEq V] {old new : List (List V)}
    (h : List.Forall₂ (fun a b => b = a ∨ b = a.reverse) old new) (v : V) :
    endpoints new v = endpoints old v := by
  induction h with
  | nil => rfl
  | cons hab _ ih =>
    rcases hab with rfl | rfl
    · simpa only [endpoints, List.map_cons, List.sum_cons] using
        congrArg (fun n => _ + n) ih
    · simp only [endpoints, List.map_cons, List.sum_cons, List.head?_reverse,
        List.getLast?_reverse] at *
      omega

/-- Arbitrary pointwise reversals preserve the exact accepted edge partition. -/
theorem Accepted.reorient {edges : Finset (Sym2 V)} {old new : List (List V)}
    (h : Accepted edges old)
    (hr : List.Forall₂ (fun a b => b = a ∨ b = a.reverse) old new) :
    Accepted edges new := by
  refine ⟨?_, (familyEdges_reorient hr).trans h.2⟩
  have hs := h.1
  clear h
  induction hr with
  | nil => simp
  | @cons a b old new hab _ ih =>
    intro word hw
    rcases List.mem_cons.mp hw with rfl | hw
    · have ha := hs a (by simp)
      rcases hab with rfl | rfl
      · exact ha
      · simpa only [List.length_reverse, List.nodup_reverse] using ha
    · exact ih (fun w hw => hs w (List.mem_cons_of_mem _ hw)) word hw

/-- Reordering word occurrences preserves the exact accepted partition. -/
theorem Accepted.perm {edges : Finset (Sym2 V)} {old new : List (List V)}
    (h : Accepted edges old) (hp : old.Perm new) : Accepted edges new := by
  refine ⟨fun w hw => h.1 w (hp.mem_iff.mpr hw), ?_⟩
  have he : (familyEdges old : Multiset (Sym2 V)) = familyEdges new :=
    Quot.sound (hp.flatMap_right wordEdges)
  exact he.symm.trans h.2

/-- Reordering occurrences does not change any endpoint multiplicity. -/
theorem endpoints_perm [DecidableEq V] {old new : List (List V)}
    (hp : old.Perm new) (v : V) : endpoints old v = endpoints new v := by
  exact (hp.map _).sum_eq

/-- Reoriented and reordered replacements retain the full record whenever
their new ordered roles have been verified. Added paths are left untouched. -/
theorem RecordAccepted.normalize [DecidableEq V]
    {edges : Finset (Sym2 V)} {roles roles' : List (List V × Finset V)}
    {old oriented new added : List (List V)} {budget : ℕ}
    {marked : Finset V} {required : V → ℕ}
    (h : RecordAccepted edges roles old added budget marked required)
    (hr : List.Forall₂ (fun a b => b = a ∨ b = a.reverse) old oriented)
    (hp : oriented.Perm new)
    (hc : List.Forall₂ (fun role word => Compatible role.1 role.2 word) roles' new) :
    RecordAccepted edges roles' new added budget marked required := by
  have ha : List.Forall₂ (fun a b : List V => b = a ∨ b = a.reverse) added added :=
    List.forall₂_same.mpr (fun _ _ => Or.inl rfl)
  have hr' := List.rel_append hr ha
  have hp' := hp.append_right added
  refine ⟨(h.1.reorient hr').perm hp', hc, h.2.2.1, ?_⟩
  intro v hv
  rw [← endpoints_perm hp', endpoints_reorient hr']
  exact h.2.2.2 v hv

/-- Choosing orientations of two-entry boundaries induces legal word orientations. -/
theorem compatible_orient_boundaries {allowed : Finset V} {bs words : List (List V)}
    (h : List.Forall₂ (fun b w => Compatible b allowed w) bs words)
    (f : List V → List V)
    (hf : ∀ b, f b = b ∨ (b.length = 2 ∧ f b = b.reverse)) :
    ∃ ws, List.Forall₂ (fun a b => b = a ∨ b = a.reverse) words ws ∧
      List.Forall₂ (fun b w => Compatible b allowed w) (bs.map f) ws := by
  induction h with
  | nil => exact ⟨[], .nil, .nil⟩
  | @cons b w bs words hb _ ih =>
    obtain ⟨ws, hr, hc⟩ := ih
    rcases hf b with he | ⟨hl, he⟩
    · exact ⟨w :: ws, .cons (Or.inl rfl) hr, .cons (he.symm ▸ hb) hc⟩
    · obtain ⟨a, c, rfl⟩ := List.length_eq_two.mp hl
      refine ⟨w.reverse :: ws, .cons (Or.inr rfl) hr, .cons ?_ hc⟩
      simpa only [he, List.reverse_cons, List.reverse_nil, List.nil_append,
        List.cons_append] using hb.reverse_pair

/-- Boundary normalization and a finite role permutation suffice to normalize
an arbitrary accepted record; no new carrier compatibility is assumed. -/
theorem RecordAccepted.normalize_boundaries [DecidableEq V]
    {edges : Finset (Sym2 V)} {bs target : List (List V)} {allowed : Finset V}
    {old added : List (List V)} {budget : ℕ} {marked : Finset V} {required : V → ℕ}
    (h : RecordAccepted edges (bs.map (fun b => (b, allowed)))
      old added budget marked required)
    (f : List V → List V)
    (hf : ∀ b, f b = b ∨ (b.length = 2 ∧ f b = b.reverse))
    (hp : (bs.map f).Perm target) :
    ∃ new, RecordAccepted edges (target.map (fun b => (b, allowed)))
      new added budget marked required := by
  have hc := List.forall₂_map_left_iff.mp h.2.1
  obtain ⟨ws, hr, hw⟩ := compatible_orient_boundaries hc f hf
  obtain ⟨new, hn, hperm⟩ := List.perm_comp_forall₂ hp.symm hw
  exact ⟨new, h.normalize hr hperm.symm (List.forall₂_map_left_iff.mpr hn)⟩

end Gallai.Certificate
