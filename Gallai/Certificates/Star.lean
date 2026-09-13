/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Mathlib.Data.Sym.Sym2
import Mathlib.Data.List.Perm.Basic

/-!
# The three finite star-release identities

The alphabet is the released hub, four private vertices and four anchors.
These kernel-checked identities record exact edge multiplicity, simplicity,
attachment avoidance and endpoint changes. They do not themselves transport
arbitrary old carriers or assert the all-order star expansion theorem.
-/

namespace Gallai.Star

/-- The nine distinct local vertices in a full-incidence star expansion. -/
inductive Vertex
  /-- Released old hub. -/
  | x
  /-- First private vertex. -/
  | a
  /-- Second private vertex. -/
  | b
  /-- Third private vertex. -/
  | c
  /-- Fourth private vertex. -/
  | d
  /-- First old anchor. -/
  | p
  /-- Second old anchor. -/
  | q
  /-- Third old anchor. -/
  | r
  /-- Fourth old anchor. -/
  | s
  deriving DecidableEq

open Vertex

/-- Vertices available after all old occurrences of the hub are released. -/
def fresh : List Vertex := [x, a, b, c, d]

/-- The four retained old anchors. -/
def anchors : List Vertex := [p, q, r, s]

/-- Unordered edges in a word, retaining multiplicities. -/
def wordEdges (word : List Vertex) : List (Sym2 Vertex) :=
  List.zipWith (fun u v => s(u, v)) word word.tail

/-- Edge multilist of a family of words. -/
def familyEdges (words : List (List Vertex)) : List (Sym2 Vertex) := words.flatMap wordEdges

/-- The 26 active edges, including the four released old spokes. -/
def activeEdges : List (Sym2 Vertex) :=
  [s(x, a), s(x, b), s(x, c), s(x, d), s(a, b), s(c, d)] ++
    fresh.flatMap (fun u => anchors.map (fun v => s(u, v)))

/-- The old star edges, before release. -/
def spokes : List (Sym2 Vertex) := anchors.map (fun u => s(x, u))

/-- Endpoint incidences of a word family. -/
def endpoints (words : List (List Vertex)) (v : Vertex) : ℕ :=
  (words.map (fun word => (if word.head? = some v then 1 else 0) +
    (if word.getLast? = some v then 1 else 0))).sum

/-- A replacement avoids every old anchor other than its prescribed attachments. -/
def compatible (old replacement : List Vertex) : Prop :=
  replacement.head? = old.head? ∧
    if old.length = 2 then (∀ v ∈ replacement.tail, v ∈ fresh)
    else replacement.getLast? = old.getLast? ∧
      ∀ v ∈ replacement.tail.dropLast, v ∈ fresh

/-- Complete local acceptance contract; no ambient-carrier lifting is assumed. -/
def Valid (old replacements added : List (List Vertex)) (outputAtHub : ℕ) : Prop :=
  replacements.length = old.length ∧ added.length = 2 ∧
  (∀ word ∈ replacements ++ added, 2 ≤ word.length ∧ word.Nodup) ∧
  List.Forall₂ compatible old replacements ∧
  (familyEdges old).Perm spokes ∧
  (familyEdges (replacements ++ added)).Perm activeEdges ∧
  (∀ v ∈ anchors, endpoints (replacements ++ added) v = endpoints old v) ∧
  endpoints (replacements ++ added) x = outputAtHub

/-- Two through runs, with no endpoint at the old hub. -/
def oldZero : List (List Vertex) := [[p, x, q], [r, x, s]]
/-- Replacement connectors for two through runs. -/
def replaceZero : List (List Vertex) := [[p, a, b, x, c, d, q], [r, a, x, d, s]]
/-- Two additional paths for the zero-endpoint interface. -/
def addZero : List (List Vertex) := [[a, q, x, p, b, s, c, r, d], [a, s, x, r, b, q, c, p, d]]

/-- Two terminal runs and one through run. -/
def oldTwo : List (List Vertex) := [[p, x], [q, x], [r, x, s]]
/-- Replacements for the two-endpoint interface. -/
def replaceTwo : List (List Vertex) := [[p, a, b, x, c, d], [q, a, x, d], [r, x, s]]
/-- Two additional paths for the two-endpoint interface. -/
def addTwo : List (List Vertex) := [[x, p, b, q, c, r, d, s, a], [x, q, d, p, c, s, b, r, a]]

/-- Four terminal runs. -/
def oldFour : List (List Vertex) := [[p, x], [q, x], [r, x], [s, x]]
/-- Fresh tails after all four terminal spokes are released. -/
def replaceFour : List (List Vertex) := [[p, a, b, x, c], [q, b], [r, c, d, x, a], [s, d]]
/-- Two additional paths for the four-endpoint interface. -/
def addFour : List (List Vertex) := [[d, p, c, s, b, r, x, q, a], [c, q, d, r, a, s, x, p, b]]

/-- Every active edge is listed once, and the active graph has 26 edges. -/
theorem activeEdges_exact : activeEdges.Nodup ∧ activeEdges.length = 26 := by decide

/-- The zero-endpoint identity has the exact local reconstruction contract. -/
theorem zero_valid : Valid oldZero replaceZero addZero 0 := by
  unfold Valid compatible
  decide

/-- The two-endpoint identity has the exact local reconstruction contract. -/
theorem two_valid : Valid oldTwo replaceTwo addTwo 2 := by
  unfold Valid compatible
  decide

/-- The four-endpoint identity removes all endpoint occurrences at the hub. -/
theorem four_valid : Valid oldFour replaceFour addFour 0 := by
  unfold Valid compatible
  decide

/-- The input labels really are the three claimed endpoint profiles. -/
theorem input_profiles : endpoints oldZero x = 0 ∧ endpoints oldTwo x = 2 ∧
    endpoints oldFour x = 4 := by decide

/-- A compatible terminal tail contains no old anchor except its attachment. -/
theorem compatible_terminal_support (u : Vertex) (replacement : List Vertex)
    (h : compatible [u, x] replacement) (w : Vertex) (hw : w ∈ replacement) :
    w = u ∨ w ∈ fresh := by
  have hh : replacement.head? = some u := h.1
  have ht : ∀ v ∈ replacement.tail, v ∈ fresh := by simpa using h.2
  cases replacement with
  | nil => simp at hw
  | cons hd rest =>
    have ha : hd = u := Option.some.inj hh
    subst hd
    rcases List.mem_cons.mp hw with he | he
    · exact Or.inl he
    · exact Or.inr (ht w he)

/-- A compatible through connector contains no old anchors except its two attachments. -/
theorem compatible_through_support (u v : Vertex) (replacement : List Vertex)
    (h : compatible [u, x, v] replacement) (w : Vertex) (hw : w ∈ replacement) :
    w = u ∨ w = v ∨ w ∈ fresh := by
  have hh : replacement.head? = some u := h.1
  have ht : replacement.getLast? = some v ∧
      ∀ w' ∈ replacement.tail.dropLast, w' ∈ fresh := by simpa using h.2
  cases replacement with
  | nil => simp at hw
  | cons hd rest =>
    have ha : hd = u := Option.some.inj hh
    subst hd
    rcases List.mem_cons.mp hw with he | he
    · exact Or.inl he
    · have hne : rest ≠ [] := List.ne_nil_of_mem he
      have hlast : rest.getLast hne = v := by
        have hl := ht.1
        rw [List.getLast?_cons_of_ne_nil hne, List.getLast?_eq_some_getLast hne] at hl
        exact Option.some.inj hl
      rw [← List.dropLast_concat_getLast hne, List.mem_append, List.mem_singleton] at he
      rcases he with he | he
      · exact Or.inr (Or.inr (ht.2 w he))
      · exact Or.inr (Or.inl (he.trans hlast))

end Gallai.Star
