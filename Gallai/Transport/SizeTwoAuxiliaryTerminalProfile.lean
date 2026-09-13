/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoNormalizedTerminal
import Gallai.Transport.SizeTwoTerminalFamily

/-! # Terminal profiles supplied by the actual syndrome auxiliary -/
namespace Gallai.WholeBowtie
open Certificate Certificate.SizeTwo
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {G : SimpleGraph V} [DecidableRel G.Adj] (B : WholeBowtie G)

/-- Normalize the actual auxiliary decomposition while preserving its whole
endpoint vector and path budget. All profile premises of terminal-family
reconstruction, including literal p/q attachment order, are then supplied. -/
theorem sizeTwo_auxiliary_terminal_profile (A : B.AnchorNumbering)
    (hsyndrome : B.syndrome = {(A 0).val,(A 1).val})
    (D : Decomposition B.syndromeStar) (he : D.endpointCount B.completedHub = 2)
    (hr : 0 < D.endpointCount (B.sizeTwoRemoteMarks A 0))
    (hs : 0 < D.endpointCount (B.sizeTwoRemoteMarks A 1)) :
    ∃ E : Decomposition B.syndromeStar, E.size = D.size ∧
      (∀ v, E.endpointCount v = D.endpointCount v) ∧
      ∃ f : Fin 4 → Fin E.size, ∃ i : Fin 13,
        through i = false ∧
        (∀ r : Fin 2,
          (E.path (f (remoteRole i r))).start = B.sizeTwoRemoteMarks A r ∨
          (E.path (f (remoteRole i r))).finish = B.sizeTwoRemoteMarks A r) ∧
        (∀ j k, f j = f k ↔ owner i j = owner i k) ∧
        (E.path (f 0)).finish = B.completedHub ∧
        (E.path (f 0)).walk.reverse.snd.val = B.completedLabel A Star.Vertex.p ∧
        (E.path (f 1)).finish = B.completedHub ∧
        (E.path (f 1)).walk.reverse.snd.val = B.completedLabel A Star.Vertex.q ∧
        ∀ k, k ≠ f 0 → k ≠ f 1 → B.completedHub ∉ (E.path k).walk.support := by
  let p : B.StarSurvivor := B.completedOutside (A 0).val (B.numberedAnchor_not_mem A 0)
  let q : B.StarSurvivor := B.completedOutside (A 1).val (B.numberedAnchor_not_mem A 1)
  have hpq : p ≠ q := by
    intro h
    have hv : (A 0).val = (A 1).val := congrArg (fun v : B.StarSurvivor => v.val) h
    have ha : A 0 = A 1 := Subtype.ext hv
    have hh := A.injective ha
    exact (by decide : (0 : Fin 4) ≠ 1) hh
  have hcard : B.syndrome.card = 2 := by
    rw [hsyndrome,Finset.card_pair]
    intro h
    exact hpq (Subtype.ext h)
  have hp : B.syndromeStar.Adj B.completedHub p := by
    apply (B.syndromeStar_hub_adj p).mpr
    simp [hsyndrome,p,completedOutside]
  have hq : B.syndromeStar.Adj B.completedHub q := by
    apply (B.syndromeStar_hub_adj q).mpr
    simp [hsyndrome,q,completedOutside]
  have hxr : ∀ r : Fin 2, B.completedHub ≠ B.sizeTwoRemoteMarks A r := by
    intro r h
    exact B.label_ne_numberedAnchor A 0 ⟨r.val + 2,by omega⟩ (congrArg Subtype.val h)
  have hrs : B.sizeTwoRemoteMarks A 0 ≠ B.sizeTwoRemoteMarks A 1 := by
    intro h
    exact (by decide : (0 : Fin 2) ≠ 1) ((B.sizeTwoRemoteMarks A).injective h)
  obtain ⟨E,hsize,hcounts,f,i,hi,hends,howner,hx0,hu0,hx1,hu1,havoid⟩ :=
    D.sizeTwo_normalized_terminal B.completedHub p q
      (B.sizeTwoRemoteMarks A 0) (B.sizeTwoRemoteMarks A 1)
      (B.syndromeStar_hub_degree_two hcard) he hp hq hpq (hxr 0) (hxr 1) hrs hr hs
  refine ⟨E,hsize,hcounts,f,i,hi,?_,howner,hx0,?_,hx1,?_,havoid⟩
  · intro r
    fin_cases r
    · simpa [remoteRole,hi] using hends 2
    · simpa [remoteRole,hi] using hends 3
  · simpa [p,completedLabel,completedOutside] using congrArg Subtype.val hu0
  · simpa [q,completedLabel,completedOutside] using congrArg Subtype.val hu1

end Gallai.WholeBowtie
