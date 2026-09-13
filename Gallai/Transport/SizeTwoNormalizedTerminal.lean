/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Transport.SizeTwoHubSelection
import Gallai.Transport.SizeTwoTerminalSelection

/-! # Actual normalized terminal profiles with fixed spoke roles -/
namespace Gallai.Decomposition
variable {V : Type*} [Fintype V] [DecidableEq V]
variable {H : SimpleGraph V} [DecidableRel H.Adj]

/-- Normalize the original decomposition and select a catalogue profile with
spokes p and q assigned to roles zero and one, respectively. This preserves
size and every endpoint count; no favourable decomposition is postulated. -/
theorem sizeTwo_normalized_terminal (D : Decomposition H) (x p q r s : V)
    (hd : H.degree x = 2) (he : D.endpointCount x = 2)
    (hp : H.Adj x p) (hq : H.Adj x q) (hpq : p ≠ q)
    (hxr : x ≠ r) (hxs : x ≠ s) (hrs : r ≠ s)
    (hr : 0 < D.endpointCount r) (hs : 0 < D.endpointCount s) :
    ∃ E : Decomposition H, E.size = D.size ∧
      (∀ v, E.endpointCount v = D.endpointCount v) ∧
      ∃ f : Fin 4 → Fin E.size, ∃ i : Fin 13,
        Certificate.SizeTwo.through i = false ∧
        (∀ j, (E.path (f j)).start = (![x,x,r,s] j) ∨
          (E.path (f j)).finish = (![x,x,r,s] j)) ∧
        (∀ j k, f j = f k ↔ Certificate.SizeTwo.owner i j = Certificate.SizeTwo.owner i k) ∧
        (E.path (f 0)).finish = x ∧ (E.path (f 0)).walk.reverse.snd = p ∧
        (E.path (f 1)).finish = x ∧ (E.path (f 1)).walk.reverse.snd = q ∧
        ∀ k : Fin E.size, k ≠ f 0 → k ≠ f 1 → x ∉ (E.path k).walk.support := by
  obtain ⟨ip,iq,hneq,hpf,hpn,hqf,hqn,havoid⟩ :=
    D.degree_two_terminal_spoke_selection x p q hd he hp hq hpq
  let E := D.orientToward x
  have hrE : 0 < E.endpointCount r := by
    simpa only [E,D.orientToward_endpointCount] using hr
  have hsE : 0 < E.endpointCount s := by
    simpa only [E,D.orientToward_endpointCount] using hs
  obtain ⟨f,i,hf0,hf1,hi,hends,howner⟩ := E.sizeTwo_terminal_selection_fixed x r s
    hxr hxs hrs ip iq hneq (Or.inr hpf) (Or.inr hqf) hrE hsE
  refine ⟨E,rfl,D.orientToward_endpointCount x,f,i,hi,hends,howner,?_,?_,?_,?_,?_⟩
  · rw [hf0]; exact hpf
  · rw [hf0]; exact hpn
  · rw [hf1]; exact hqf
  · rw [hf1]; exact hqn
  · intro k hk0 hk1 hk
    have hk' : x ∈ (D.path k).walk.support :=
      ((D.path k).mem_toward_support x x).mp hk
    exact havoid k (by simpa only [hf0,E,orientToward_size] using hk0)
      (by simpa only [hf1,E,orientToward_size] using hk1) hk'

end Gallai.Decomposition
