/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block10.Core
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.SizeTwo.Coverage.Block10
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem witness_064 :
    (∀ j : Fin 4, (anchorPermutation (permutation (64 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (64 : Fin 256)) (anchorPermutation (permutation (64 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (64 : Fin 256))) = pairEncodedAt (blockIndex 10 (64 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_065 :
    (∀ j : Fin 4, (anchorPermutation (permutation (65 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (65 : Fin 256)) (anchorPermutation (permutation (65 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (65 : Fin 256))) = pairEncodedAt (blockIndex 10 (65 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_066 :
    (∀ j : Fin 4, (anchorPermutation (permutation (66 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (66 : Fin 256)) (anchorPermutation (permutation (66 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (66 : Fin 256))) = pairEncodedAt (blockIndex 10 (66 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_067 :
    (∀ j : Fin 4, (anchorPermutation (permutation (67 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (67 : Fin 256)) (anchorPermutation (permutation (67 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (67 : Fin 256))) = pairEncodedAt (blockIndex 10 (67 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_068 :
    (∀ j : Fin 4, (anchorPermutation (permutation (68 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (68 : Fin 256)) (anchorPermutation (permutation (68 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (68 : Fin 256))) = pairEncodedAt (blockIndex 10 (68 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_069 :
    (∀ j : Fin 4, (anchorPermutation (permutation (69 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (69 : Fin 256)) (anchorPermutation (permutation (69 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (69 : Fin 256))) = pairEncodedAt (blockIndex 10 (69 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_070 :
    (∀ j : Fin 4, (anchorPermutation (permutation (70 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (70 : Fin 256)) (anchorPermutation (permutation (70 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (70 : Fin 256))) = pairEncodedAt (blockIndex 10 (70 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_071 :
    (∀ j : Fin 4, (anchorPermutation (permutation (71 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (71 : Fin 256)) (anchorPermutation (permutation (71 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (71 : Fin 256))) = pairEncodedAt (blockIndex 10 (71 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_072 :
    (∀ j : Fin 4, (anchorPermutation (permutation (72 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (72 : Fin 256)) (anchorPermutation (permutation (72 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (72 : Fin 256))) = pairEncodedAt (blockIndex 10 (72 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_073 :
    (∀ j : Fin 4, (anchorPermutation (permutation (73 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (73 : Fin 256)) (anchorPermutation (permutation (73 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (73 : Fin 256))) = pairEncodedAt (blockIndex 10 (73 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_074 :
    (∀ j : Fin 4, (anchorPermutation (permutation (74 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (74 : Fin 256)) (anchorPermutation (permutation (74 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (74 : Fin 256))) = pairEncodedAt (blockIndex 10 (74 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_075 :
    (∀ j : Fin 4, (anchorPermutation (permutation (75 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (75 : Fin 256)) (anchorPermutation (permutation (75 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (75 : Fin 256))) = pairEncodedAt (blockIndex 10 (75 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_076 :
    (∀ j : Fin 4, (anchorPermutation (permutation (76 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (76 : Fin 256)) (anchorPermutation (permutation (76 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (76 : Fin 256))) = pairEncodedAt (blockIndex 10 (76 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_077 :
    (∀ j : Fin 4, (anchorPermutation (permutation (77 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (77 : Fin 256)) (anchorPermutation (permutation (77 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (77 : Fin 256))) = pairEncodedAt (blockIndex 10 (77 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_078 :
    (∀ j : Fin 4, (anchorPermutation (permutation (78 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (78 : Fin 256)) (anchorPermutation (permutation (78 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (78 : Fin 256))) = pairEncodedAt (blockIndex 10 (78 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_079 :
    (∀ j : Fin 4, (anchorPermutation (permutation (79 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (79 : Fin 256)) (anchorPermutation (permutation (79 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (79 : Fin 256))) = pairEncodedAt (blockIndex 10 (79 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_080 :
    (∀ j : Fin 4, (anchorPermutation (permutation (80 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (80 : Fin 256)) (anchorPermutation (permutation (80 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (80 : Fin 256))) = pairEncodedAt (blockIndex 10 (80 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_081 :
    (∀ j : Fin 4, (anchorPermutation (permutation (81 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (81 : Fin 256)) (anchorPermutation (permutation (81 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (81 : Fin 256))) = pairEncodedAt (blockIndex 10 (81 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_082 :
    (∀ j : Fin 4, (anchorPermutation (permutation (82 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (82 : Fin 256)) (anchorPermutation (permutation (82 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (82 : Fin 256))) = pairEncodedAt (blockIndex 10 (82 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_083 :
    (∀ j : Fin 4, (anchorPermutation (permutation (83 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (83 : Fin 256)) (anchorPermutation (permutation (83 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (83 : Fin 256))) = pairEncodedAt (blockIndex 10 (83 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_084 :
    (∀ j : Fin 4, (anchorPermutation (permutation (84 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (84 : Fin 256)) (anchorPermutation (permutation (84 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (84 : Fin 256))) = pairEncodedAt (blockIndex 10 (84 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_085 :
    (∀ j : Fin 4, (anchorPermutation (permutation (85 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (85 : Fin 256)) (anchorPermutation (permutation (85 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (85 : Fin 256))) = pairEncodedAt (blockIndex 10 (85 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_086 :
    (∀ j : Fin 4, (anchorPermutation (permutation (86 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (86 : Fin 256)) (anchorPermutation (permutation (86 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (86 : Fin 256))) = pairEncodedAt (blockIndex 10 (86 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_087 :
    (∀ j : Fin 4, (anchorPermutation (permutation (87 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (87 : Fin 256)) (anchorPermutation (permutation (87 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (87 : Fin 256))) = pairEncodedAt (blockIndex 10 (87 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_088 :
    (∀ j : Fin 4, (anchorPermutation (permutation (88 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (88 : Fin 256)) (anchorPermutation (permutation (88 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (88 : Fin 256))) = pairEncodedAt (blockIndex 10 (88 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_089 :
    (∀ j : Fin 4, (anchorPermutation (permutation (89 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (89 : Fin 256)) (anchorPermutation (permutation (89 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (89 : Fin 256))) = pairEncodedAt (blockIndex 10 (89 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_090 :
    (∀ j : Fin 4, (anchorPermutation (permutation (90 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (90 : Fin 256)) (anchorPermutation (permutation (90 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (90 : Fin 256))) = pairEncodedAt (blockIndex 10 (90 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_091 :
    (∀ j : Fin 4, (anchorPermutation (permutation (91 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (91 : Fin 256)) (anchorPermutation (permutation (91 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (91 : Fin 256))) = pairEncodedAt (blockIndex 10 (91 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_092 :
    (∀ j : Fin 4, (anchorPermutation (permutation (92 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (92 : Fin 256)) (anchorPermutation (permutation (92 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (92 : Fin 256))) = pairEncodedAt (blockIndex 10 (92 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_093 :
    (∀ j : Fin 4, (anchorPermutation (permutation (93 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (93 : Fin 256)) (anchorPermutation (permutation (93 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (93 : Fin 256))) = pairEncodedAt (blockIndex 10 (93 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_094 :
    (∀ j : Fin 4, (anchorPermutation (permutation (94 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (94 : Fin 256)) (anchorPermutation (permutation (94 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (94 : Fin 256))) = pairEncodedAt (blockIndex 10 (94 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_095 :
    (∀ j : Fin 4, (anchorPermutation (permutation (95 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (95 : Fin 256)) (anchorPermutation (permutation (95 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (95 : Fin 256))) = pairEncodedAt (blockIndex 10 (95 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_096 :
    (∀ j : Fin 4, (anchorPermutation (permutation (96 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (96 : Fin 256)) (anchorPermutation (permutation (96 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (96 : Fin 256))) = pairEncodedAt (blockIndex 10 (96 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_097 :
    (∀ j : Fin 4, (anchorPermutation (permutation (97 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (97 : Fin 256)) (anchorPermutation (permutation (97 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (97 : Fin 256))) = pairEncodedAt (blockIndex 10 (97 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_098 :
    (∀ j : Fin 4, (anchorPermutation (permutation (98 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (98 : Fin 256)) (anchorPermutation (permutation (98 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (98 : Fin 256))) = pairEncodedAt (blockIndex 10 (98 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_099 :
    (∀ j : Fin 4, (anchorPermutation (permutation (99 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (99 : Fin 256)) (anchorPermutation (permutation (99 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (99 : Fin 256))) = pairEncodedAt (blockIndex 10 (99 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_100 :
    (∀ j : Fin 4, (anchorPermutation (permutation (100 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (100 : Fin 256)) (anchorPermutation (permutation (100 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (100 : Fin 256))) = pairEncodedAt (blockIndex 10 (100 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_101 :
    (∀ j : Fin 4, (anchorPermutation (permutation (101 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (101 : Fin 256)) (anchorPermutation (permutation (101 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (101 : Fin 256))) = pairEncodedAt (blockIndex 10 (101 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_102 :
    (∀ j : Fin 4, (anchorPermutation (permutation (102 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (102 : Fin 256)) (anchorPermutation (permutation (102 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (102 : Fin 256))) = pairEncodedAt (blockIndex 10 (102 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_103 :
    (∀ j : Fin 4, (anchorPermutation (permutation (103 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (103 : Fin 256)) (anchorPermutation (permutation (103 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (103 : Fin 256))) = pairEncodedAt (blockIndex 10 (103 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_104 :
    (∀ j : Fin 4, (anchorPermutation (permutation (104 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (104 : Fin 256)) (anchorPermutation (permutation (104 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (104 : Fin 256))) = pairEncodedAt (blockIndex 10 (104 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_105 :
    (∀ j : Fin 4, (anchorPermutation (permutation (105 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (105 : Fin 256)) (anchorPermutation (permutation (105 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (105 : Fin 256))) = pairEncodedAt (blockIndex 10 (105 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_106 :
    (∀ j : Fin 4, (anchorPermutation (permutation (106 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (106 : Fin 256)) (anchorPermutation (permutation (106 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (106 : Fin 256))) = pairEncodedAt (blockIndex 10 (106 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_107 :
    (∀ j : Fin 4, (anchorPermutation (permutation (107 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (107 : Fin 256)) (anchorPermutation (permutation (107 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (107 : Fin 256))) = pairEncodedAt (blockIndex 10 (107 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_108 :
    (∀ j : Fin 4, (anchorPermutation (permutation (108 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (108 : Fin 256)) (anchorPermutation (permutation (108 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (108 : Fin 256))) = pairEncodedAt (blockIndex 10 (108 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_109 :
    (∀ j : Fin 4, (anchorPermutation (permutation (109 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (109 : Fin 256)) (anchorPermutation (permutation (109 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (109 : Fin 256))) = pairEncodedAt (blockIndex 10 (109 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_110 :
    (∀ j : Fin 4, (anchorPermutation (permutation (110 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (110 : Fin 256)) (anchorPermutation (permutation (110 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (110 : Fin 256))) = pairEncodedAt (blockIndex 10 (110 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_111 :
    (∀ j : Fin 4, (anchorPermutation (permutation (111 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (111 : Fin 256)) (anchorPermutation (permutation (111 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (111 : Fin 256))) = pairEncodedAt (blockIndex 10 (111 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_112 :
    (∀ j : Fin 4, (anchorPermutation (permutation (112 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (112 : Fin 256)) (anchorPermutation (permutation (112 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (112 : Fin 256))) = pairEncodedAt (blockIndex 10 (112 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_113 :
    (∀ j : Fin 4, (anchorPermutation (permutation (113 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (113 : Fin 256)) (anchorPermutation (permutation (113 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (113 : Fin 256))) = pairEncodedAt (blockIndex 10 (113 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_114 :
    (∀ j : Fin 4, (anchorPermutation (permutation (114 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (114 : Fin 256)) (anchorPermutation (permutation (114 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (114 : Fin 256))) = pairEncodedAt (blockIndex 10 (114 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_115 :
    (∀ j : Fin 4, (anchorPermutation (permutation (115 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (115 : Fin 256)) (anchorPermutation (permutation (115 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (115 : Fin 256))) = pairEncodedAt (blockIndex 10 (115 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_116 :
    (∀ j : Fin 4, (anchorPermutation (permutation (116 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (116 : Fin 256)) (anchorPermutation (permutation (116 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (116 : Fin 256))) = pairEncodedAt (blockIndex 10 (116 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_117 :
    (∀ j : Fin 4, (anchorPermutation (permutation (117 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (117 : Fin 256)) (anchorPermutation (permutation (117 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (117 : Fin 256))) = pairEncodedAt (blockIndex 10 (117 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_118 :
    (∀ j : Fin 4, (anchorPermutation (permutation (118 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (118 : Fin 256)) (anchorPermutation (permutation (118 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (118 : Fin 256))) = pairEncodedAt (blockIndex 10 (118 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_119 :
    (∀ j : Fin 4, (anchorPermutation (permutation (119 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (119 : Fin 256)) (anchorPermutation (permutation (119 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (119 : Fin 256))) = pairEncodedAt (blockIndex 10 (119 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_120 :
    (∀ j : Fin 4, (anchorPermutation (permutation (120 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (120 : Fin 256)) (anchorPermutation (permutation (120 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (120 : Fin 256))) = pairEncodedAt (blockIndex 10 (120 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_121 :
    (∀ j : Fin 4, (anchorPermutation (permutation (121 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (121 : Fin 256)) (anchorPermutation (permutation (121 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (121 : Fin 256))) = pairEncodedAt (blockIndex 10 (121 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_122 :
    (∀ j : Fin 4, (anchorPermutation (permutation (122 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (122 : Fin 256)) (anchorPermutation (permutation (122 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (122 : Fin 256))) = pairEncodedAt (blockIndex 10 (122 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_123 :
    (∀ j : Fin 4, (anchorPermutation (permutation (123 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (123 : Fin 256)) (anchorPermutation (permutation (123 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (123 : Fin 256))) = pairEncodedAt (blockIndex 10 (123 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_124 :
    (∀ j : Fin 4, (anchorPermutation (permutation (124 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (124 : Fin 256)) (anchorPermutation (permutation (124 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (124 : Fin 256))) = pairEncodedAt (blockIndex 10 (124 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_125 :
    (∀ j : Fin 4, (anchorPermutation (permutation (125 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (125 : Fin 256)) (anchorPermutation (permutation (125 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (125 : Fin 256))) = pairEncodedAt (blockIndex 10 (125 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_126 :
    (∀ j : Fin 4, (anchorPermutation (permutation (126 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (126 : Fin 256)) (anchorPermutation (permutation (126 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (126 : Fin 256))) = pairEncodedAt (blockIndex 10 (126 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_127 :
    (∀ j : Fin 4, (anchorPermutation (permutation (127 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (127 : Fin 256)) (anchorPermutation (permutation (127 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (127 : Fin 256))) = pairEncodedAt (blockIndex 10 (127 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

theorem witness_chunk_1 (r : Fin 64) :
    (∀ j : Fin 4, (anchorPermutation (permutation ⟨1 * 64 + r.val, by omega⟩) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action ⟨1 * 64 + r.val, by omega⟩) (anchorPermutation (permutation ⟨1 * 64 + r.val, by omega⟩))
      (SizeTwo.Catalogue.Rows.state (orbit ⟨1 * 64 + r.val, by omega⟩)) = pairEncodedAt (blockIndex 10 ⟨1 * 64 + r.val, by omega⟩) := by
  fin_cases r
  · exact witness_064
  · exact witness_065
  · exact witness_066
  · exact witness_067
  · exact witness_068
  · exact witness_069
  · exact witness_070
  · exact witness_071
  · exact witness_072
  · exact witness_073
  · exact witness_074
  · exact witness_075
  · exact witness_076
  · exact witness_077
  · exact witness_078
  · exact witness_079
  · exact witness_080
  · exact witness_081
  · exact witness_082
  · exact witness_083
  · exact witness_084
  · exact witness_085
  · exact witness_086
  · exact witness_087
  · exact witness_088
  · exact witness_089
  · exact witness_090
  · exact witness_091
  · exact witness_092
  · exact witness_093
  · exact witness_094
  · exact witness_095
  · exact witness_096
  · exact witness_097
  · exact witness_098
  · exact witness_099
  · exact witness_100
  · exact witness_101
  · exact witness_102
  · exact witness_103
  · exact witness_104
  · exact witness_105
  · exact witness_106
  · exact witness_107
  · exact witness_108
  · exact witness_109
  · exact witness_110
  · exact witness_111
  · exact witness_112
  · exact witness_113
  · exact witness_114
  · exact witness_115
  · exact witness_116
  · exact witness_117
  · exact witness_118
  · exact witness_119
  · exact witness_120
  · exact witness_121
  · exact witness_122
  · exact witness_123
  · exact witness_124
  · exact witness_125
  · exact witness_126
  · exact witness_127
end Gallai.Certificate.SizeTwo.Coverage.Block10
