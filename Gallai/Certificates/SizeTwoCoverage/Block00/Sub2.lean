/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block00.Core
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.SizeTwo.Coverage.Block00
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem witness_128 :
    (∀ j : Fin 4, (anchorPermutation (permutation (128 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (128 : Fin 256)) (anchorPermutation (permutation (128 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (128 : Fin 256))) = pairEncodedAt (blockIndex 0 (128 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_129 :
    (∀ j : Fin 4, (anchorPermutation (permutation (129 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (129 : Fin 256)) (anchorPermutation (permutation (129 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (129 : Fin 256))) = pairEncodedAt (blockIndex 0 (129 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_130 :
    (∀ j : Fin 4, (anchorPermutation (permutation (130 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (130 : Fin 256)) (anchorPermutation (permutation (130 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (130 : Fin 256))) = pairEncodedAt (blockIndex 0 (130 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_131 :
    (∀ j : Fin 4, (anchorPermutation (permutation (131 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (131 : Fin 256)) (anchorPermutation (permutation (131 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (131 : Fin 256))) = pairEncodedAt (blockIndex 0 (131 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_132 :
    (∀ j : Fin 4, (anchorPermutation (permutation (132 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (132 : Fin 256)) (anchorPermutation (permutation (132 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (132 : Fin 256))) = pairEncodedAt (blockIndex 0 (132 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_133 :
    (∀ j : Fin 4, (anchorPermutation (permutation (133 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (133 : Fin 256)) (anchorPermutation (permutation (133 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (133 : Fin 256))) = pairEncodedAt (blockIndex 0 (133 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_134 :
    (∀ j : Fin 4, (anchorPermutation (permutation (134 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (134 : Fin 256)) (anchorPermutation (permutation (134 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (134 : Fin 256))) = pairEncodedAt (blockIndex 0 (134 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_135 :
    (∀ j : Fin 4, (anchorPermutation (permutation (135 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (135 : Fin 256)) (anchorPermutation (permutation (135 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (135 : Fin 256))) = pairEncodedAt (blockIndex 0 (135 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_136 :
    (∀ j : Fin 4, (anchorPermutation (permutation (136 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (136 : Fin 256)) (anchorPermutation (permutation (136 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (136 : Fin 256))) = pairEncodedAt (blockIndex 0 (136 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_137 :
    (∀ j : Fin 4, (anchorPermutation (permutation (137 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (137 : Fin 256)) (anchorPermutation (permutation (137 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (137 : Fin 256))) = pairEncodedAt (blockIndex 0 (137 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_138 :
    (∀ j : Fin 4, (anchorPermutation (permutation (138 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (138 : Fin 256)) (anchorPermutation (permutation (138 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (138 : Fin 256))) = pairEncodedAt (blockIndex 0 (138 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_139 :
    (∀ j : Fin 4, (anchorPermutation (permutation (139 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (139 : Fin 256)) (anchorPermutation (permutation (139 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (139 : Fin 256))) = pairEncodedAt (blockIndex 0 (139 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_140 :
    (∀ j : Fin 4, (anchorPermutation (permutation (140 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (140 : Fin 256)) (anchorPermutation (permutation (140 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (140 : Fin 256))) = pairEncodedAt (blockIndex 0 (140 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_141 :
    (∀ j : Fin 4, (anchorPermutation (permutation (141 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (141 : Fin 256)) (anchorPermutation (permutation (141 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (141 : Fin 256))) = pairEncodedAt (blockIndex 0 (141 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_142 :
    (∀ j : Fin 4, (anchorPermutation (permutation (142 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (142 : Fin 256)) (anchorPermutation (permutation (142 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (142 : Fin 256))) = pairEncodedAt (blockIndex 0 (142 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_143 :
    (∀ j : Fin 4, (anchorPermutation (permutation (143 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (143 : Fin 256)) (anchorPermutation (permutation (143 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (143 : Fin 256))) = pairEncodedAt (blockIndex 0 (143 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_144 :
    (∀ j : Fin 4, (anchorPermutation (permutation (144 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (144 : Fin 256)) (anchorPermutation (permutation (144 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (144 : Fin 256))) = pairEncodedAt (blockIndex 0 (144 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_145 :
    (∀ j : Fin 4, (anchorPermutation (permutation (145 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (145 : Fin 256)) (anchorPermutation (permutation (145 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (145 : Fin 256))) = pairEncodedAt (blockIndex 0 (145 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_146 :
    (∀ j : Fin 4, (anchorPermutation (permutation (146 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (146 : Fin 256)) (anchorPermutation (permutation (146 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (146 : Fin 256))) = pairEncodedAt (blockIndex 0 (146 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_147 :
    (∀ j : Fin 4, (anchorPermutation (permutation (147 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (147 : Fin 256)) (anchorPermutation (permutation (147 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (147 : Fin 256))) = pairEncodedAt (blockIndex 0 (147 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_148 :
    (∀ j : Fin 4, (anchorPermutation (permutation (148 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (148 : Fin 256)) (anchorPermutation (permutation (148 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (148 : Fin 256))) = pairEncodedAt (blockIndex 0 (148 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_149 :
    (∀ j : Fin 4, (anchorPermutation (permutation (149 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (149 : Fin 256)) (anchorPermutation (permutation (149 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (149 : Fin 256))) = pairEncodedAt (blockIndex 0 (149 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_150 :
    (∀ j : Fin 4, (anchorPermutation (permutation (150 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (150 : Fin 256)) (anchorPermutation (permutation (150 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (150 : Fin 256))) = pairEncodedAt (blockIndex 0 (150 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_151 :
    (∀ j : Fin 4, (anchorPermutation (permutation (151 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (151 : Fin 256)) (anchorPermutation (permutation (151 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (151 : Fin 256))) = pairEncodedAt (blockIndex 0 (151 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_152 :
    (∀ j : Fin 4, (anchorPermutation (permutation (152 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (152 : Fin 256)) (anchorPermutation (permutation (152 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (152 : Fin 256))) = pairEncodedAt (blockIndex 0 (152 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_153 :
    (∀ j : Fin 4, (anchorPermutation (permutation (153 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (153 : Fin 256)) (anchorPermutation (permutation (153 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (153 : Fin 256))) = pairEncodedAt (blockIndex 0 (153 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_154 :
    (∀ j : Fin 4, (anchorPermutation (permutation (154 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (154 : Fin 256)) (anchorPermutation (permutation (154 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (154 : Fin 256))) = pairEncodedAt (blockIndex 0 (154 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_155 :
    (∀ j : Fin 4, (anchorPermutation (permutation (155 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (155 : Fin 256)) (anchorPermutation (permutation (155 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (155 : Fin 256))) = pairEncodedAt (blockIndex 0 (155 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_156 :
    (∀ j : Fin 4, (anchorPermutation (permutation (156 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (156 : Fin 256)) (anchorPermutation (permutation (156 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (156 : Fin 256))) = pairEncodedAt (blockIndex 0 (156 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_157 :
    (∀ j : Fin 4, (anchorPermutation (permutation (157 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (157 : Fin 256)) (anchorPermutation (permutation (157 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (157 : Fin 256))) = pairEncodedAt (blockIndex 0 (157 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_158 :
    (∀ j : Fin 4, (anchorPermutation (permutation (158 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (158 : Fin 256)) (anchorPermutation (permutation (158 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (158 : Fin 256))) = pairEncodedAt (blockIndex 0 (158 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_159 :
    (∀ j : Fin 4, (anchorPermutation (permutation (159 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (159 : Fin 256)) (anchorPermutation (permutation (159 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (159 : Fin 256))) = pairEncodedAt (blockIndex 0 (159 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_160 :
    (∀ j : Fin 4, (anchorPermutation (permutation (160 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (160 : Fin 256)) (anchorPermutation (permutation (160 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (160 : Fin 256))) = pairEncodedAt (blockIndex 0 (160 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_161 :
    (∀ j : Fin 4, (anchorPermutation (permutation (161 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (161 : Fin 256)) (anchorPermutation (permutation (161 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (161 : Fin 256))) = pairEncodedAt (blockIndex 0 (161 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_162 :
    (∀ j : Fin 4, (anchorPermutation (permutation (162 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (162 : Fin 256)) (anchorPermutation (permutation (162 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (162 : Fin 256))) = pairEncodedAt (blockIndex 0 (162 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_163 :
    (∀ j : Fin 4, (anchorPermutation (permutation (163 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (163 : Fin 256)) (anchorPermutation (permutation (163 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (163 : Fin 256))) = pairEncodedAt (blockIndex 0 (163 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_164 :
    (∀ j : Fin 4, (anchorPermutation (permutation (164 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (164 : Fin 256)) (anchorPermutation (permutation (164 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (164 : Fin 256))) = pairEncodedAt (blockIndex 0 (164 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_165 :
    (∀ j : Fin 4, (anchorPermutation (permutation (165 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (165 : Fin 256)) (anchorPermutation (permutation (165 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (165 : Fin 256))) = pairEncodedAt (blockIndex 0 (165 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_166 :
    (∀ j : Fin 4, (anchorPermutation (permutation (166 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (166 : Fin 256)) (anchorPermutation (permutation (166 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (166 : Fin 256))) = pairEncodedAt (blockIndex 0 (166 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_167 :
    (∀ j : Fin 4, (anchorPermutation (permutation (167 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (167 : Fin 256)) (anchorPermutation (permutation (167 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (167 : Fin 256))) = pairEncodedAt (blockIndex 0 (167 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_168 :
    (∀ j : Fin 4, (anchorPermutation (permutation (168 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (168 : Fin 256)) (anchorPermutation (permutation (168 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (168 : Fin 256))) = pairEncodedAt (blockIndex 0 (168 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_169 :
    (∀ j : Fin 4, (anchorPermutation (permutation (169 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (169 : Fin 256)) (anchorPermutation (permutation (169 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (169 : Fin 256))) = pairEncodedAt (blockIndex 0 (169 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_170 :
    (∀ j : Fin 4, (anchorPermutation (permutation (170 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (170 : Fin 256)) (anchorPermutation (permutation (170 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (170 : Fin 256))) = pairEncodedAt (blockIndex 0 (170 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_171 :
    (∀ j : Fin 4, (anchorPermutation (permutation (171 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (171 : Fin 256)) (anchorPermutation (permutation (171 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (171 : Fin 256))) = pairEncodedAt (blockIndex 0 (171 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_172 :
    (∀ j : Fin 4, (anchorPermutation (permutation (172 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (172 : Fin 256)) (anchorPermutation (permutation (172 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (172 : Fin 256))) = pairEncodedAt (blockIndex 0 (172 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_173 :
    (∀ j : Fin 4, (anchorPermutation (permutation (173 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (173 : Fin 256)) (anchorPermutation (permutation (173 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (173 : Fin 256))) = pairEncodedAt (blockIndex 0 (173 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_174 :
    (∀ j : Fin 4, (anchorPermutation (permutation (174 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (174 : Fin 256)) (anchorPermutation (permutation (174 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (174 : Fin 256))) = pairEncodedAt (blockIndex 0 (174 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_175 :
    (∀ j : Fin 4, (anchorPermutation (permutation (175 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (175 : Fin 256)) (anchorPermutation (permutation (175 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (175 : Fin 256))) = pairEncodedAt (blockIndex 0 (175 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_176 :
    (∀ j : Fin 4, (anchorPermutation (permutation (176 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (176 : Fin 256)) (anchorPermutation (permutation (176 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (176 : Fin 256))) = pairEncodedAt (blockIndex 0 (176 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_177 :
    (∀ j : Fin 4, (anchorPermutation (permutation (177 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (177 : Fin 256)) (anchorPermutation (permutation (177 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (177 : Fin 256))) = pairEncodedAt (blockIndex 0 (177 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_178 :
    (∀ j : Fin 4, (anchorPermutation (permutation (178 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (178 : Fin 256)) (anchorPermutation (permutation (178 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (178 : Fin 256))) = pairEncodedAt (blockIndex 0 (178 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_179 :
    (∀ j : Fin 4, (anchorPermutation (permutation (179 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (179 : Fin 256)) (anchorPermutation (permutation (179 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (179 : Fin 256))) = pairEncodedAt (blockIndex 0 (179 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_180 :
    (∀ j : Fin 4, (anchorPermutation (permutation (180 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (180 : Fin 256)) (anchorPermutation (permutation (180 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (180 : Fin 256))) = pairEncodedAt (blockIndex 0 (180 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_181 :
    (∀ j : Fin 4, (anchorPermutation (permutation (181 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (181 : Fin 256)) (anchorPermutation (permutation (181 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (181 : Fin 256))) = pairEncodedAt (blockIndex 0 (181 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_182 :
    (∀ j : Fin 4, (anchorPermutation (permutation (182 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (182 : Fin 256)) (anchorPermutation (permutation (182 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (182 : Fin 256))) = pairEncodedAt (blockIndex 0 (182 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_183 :
    (∀ j : Fin 4, (anchorPermutation (permutation (183 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (183 : Fin 256)) (anchorPermutation (permutation (183 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (183 : Fin 256))) = pairEncodedAt (blockIndex 0 (183 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_184 :
    (∀ j : Fin 4, (anchorPermutation (permutation (184 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (184 : Fin 256)) (anchorPermutation (permutation (184 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (184 : Fin 256))) = pairEncodedAt (blockIndex 0 (184 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_185 :
    (∀ j : Fin 4, (anchorPermutation (permutation (185 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (185 : Fin 256)) (anchorPermutation (permutation (185 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (185 : Fin 256))) = pairEncodedAt (blockIndex 0 (185 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_186 :
    (∀ j : Fin 4, (anchorPermutation (permutation (186 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (186 : Fin 256)) (anchorPermutation (permutation (186 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (186 : Fin 256))) = pairEncodedAt (blockIndex 0 (186 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_187 :
    (∀ j : Fin 4, (anchorPermutation (permutation (187 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (187 : Fin 256)) (anchorPermutation (permutation (187 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (187 : Fin 256))) = pairEncodedAt (blockIndex 0 (187 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_188 :
    (∀ j : Fin 4, (anchorPermutation (permutation (188 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (188 : Fin 256)) (anchorPermutation (permutation (188 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (188 : Fin 256))) = pairEncodedAt (blockIndex 0 (188 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_189 :
    (∀ j : Fin 4, (anchorPermutation (permutation (189 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (189 : Fin 256)) (anchorPermutation (permutation (189 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (189 : Fin 256))) = pairEncodedAt (blockIndex 0 (189 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_190 :
    (∀ j : Fin 4, (anchorPermutation (permutation (190 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (190 : Fin 256)) (anchorPermutation (permutation (190 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (190 : Fin 256))) = pairEncodedAt (blockIndex 0 (190 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_191 :
    (∀ j : Fin 4, (anchorPermutation (permutation (191 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (191 : Fin 256)) (anchorPermutation (permutation (191 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (191 : Fin 256))) = pairEncodedAt (blockIndex 0 (191 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

theorem witness_chunk_2 (r : Fin 64) :
    (∀ j : Fin 4, (anchorPermutation (permutation ⟨2 * 64 + r.val, by omega⟩) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action ⟨2 * 64 + r.val, by omega⟩) (anchorPermutation (permutation ⟨2 * 64 + r.val, by omega⟩))
      (SizeTwo.Catalogue.Rows.state (orbit ⟨2 * 64 + r.val, by omega⟩)) = pairEncodedAt (blockIndex 0 ⟨2 * 64 + r.val, by omega⟩) := by
  fin_cases r
  · exact witness_128
  · exact witness_129
  · exact witness_130
  · exact witness_131
  · exact witness_132
  · exact witness_133
  · exact witness_134
  · exact witness_135
  · exact witness_136
  · exact witness_137
  · exact witness_138
  · exact witness_139
  · exact witness_140
  · exact witness_141
  · exact witness_142
  · exact witness_143
  · exact witness_144
  · exact witness_145
  · exact witness_146
  · exact witness_147
  · exact witness_148
  · exact witness_149
  · exact witness_150
  · exact witness_151
  · exact witness_152
  · exact witness_153
  · exact witness_154
  · exact witness_155
  · exact witness_156
  · exact witness_157
  · exact witness_158
  · exact witness_159
  · exact witness_160
  · exact witness_161
  · exact witness_162
  · exact witness_163
  · exact witness_164
  · exact witness_165
  · exact witness_166
  · exact witness_167
  · exact witness_168
  · exact witness_169
  · exact witness_170
  · exact witness_171
  · exact witness_172
  · exact witness_173
  · exact witness_174
  · exact witness_175
  · exact witness_176
  · exact witness_177
  · exact witness_178
  · exact witness_179
  · exact witness_180
  · exact witness_181
  · exact witness_182
  · exact witness_183
  · exact witness_184
  · exact witness_185
  · exact witness_186
  · exact witness_187
  · exact witness_188
  · exact witness_189
  · exact witness_190
  · exact witness_191
end Gallai.Certificate.SizeTwo.Coverage.Block00
