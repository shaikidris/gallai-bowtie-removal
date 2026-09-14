/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block01.Core
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.SizeTwo.Coverage.Block01
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem witness_192 :
    (∀ j : Fin 4, (anchorPermutation (permutation (192 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (192 : Fin 256)) (anchorPermutation (permutation (192 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (192 : Fin 256))) = pairEncodedAt (blockIndex 1 (192 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_193 :
    (∀ j : Fin 4, (anchorPermutation (permutation (193 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (193 : Fin 256)) (anchorPermutation (permutation (193 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (193 : Fin 256))) = pairEncodedAt (blockIndex 1 (193 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_194 :
    (∀ j : Fin 4, (anchorPermutation (permutation (194 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (194 : Fin 256)) (anchorPermutation (permutation (194 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (194 : Fin 256))) = pairEncodedAt (blockIndex 1 (194 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_195 :
    (∀ j : Fin 4, (anchorPermutation (permutation (195 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (195 : Fin 256)) (anchorPermutation (permutation (195 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (195 : Fin 256))) = pairEncodedAt (blockIndex 1 (195 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_196 :
    (∀ j : Fin 4, (anchorPermutation (permutation (196 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (196 : Fin 256)) (anchorPermutation (permutation (196 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (196 : Fin 256))) = pairEncodedAt (blockIndex 1 (196 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_197 :
    (∀ j : Fin 4, (anchorPermutation (permutation (197 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (197 : Fin 256)) (anchorPermutation (permutation (197 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (197 : Fin 256))) = pairEncodedAt (blockIndex 1 (197 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_198 :
    (∀ j : Fin 4, (anchorPermutation (permutation (198 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (198 : Fin 256)) (anchorPermutation (permutation (198 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (198 : Fin 256))) = pairEncodedAt (blockIndex 1 (198 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_199 :
    (∀ j : Fin 4, (anchorPermutation (permutation (199 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (199 : Fin 256)) (anchorPermutation (permutation (199 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (199 : Fin 256))) = pairEncodedAt (blockIndex 1 (199 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_200 :
    (∀ j : Fin 4, (anchorPermutation (permutation (200 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (200 : Fin 256)) (anchorPermutation (permutation (200 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (200 : Fin 256))) = pairEncodedAt (blockIndex 1 (200 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_201 :
    (∀ j : Fin 4, (anchorPermutation (permutation (201 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (201 : Fin 256)) (anchorPermutation (permutation (201 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (201 : Fin 256))) = pairEncodedAt (blockIndex 1 (201 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_202 :
    (∀ j : Fin 4, (anchorPermutation (permutation (202 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (202 : Fin 256)) (anchorPermutation (permutation (202 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (202 : Fin 256))) = pairEncodedAt (blockIndex 1 (202 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_203 :
    (∀ j : Fin 4, (anchorPermutation (permutation (203 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (203 : Fin 256)) (anchorPermutation (permutation (203 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (203 : Fin 256))) = pairEncodedAt (blockIndex 1 (203 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_204 :
    (∀ j : Fin 4, (anchorPermutation (permutation (204 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (204 : Fin 256)) (anchorPermutation (permutation (204 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (204 : Fin 256))) = pairEncodedAt (blockIndex 1 (204 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_205 :
    (∀ j : Fin 4, (anchorPermutation (permutation (205 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (205 : Fin 256)) (anchorPermutation (permutation (205 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (205 : Fin 256))) = pairEncodedAt (blockIndex 1 (205 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_206 :
    (∀ j : Fin 4, (anchorPermutation (permutation (206 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (206 : Fin 256)) (anchorPermutation (permutation (206 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (206 : Fin 256))) = pairEncodedAt (blockIndex 1 (206 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_207 :
    (∀ j : Fin 4, (anchorPermutation (permutation (207 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (207 : Fin 256)) (anchorPermutation (permutation (207 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (207 : Fin 256))) = pairEncodedAt (blockIndex 1 (207 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_208 :
    (∀ j : Fin 4, (anchorPermutation (permutation (208 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (208 : Fin 256)) (anchorPermutation (permutation (208 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (208 : Fin 256))) = pairEncodedAt (blockIndex 1 (208 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_209 :
    (∀ j : Fin 4, (anchorPermutation (permutation (209 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (209 : Fin 256)) (anchorPermutation (permutation (209 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (209 : Fin 256))) = pairEncodedAt (blockIndex 1 (209 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_210 :
    (∀ j : Fin 4, (anchorPermutation (permutation (210 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (210 : Fin 256)) (anchorPermutation (permutation (210 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (210 : Fin 256))) = pairEncodedAt (blockIndex 1 (210 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_211 :
    (∀ j : Fin 4, (anchorPermutation (permutation (211 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (211 : Fin 256)) (anchorPermutation (permutation (211 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (211 : Fin 256))) = pairEncodedAt (blockIndex 1 (211 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_212 :
    (∀ j : Fin 4, (anchorPermutation (permutation (212 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (212 : Fin 256)) (anchorPermutation (permutation (212 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (212 : Fin 256))) = pairEncodedAt (blockIndex 1 (212 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_213 :
    (∀ j : Fin 4, (anchorPermutation (permutation (213 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (213 : Fin 256)) (anchorPermutation (permutation (213 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (213 : Fin 256))) = pairEncodedAt (blockIndex 1 (213 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_214 :
    (∀ j : Fin 4, (anchorPermutation (permutation (214 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (214 : Fin 256)) (anchorPermutation (permutation (214 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (214 : Fin 256))) = pairEncodedAt (blockIndex 1 (214 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_215 :
    (∀ j : Fin 4, (anchorPermutation (permutation (215 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (215 : Fin 256)) (anchorPermutation (permutation (215 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (215 : Fin 256))) = pairEncodedAt (blockIndex 1 (215 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_216 :
    (∀ j : Fin 4, (anchorPermutation (permutation (216 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (216 : Fin 256)) (anchorPermutation (permutation (216 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (216 : Fin 256))) = pairEncodedAt (blockIndex 1 (216 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_217 :
    (∀ j : Fin 4, (anchorPermutation (permutation (217 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (217 : Fin 256)) (anchorPermutation (permutation (217 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (217 : Fin 256))) = pairEncodedAt (blockIndex 1 (217 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_218 :
    (∀ j : Fin 4, (anchorPermutation (permutation (218 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (218 : Fin 256)) (anchorPermutation (permutation (218 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (218 : Fin 256))) = pairEncodedAt (blockIndex 1 (218 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_219 :
    (∀ j : Fin 4, (anchorPermutation (permutation (219 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (219 : Fin 256)) (anchorPermutation (permutation (219 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (219 : Fin 256))) = pairEncodedAt (blockIndex 1 (219 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_220 :
    (∀ j : Fin 4, (anchorPermutation (permutation (220 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (220 : Fin 256)) (anchorPermutation (permutation (220 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (220 : Fin 256))) = pairEncodedAt (blockIndex 1 (220 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_221 :
    (∀ j : Fin 4, (anchorPermutation (permutation (221 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (221 : Fin 256)) (anchorPermutation (permutation (221 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (221 : Fin 256))) = pairEncodedAt (blockIndex 1 (221 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_222 :
    (∀ j : Fin 4, (anchorPermutation (permutation (222 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (222 : Fin 256)) (anchorPermutation (permutation (222 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (222 : Fin 256))) = pairEncodedAt (blockIndex 1 (222 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_223 :
    (∀ j : Fin 4, (anchorPermutation (permutation (223 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (223 : Fin 256)) (anchorPermutation (permutation (223 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (223 : Fin 256))) = pairEncodedAt (blockIndex 1 (223 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_224 :
    (∀ j : Fin 4, (anchorPermutation (permutation (224 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (224 : Fin 256)) (anchorPermutation (permutation (224 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (224 : Fin 256))) = pairEncodedAt (blockIndex 1 (224 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_225 :
    (∀ j : Fin 4, (anchorPermutation (permutation (225 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (225 : Fin 256)) (anchorPermutation (permutation (225 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (225 : Fin 256))) = pairEncodedAt (blockIndex 1 (225 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_226 :
    (∀ j : Fin 4, (anchorPermutation (permutation (226 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (226 : Fin 256)) (anchorPermutation (permutation (226 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (226 : Fin 256))) = pairEncodedAt (blockIndex 1 (226 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_227 :
    (∀ j : Fin 4, (anchorPermutation (permutation (227 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (227 : Fin 256)) (anchorPermutation (permutation (227 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (227 : Fin 256))) = pairEncodedAt (blockIndex 1 (227 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_228 :
    (∀ j : Fin 4, (anchorPermutation (permutation (228 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (228 : Fin 256)) (anchorPermutation (permutation (228 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (228 : Fin 256))) = pairEncodedAt (blockIndex 1 (228 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_229 :
    (∀ j : Fin 4, (anchorPermutation (permutation (229 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (229 : Fin 256)) (anchorPermutation (permutation (229 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (229 : Fin 256))) = pairEncodedAt (blockIndex 1 (229 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_230 :
    (∀ j : Fin 4, (anchorPermutation (permutation (230 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (230 : Fin 256)) (anchorPermutation (permutation (230 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (230 : Fin 256))) = pairEncodedAt (blockIndex 1 (230 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_231 :
    (∀ j : Fin 4, (anchorPermutation (permutation (231 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (231 : Fin 256)) (anchorPermutation (permutation (231 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (231 : Fin 256))) = pairEncodedAt (blockIndex 1 (231 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_232 :
    (∀ j : Fin 4, (anchorPermutation (permutation (232 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (232 : Fin 256)) (anchorPermutation (permutation (232 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (232 : Fin 256))) = pairEncodedAt (blockIndex 1 (232 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_233 :
    (∀ j : Fin 4, (anchorPermutation (permutation (233 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (233 : Fin 256)) (anchorPermutation (permutation (233 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (233 : Fin 256))) = pairEncodedAt (blockIndex 1 (233 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_234 :
    (∀ j : Fin 4, (anchorPermutation (permutation (234 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (234 : Fin 256)) (anchorPermutation (permutation (234 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (234 : Fin 256))) = pairEncodedAt (blockIndex 1 (234 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_235 :
    (∀ j : Fin 4, (anchorPermutation (permutation (235 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (235 : Fin 256)) (anchorPermutation (permutation (235 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (235 : Fin 256))) = pairEncodedAt (blockIndex 1 (235 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_236 :
    (∀ j : Fin 4, (anchorPermutation (permutation (236 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (236 : Fin 256)) (anchorPermutation (permutation (236 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (236 : Fin 256))) = pairEncodedAt (blockIndex 1 (236 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_237 :
    (∀ j : Fin 4, (anchorPermutation (permutation (237 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (237 : Fin 256)) (anchorPermutation (permutation (237 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (237 : Fin 256))) = pairEncodedAt (blockIndex 1 (237 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_238 :
    (∀ j : Fin 4, (anchorPermutation (permutation (238 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (238 : Fin 256)) (anchorPermutation (permutation (238 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (238 : Fin 256))) = pairEncodedAt (blockIndex 1 (238 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_239 :
    (∀ j : Fin 4, (anchorPermutation (permutation (239 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (239 : Fin 256)) (anchorPermutation (permutation (239 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (239 : Fin 256))) = pairEncodedAt (blockIndex 1 (239 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_240 :
    (∀ j : Fin 4, (anchorPermutation (permutation (240 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (240 : Fin 256)) (anchorPermutation (permutation (240 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (240 : Fin 256))) = pairEncodedAt (blockIndex 1 (240 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_241 :
    (∀ j : Fin 4, (anchorPermutation (permutation (241 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (241 : Fin 256)) (anchorPermutation (permutation (241 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (241 : Fin 256))) = pairEncodedAt (blockIndex 1 (241 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_242 :
    (∀ j : Fin 4, (anchorPermutation (permutation (242 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (242 : Fin 256)) (anchorPermutation (permutation (242 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (242 : Fin 256))) = pairEncodedAt (blockIndex 1 (242 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_243 :
    (∀ j : Fin 4, (anchorPermutation (permutation (243 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (243 : Fin 256)) (anchorPermutation (permutation (243 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (243 : Fin 256))) = pairEncodedAt (blockIndex 1 (243 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_244 :
    (∀ j : Fin 4, (anchorPermutation (permutation (244 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (244 : Fin 256)) (anchorPermutation (permutation (244 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (244 : Fin 256))) = pairEncodedAt (blockIndex 1 (244 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_245 :
    (∀ j : Fin 4, (anchorPermutation (permutation (245 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (245 : Fin 256)) (anchorPermutation (permutation (245 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (245 : Fin 256))) = pairEncodedAt (blockIndex 1 (245 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_246 :
    (∀ j : Fin 4, (anchorPermutation (permutation (246 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (246 : Fin 256)) (anchorPermutation (permutation (246 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (246 : Fin 256))) = pairEncodedAt (blockIndex 1 (246 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_247 :
    (∀ j : Fin 4, (anchorPermutation (permutation (247 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (247 : Fin 256)) (anchorPermutation (permutation (247 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (247 : Fin 256))) = pairEncodedAt (blockIndex 1 (247 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_248 :
    (∀ j : Fin 4, (anchorPermutation (permutation (248 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (248 : Fin 256)) (anchorPermutation (permutation (248 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (248 : Fin 256))) = pairEncodedAt (blockIndex 1 (248 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_249 :
    (∀ j : Fin 4, (anchorPermutation (permutation (249 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (249 : Fin 256)) (anchorPermutation (permutation (249 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (249 : Fin 256))) = pairEncodedAt (blockIndex 1 (249 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_250 :
    (∀ j : Fin 4, (anchorPermutation (permutation (250 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (250 : Fin 256)) (anchorPermutation (permutation (250 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (250 : Fin 256))) = pairEncodedAt (blockIndex 1 (250 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_251 :
    (∀ j : Fin 4, (anchorPermutation (permutation (251 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (251 : Fin 256)) (anchorPermutation (permutation (251 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (251 : Fin 256))) = pairEncodedAt (blockIndex 1 (251 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_252 :
    (∀ j : Fin 4, (anchorPermutation (permutation (252 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (252 : Fin 256)) (anchorPermutation (permutation (252 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (252 : Fin 256))) = pairEncodedAt (blockIndex 1 (252 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_253 :
    (∀ j : Fin 4, (anchorPermutation (permutation (253 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (253 : Fin 256)) (anchorPermutation (permutation (253 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (253 : Fin 256))) = pairEncodedAt (blockIndex 1 (253 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_254 :
    (∀ j : Fin 4, (anchorPermutation (permutation (254 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (254 : Fin 256)) (anchorPermutation (permutation (254 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (254 : Fin 256))) = pairEncodedAt (blockIndex 1 (254 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_255 :
    (∀ j : Fin 4, (anchorPermutation (permutation (255 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (255 : Fin 256)) (anchorPermutation (permutation (255 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (255 : Fin 256))) = pairEncodedAt (blockIndex 1 (255 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

theorem witness_chunk_3 (r : Fin 64) :
    (∀ j : Fin 4, (anchorPermutation (permutation ⟨3 * 64 + r.val, by omega⟩) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action ⟨3 * 64 + r.val, by omega⟩) (anchorPermutation (permutation ⟨3 * 64 + r.val, by omega⟩))
      (SizeTwo.Catalogue.Rows.state (orbit ⟨3 * 64 + r.val, by omega⟩)) = pairEncodedAt (blockIndex 1 ⟨3 * 64 + r.val, by omega⟩) := by
  fin_cases r
  · exact witness_192
  · exact witness_193
  · exact witness_194
  · exact witness_195
  · exact witness_196
  · exact witness_197
  · exact witness_198
  · exact witness_199
  · exact witness_200
  · exact witness_201
  · exact witness_202
  · exact witness_203
  · exact witness_204
  · exact witness_205
  · exact witness_206
  · exact witness_207
  · exact witness_208
  · exact witness_209
  · exact witness_210
  · exact witness_211
  · exact witness_212
  · exact witness_213
  · exact witness_214
  · exact witness_215
  · exact witness_216
  · exact witness_217
  · exact witness_218
  · exact witness_219
  · exact witness_220
  · exact witness_221
  · exact witness_222
  · exact witness_223
  · exact witness_224
  · exact witness_225
  · exact witness_226
  · exact witness_227
  · exact witness_228
  · exact witness_229
  · exact witness_230
  · exact witness_231
  · exact witness_232
  · exact witness_233
  · exact witness_234
  · exact witness_235
  · exact witness_236
  · exact witness_237
  · exact witness_238
  · exact witness_239
  · exact witness_240
  · exact witness_241
  · exact witness_242
  · exact witness_243
  · exact witness_244
  · exact witness_245
  · exact witness_246
  · exact witness_247
  · exact witness_248
  · exact witness_249
  · exact witness_250
  · exact witness_251
  · exact witness_252
  · exact witness_253
  · exact witness_254
  · exact witness_255
end Gallai.Certificate.SizeTwo.Coverage.Block01
