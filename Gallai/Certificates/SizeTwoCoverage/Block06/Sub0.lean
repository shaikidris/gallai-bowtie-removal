/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.SizeTwoCoverage.Block06.Core
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.SizeTwo.Coverage.Block06
open CompletedStar CompletedStar.Coverage
set_option maxRecDepth 100000
set_option maxHeartbeats 0
private theorem witness_000 :
    (∀ j : Fin 4, (anchorPermutation (permutation (0 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (0 : Fin 256)) (anchorPermutation (permutation (0 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (0 : Fin 256))) = pairEncodedAt (blockIndex 6 (0 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_001 :
    (∀ j : Fin 4, (anchorPermutation (permutation (1 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (1 : Fin 256)) (anchorPermutation (permutation (1 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (1 : Fin 256))) = pairEncodedAt (blockIndex 6 (1 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_002 :
    (∀ j : Fin 4, (anchorPermutation (permutation (2 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (2 : Fin 256)) (anchorPermutation (permutation (2 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (2 : Fin 256))) = pairEncodedAt (blockIndex 6 (2 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_003 :
    (∀ j : Fin 4, (anchorPermutation (permutation (3 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (3 : Fin 256)) (anchorPermutation (permutation (3 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (3 : Fin 256))) = pairEncodedAt (blockIndex 6 (3 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_004 :
    (∀ j : Fin 4, (anchorPermutation (permutation (4 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (4 : Fin 256)) (anchorPermutation (permutation (4 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (4 : Fin 256))) = pairEncodedAt (blockIndex 6 (4 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_005 :
    (∀ j : Fin 4, (anchorPermutation (permutation (5 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (5 : Fin 256)) (anchorPermutation (permutation (5 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (5 : Fin 256))) = pairEncodedAt (blockIndex 6 (5 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_006 :
    (∀ j : Fin 4, (anchorPermutation (permutation (6 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (6 : Fin 256)) (anchorPermutation (permutation (6 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (6 : Fin 256))) = pairEncodedAt (blockIndex 6 (6 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_007 :
    (∀ j : Fin 4, (anchorPermutation (permutation (7 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (7 : Fin 256)) (anchorPermutation (permutation (7 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (7 : Fin 256))) = pairEncodedAt (blockIndex 6 (7 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_008 :
    (∀ j : Fin 4, (anchorPermutation (permutation (8 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (8 : Fin 256)) (anchorPermutation (permutation (8 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (8 : Fin 256))) = pairEncodedAt (blockIndex 6 (8 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_009 :
    (∀ j : Fin 4, (anchorPermutation (permutation (9 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (9 : Fin 256)) (anchorPermutation (permutation (9 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (9 : Fin 256))) = pairEncodedAt (blockIndex 6 (9 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_010 :
    (∀ j : Fin 4, (anchorPermutation (permutation (10 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (10 : Fin 256)) (anchorPermutation (permutation (10 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (10 : Fin 256))) = pairEncodedAt (blockIndex 6 (10 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_011 :
    (∀ j : Fin 4, (anchorPermutation (permutation (11 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (11 : Fin 256)) (anchorPermutation (permutation (11 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (11 : Fin 256))) = pairEncodedAt (blockIndex 6 (11 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_012 :
    (∀ j : Fin 4, (anchorPermutation (permutation (12 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (12 : Fin 256)) (anchorPermutation (permutation (12 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (12 : Fin 256))) = pairEncodedAt (blockIndex 6 (12 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_013 :
    (∀ j : Fin 4, (anchorPermutation (permutation (13 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (13 : Fin 256)) (anchorPermutation (permutation (13 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (13 : Fin 256))) = pairEncodedAt (blockIndex 6 (13 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_014 :
    (∀ j : Fin 4, (anchorPermutation (permutation (14 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (14 : Fin 256)) (anchorPermutation (permutation (14 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (14 : Fin 256))) = pairEncodedAt (blockIndex 6 (14 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_015 :
    (∀ j : Fin 4, (anchorPermutation (permutation (15 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (15 : Fin 256)) (anchorPermutation (permutation (15 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (15 : Fin 256))) = pairEncodedAt (blockIndex 6 (15 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_016 :
    (∀ j : Fin 4, (anchorPermutation (permutation (16 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (16 : Fin 256)) (anchorPermutation (permutation (16 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (16 : Fin 256))) = pairEncodedAt (blockIndex 6 (16 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_017 :
    (∀ j : Fin 4, (anchorPermutation (permutation (17 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (17 : Fin 256)) (anchorPermutation (permutation (17 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (17 : Fin 256))) = pairEncodedAt (blockIndex 6 (17 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_018 :
    (∀ j : Fin 4, (anchorPermutation (permutation (18 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (18 : Fin 256)) (anchorPermutation (permutation (18 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (18 : Fin 256))) = pairEncodedAt (blockIndex 6 (18 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_019 :
    (∀ j : Fin 4, (anchorPermutation (permutation (19 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (19 : Fin 256)) (anchorPermutation (permutation (19 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (19 : Fin 256))) = pairEncodedAt (blockIndex 6 (19 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_020 :
    (∀ j : Fin 4, (anchorPermutation (permutation (20 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (20 : Fin 256)) (anchorPermutation (permutation (20 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (20 : Fin 256))) = pairEncodedAt (blockIndex 6 (20 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_021 :
    (∀ j : Fin 4, (anchorPermutation (permutation (21 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (21 : Fin 256)) (anchorPermutation (permutation (21 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (21 : Fin 256))) = pairEncodedAt (blockIndex 6 (21 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_022 :
    (∀ j : Fin 4, (anchorPermutation (permutation (22 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (22 : Fin 256)) (anchorPermutation (permutation (22 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (22 : Fin 256))) = pairEncodedAt (blockIndex 6 (22 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_023 :
    (∀ j : Fin 4, (anchorPermutation (permutation (23 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (23 : Fin 256)) (anchorPermutation (permutation (23 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (23 : Fin 256))) = pairEncodedAt (blockIndex 6 (23 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_024 :
    (∀ j : Fin 4, (anchorPermutation (permutation (24 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (24 : Fin 256)) (anchorPermutation (permutation (24 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (24 : Fin 256))) = pairEncodedAt (blockIndex 6 (24 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_025 :
    (∀ j : Fin 4, (anchorPermutation (permutation (25 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (25 : Fin 256)) (anchorPermutation (permutation (25 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (25 : Fin 256))) = pairEncodedAt (blockIndex 6 (25 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_026 :
    (∀ j : Fin 4, (anchorPermutation (permutation (26 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (26 : Fin 256)) (anchorPermutation (permutation (26 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (26 : Fin 256))) = pairEncodedAt (blockIndex 6 (26 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_027 :
    (∀ j : Fin 4, (anchorPermutation (permutation (27 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (27 : Fin 256)) (anchorPermutation (permutation (27 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (27 : Fin 256))) = pairEncodedAt (blockIndex 6 (27 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_028 :
    (∀ j : Fin 4, (anchorPermutation (permutation (28 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (28 : Fin 256)) (anchorPermutation (permutation (28 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (28 : Fin 256))) = pairEncodedAt (blockIndex 6 (28 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_029 :
    (∀ j : Fin 4, (anchorPermutation (permutation (29 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (29 : Fin 256)) (anchorPermutation (permutation (29 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (29 : Fin 256))) = pairEncodedAt (blockIndex 6 (29 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_030 :
    (∀ j : Fin 4, (anchorPermutation (permutation (30 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (30 : Fin 256)) (anchorPermutation (permutation (30 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (30 : Fin 256))) = pairEncodedAt (blockIndex 6 (30 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_031 :
    (∀ j : Fin 4, (anchorPermutation (permutation (31 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (31 : Fin 256)) (anchorPermutation (permutation (31 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (31 : Fin 256))) = pairEncodedAt (blockIndex 6 (31 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_032 :
    (∀ j : Fin 4, (anchorPermutation (permutation (32 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (32 : Fin 256)) (anchorPermutation (permutation (32 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (32 : Fin 256))) = pairEncodedAt (blockIndex 6 (32 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_033 :
    (∀ j : Fin 4, (anchorPermutation (permutation (33 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (33 : Fin 256)) (anchorPermutation (permutation (33 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (33 : Fin 256))) = pairEncodedAt (blockIndex 6 (33 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_034 :
    (∀ j : Fin 4, (anchorPermutation (permutation (34 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (34 : Fin 256)) (anchorPermutation (permutation (34 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (34 : Fin 256))) = pairEncodedAt (blockIndex 6 (34 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_035 :
    (∀ j : Fin 4, (anchorPermutation (permutation (35 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (35 : Fin 256)) (anchorPermutation (permutation (35 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (35 : Fin 256))) = pairEncodedAt (blockIndex 6 (35 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_036 :
    (∀ j : Fin 4, (anchorPermutation (permutation (36 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (36 : Fin 256)) (anchorPermutation (permutation (36 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (36 : Fin 256))) = pairEncodedAt (blockIndex 6 (36 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_037 :
    (∀ j : Fin 4, (anchorPermutation (permutation (37 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (37 : Fin 256)) (anchorPermutation (permutation (37 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (37 : Fin 256))) = pairEncodedAt (blockIndex 6 (37 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_038 :
    (∀ j : Fin 4, (anchorPermutation (permutation (38 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (38 : Fin 256)) (anchorPermutation (permutation (38 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (38 : Fin 256))) = pairEncodedAt (blockIndex 6 (38 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_039 :
    (∀ j : Fin 4, (anchorPermutation (permutation (39 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (39 : Fin 256)) (anchorPermutation (permutation (39 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (39 : Fin 256))) = pairEncodedAt (blockIndex 6 (39 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_040 :
    (∀ j : Fin 4, (anchorPermutation (permutation (40 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (40 : Fin 256)) (anchorPermutation (permutation (40 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (40 : Fin 256))) = pairEncodedAt (blockIndex 6 (40 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_041 :
    (∀ j : Fin 4, (anchorPermutation (permutation (41 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (41 : Fin 256)) (anchorPermutation (permutation (41 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (41 : Fin 256))) = pairEncodedAt (blockIndex 6 (41 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_042 :
    (∀ j : Fin 4, (anchorPermutation (permutation (42 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (42 : Fin 256)) (anchorPermutation (permutation (42 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (42 : Fin 256))) = pairEncodedAt (blockIndex 6 (42 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_043 :
    (∀ j : Fin 4, (anchorPermutation (permutation (43 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (43 : Fin 256)) (anchorPermutation (permutation (43 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (43 : Fin 256))) = pairEncodedAt (blockIndex 6 (43 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_044 :
    (∀ j : Fin 4, (anchorPermutation (permutation (44 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (44 : Fin 256)) (anchorPermutation (permutation (44 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (44 : Fin 256))) = pairEncodedAt (blockIndex 6 (44 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_045 :
    (∀ j : Fin 4, (anchorPermutation (permutation (45 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (45 : Fin 256)) (anchorPermutation (permutation (45 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (45 : Fin 256))) = pairEncodedAt (blockIndex 6 (45 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_046 :
    (∀ j : Fin 4, (anchorPermutation (permutation (46 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (46 : Fin 256)) (anchorPermutation (permutation (46 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (46 : Fin 256))) = pairEncodedAt (blockIndex 6 (46 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_047 :
    (∀ j : Fin 4, (anchorPermutation (permutation (47 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (47 : Fin 256)) (anchorPermutation (permutation (47 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (47 : Fin 256))) = pairEncodedAt (blockIndex 6 (47 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_048 :
    (∀ j : Fin 4, (anchorPermutation (permutation (48 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (48 : Fin 256)) (anchorPermutation (permutation (48 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (48 : Fin 256))) = pairEncodedAt (blockIndex 6 (48 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_049 :
    (∀ j : Fin 4, (anchorPermutation (permutation (49 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (49 : Fin 256)) (anchorPermutation (permutation (49 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (49 : Fin 256))) = pairEncodedAt (blockIndex 6 (49 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_050 :
    (∀ j : Fin 4, (anchorPermutation (permutation (50 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (50 : Fin 256)) (anchorPermutation (permutation (50 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (50 : Fin 256))) = pairEncodedAt (blockIndex 6 (50 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_051 :
    (∀ j : Fin 4, (anchorPermutation (permutation (51 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (51 : Fin 256)) (anchorPermutation (permutation (51 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (51 : Fin 256))) = pairEncodedAt (blockIndex 6 (51 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_052 :
    (∀ j : Fin 4, (anchorPermutation (permutation (52 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (52 : Fin 256)) (anchorPermutation (permutation (52 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (52 : Fin 256))) = pairEncodedAt (blockIndex 6 (52 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_053 :
    (∀ j : Fin 4, (anchorPermutation (permutation (53 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (53 : Fin 256)) (anchorPermutation (permutation (53 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (53 : Fin 256))) = pairEncodedAt (blockIndex 6 (53 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_054 :
    (∀ j : Fin 4, (anchorPermutation (permutation (54 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (54 : Fin 256)) (anchorPermutation (permutation (54 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (54 : Fin 256))) = pairEncodedAt (blockIndex 6 (54 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_055 :
    (∀ j : Fin 4, (anchorPermutation (permutation (55 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (55 : Fin 256)) (anchorPermutation (permutation (55 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (55 : Fin 256))) = pairEncodedAt (blockIndex 6 (55 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_056 :
    (∀ j : Fin 4, (anchorPermutation (permutation (56 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (56 : Fin 256)) (anchorPermutation (permutation (56 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (56 : Fin 256))) = pairEncodedAt (blockIndex 6 (56 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_057 :
    (∀ j : Fin 4, (anchorPermutation (permutation (57 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (57 : Fin 256)) (anchorPermutation (permutation (57 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (57 : Fin 256))) = pairEncodedAt (blockIndex 6 (57 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_058 :
    (∀ j : Fin 4, (anchorPermutation (permutation (58 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (58 : Fin 256)) (anchorPermutation (permutation (58 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (58 : Fin 256))) = pairEncodedAt (blockIndex 6 (58 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_059 :
    (∀ j : Fin 4, (anchorPermutation (permutation (59 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (59 : Fin 256)) (anchorPermutation (permutation (59 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (59 : Fin 256))) = pairEncodedAt (blockIndex 6 (59 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_060 :
    (∀ j : Fin 4, (anchorPermutation (permutation (60 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (60 : Fin 256)) (anchorPermutation (permutation (60 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (60 : Fin 256))) = pairEncodedAt (blockIndex 6 (60 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_061 :
    (∀ j : Fin 4, (anchorPermutation (permutation (61 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (61 : Fin 256)) (anchorPermutation (permutation (61 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (61 : Fin 256))) = pairEncodedAt (blockIndex 6 (61 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_062 :
    (∀ j : Fin 4, (anchorPermutation (permutation (62 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (62 : Fin 256)) (anchorPermutation (permutation (62 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (62 : Fin 256))) = pairEncodedAt (blockIndex 6 (62 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

private theorem witness_063 :
    (∀ j : Fin 4, (anchorPermutation (permutation (63 : Fin 256)) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action (63 : Fin 256)) (anchorPermutation (permutation (63 : Fin 256)))
      (SizeTwo.Catalogue.Rows.state (orbit (63 : Fin 256))) = pairEncodedAt (blockIndex 6 (63 : Fin 256)) := by
  refine ⟨by decide, ?_⟩
  funext j
  fin_cases j <;> rfl

theorem witness_chunk_0 (r : Fin 64) :
    (∀ j : Fin 4, (anchorPermutation (permutation ⟨0 * 64 + r.val, by omega⟩) j).val < 2 ↔ j.val < 2) ∧
    transformedState (action ⟨0 * 64 + r.val, by omega⟩) (anchorPermutation (permutation ⟨0 * 64 + r.val, by omega⟩))
      (SizeTwo.Catalogue.Rows.state (orbit ⟨0 * 64 + r.val, by omega⟩)) = pairEncodedAt (blockIndex 6 ⟨0 * 64 + r.val, by omega⟩) := by
  fin_cases r
  · exact witness_000
  · exact witness_001
  · exact witness_002
  · exact witness_003
  · exact witness_004
  · exact witness_005
  · exact witness_006
  · exact witness_007
  · exact witness_008
  · exact witness_009
  · exact witness_010
  · exact witness_011
  · exact witness_012
  · exact witness_013
  · exact witness_014
  · exact witness_015
  · exact witness_016
  · exact witness_017
  · exact witness_018
  · exact witness_019
  · exact witness_020
  · exact witness_021
  · exact witness_022
  · exact witness_023
  · exact witness_024
  · exact witness_025
  · exact witness_026
  · exact witness_027
  · exact witness_028
  · exact witness_029
  · exact witness_030
  · exact witness_031
  · exact witness_032
  · exact witness_033
  · exact witness_034
  · exact witness_035
  · exact witness_036
  · exact witness_037
  · exact witness_038
  · exact witness_039
  · exact witness_040
  · exact witness_041
  · exact witness_042
  · exact witness_043
  · exact witness_044
  · exact witness_045
  · exact witness_046
  · exact witness_047
  · exact witness_048
  · exact witness_049
  · exact witness_050
  · exact witness_051
  · exact witness_052
  · exact witness_053
  · exact witness_054
  · exact witness_055
  · exact witness_056
  · exact witness_057
  · exact witness_058
  · exact witness_059
  · exact witness_060
  · exact witness_061
  · exact witness_062
  · exact witness_063
end Gallai.Certificate.SizeTwo.Coverage.Block06
