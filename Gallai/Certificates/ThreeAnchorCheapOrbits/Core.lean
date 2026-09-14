/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Mathlib.Tactic.FinCases

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def cheapCodes : List (Fin 1024) := [86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109, 110, 111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154, 155, 157, 158, 159, 164, 166, 167, 169, 171, 172, 173, 174, 181, 182, 183, 184, 185, 186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229, 230, 231, 232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 253, 254, 278, 279, 280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299, 301, 302, 303, 308, 309, 310, 313, 314, 315, 316, 318, 319, 326, 327, 328, 329, 331, 332, 333, 334, 338, 339, 344, 348, 352, 353, 355, 356, 363, 364, 366, 367, 368, 369, 370, 372, 376, 378, 379, 382, 388, 389, 391, 392, 394, 395, 397, 398, 399, 400, 401, 403, 404, 411, 412, 414, 415, 416, 418, 419, 423, 424, 428, 429, 431, 433, 434, 435, 436, 438, 439, 440, 441, 443, 444, 445, 446, 452, 453, 454, 457, 458, 459, 460, 462, 463, 464, 465, 466, 468, 472, 474, 475, 478, 481, 482, 483, 484, 486, 487, 488, 489, 491, 492, 493, 494, 496, 498, 499, 502, 504, 505, 506, 508, 532, 533, 535, 536, 538, 539, 541, 542, 543, 548, 550, 551, 553, 555, 556, 557, 558, 565, 566, 567, 568, 569, 570, 572, 573, 575, 580, 581, 583, 584, 586, 587, 589, 590, 591, 592, 593, 595, 596, 603, 604, 606, 607, 608, 610, 611, 615, 616, 620, 621, 623, 625, 626, 627, 628, 630, 631, 632, 633, 635, 636, 637, 638, 644, 646, 647, 649, 651, 652, 653, 654, 656, 658, 659, 663, 664, 668, 669, 671, 673, 675, 676, 684, 688, 689, 690, 692, 693, 695, 696, 701, 709, 710, 711, 712, 713, 714, 716, 717, 719, 721, 722, 723, 724, 726, 727, 728, 729, 731, 732, 733, 734, 736, 737, 738, 740, 741, 743, 744, 749, 752, 753, 755, 756, 757, 758, 761, 764, 788, 789, 790, 793, 794, 795, 796, 798, 799, 805, 806, 807, 808, 809, 810, 812, 813, 815, 820, 822, 823, 824, 825, 827, 829, 830, 836, 837, 838, 841, 842, 843, 844, 846, 847, 848, 849, 850, 852, 856, 858, 859, 862, 865, 866, 867, 868, 870, 871, 872, 873, 875, 876, 877, 878, 880, 882, 883, 886, 888, 889, 890, 892, 901, 902, 903, 904, 905, 906, 908, 909, 911, 913, 914, 915, 916, 918, 919, 920, 921, 923, 924, 925, 926, 928, 929, 930, 932, 933, 935, 936, 941, 944, 945, 947, 948, 949, 950, 953, 956, 964, 966, 967, 968, 969, 971, 973, 974, 976, 978, 979, 982, 984, 985, 986, 988, 992, 993, 995, 996, 997, 998, 1001, 1004, 1009, 1010, 1012, 1016]
/-- Exhaustive coverage of whole-deletion codes using all three anchors. -/
private theorem cheap_chunk_0 : ∀ r : Fin 32,
    (⟨0 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨0 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨0 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_1 : ∀ r : Fin 32,
    (⟨1 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨1 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨1 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_2 : ∀ r : Fin 32,
    (⟨2 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨2 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨2 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_3 : ∀ r : Fin 32,
    (⟨3 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨3 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨3 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_4 : ∀ r : Fin 32,
    (⟨4 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨4 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨4 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_5 : ∀ r : Fin 32,
    (⟨5 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨5 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨5 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_6 : ∀ r : Fin 32,
    (⟨6 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨6 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨6 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_7 : ∀ r : Fin 32,
    (⟨7 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨7 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨7 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_8 : ∀ r : Fin 32,
    (⟨8 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨8 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨8 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_9 : ∀ r : Fin 32,
    (⟨9 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨9 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨9 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_10 : ∀ r : Fin 32,
    (⟨10 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨10 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨10 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_11 : ∀ r : Fin 32,
    (⟨11 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨11 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨11 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_12 : ∀ r : Fin 32,
    (⟨12 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨12 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨12 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_13 : ∀ r : Fin 32,
    (⟨13 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨13 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨13 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_14 : ∀ r : Fin 32,
    (⟨14 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨14 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨14 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_15 : ∀ r : Fin 32,
    (⟨15 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨15 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨15 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_16 : ∀ r : Fin 32,
    (⟨16 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨16 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨16 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_17 : ∀ r : Fin 32,
    (⟨17 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨17 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨17 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_18 : ∀ r : Fin 32,
    (⟨18 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨18 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨18 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_19 : ∀ r : Fin 32,
    (⟨19 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨19 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨19 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_20 : ∀ r : Fin 32,
    (⟨20 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨20 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨20 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_21 : ∀ r : Fin 32,
    (⟨21 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨21 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨21 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_22 : ∀ r : Fin 32,
    (⟨22 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨22 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨22 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_23 : ∀ r : Fin 32,
    (⟨23 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨23 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨23 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_24 : ∀ r : Fin 32,
    (⟨24 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨24 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨24 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_25 : ∀ r : Fin 32,
    (⟨25 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨25 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨25 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_26 : ∀ r : Fin 32,
    (⟨26 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨26 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨26 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_27 : ∀ r : Fin 32,
    (⟨27 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨27 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨27 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_28 : ∀ r : Fin 32,
    (⟨28 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨28 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨28 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_29 : ∀ r : Fin 32,
    (⟨29 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨29 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨29 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_30 : ∀ r : Fin 32,
    (⟨30 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨30 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨30 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunk_31 : ∀ r : Fin 32,
    (⟨31 * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨31 * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨31 * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by decide

private theorem cheap_chunked (q r : Fin 32) :
    (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) i)).val.testBit j.val = true) →
    (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) ∈ cheapCodes := by
  fin_cases q
  · exact cheap_chunk_0 r
  · exact cheap_chunk_1 r
  · exact cheap_chunk_2 r
  · exact cheap_chunk_3 r
  · exact cheap_chunk_4 r
  · exact cheap_chunk_5 r
  · exact cheap_chunk_6 r
  · exact cheap_chunk_7 r
  · exact cheap_chunk_8 r
  · exact cheap_chunk_9 r
  · exact cheap_chunk_10 r
  · exact cheap_chunk_11 r
  · exact cheap_chunk_12 r
  · exact cheap_chunk_13 r
  · exact cheap_chunk_14 r
  · exact cheap_chunk_15 r
  · exact cheap_chunk_16 r
  · exact cheap_chunk_17 r
  · exact cheap_chunk_18 r
  · exact cheap_chunk_19 r
  · exact cheap_chunk_20 r
  · exact cheap_chunk_21 r
  · exact cheap_chunk_22 r
  · exact cheap_chunk_23 r
  · exact cheap_chunk_24 r
  · exact cheap_chunk_25 r
  · exact cheap_chunk_26 r
  · exact cheap_chunk_27 r
  · exact cheap_chunk_28 r
  · exact cheap_chunk_29 r
  · exact cheap_chunk_30 r
  · exact cheap_chunk_31 r

theorem cheap_coverage : ∀ n : Fin 1024, n ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode n i)).val.testBit j.val = true) →
    n ∈ cheapCodes := by
  intro n
  let q : Fin 32 := ⟨n.val / 32, by omega⟩
  let r : Fin 32 := ⟨n.val % 32, by omega⟩
  have h := cheap_chunked q r
  have heq : (⟨q.val * 32 + r.val, by omega⟩ : Fin 1024) = n := by
    apply Fin.ext
    dsimp [q, r]
    omega
  simpa only [heq] using h
end Gallai.Certificate.ThreeAnchor.CheapOrbits
