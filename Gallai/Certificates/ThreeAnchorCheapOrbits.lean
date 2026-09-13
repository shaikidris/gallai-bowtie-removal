/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def cheapCodes : List (Fin 1024) := [86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109, 110, 111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154, 155, 157, 158, 159, 164, 166, 167, 169, 171, 172, 173, 174, 181, 182, 183, 184, 185, 186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229, 230, 231, 232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 253, 254, 278, 279, 280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299, 301, 302, 303, 308, 309, 310, 313, 314, 315, 316, 318, 319, 326, 327, 328, 329, 331, 332, 333, 334, 338, 339, 344, 348, 352, 353, 355, 356, 363, 364, 366, 367, 368, 369, 370, 372, 376, 378, 379, 382, 388, 389, 391, 392, 394, 395, 397, 398, 399, 400, 401, 403, 404, 411, 412, 414, 415, 416, 418, 419, 423, 424, 428, 429, 431, 433, 434, 435, 436, 438, 439, 440, 441, 443, 444, 445, 446, 452, 453, 454, 457, 458, 459, 460, 462, 463, 464, 465, 466, 468, 472, 474, 475, 478, 481, 482, 483, 484, 486, 487, 488, 489, 491, 492, 493, 494, 496, 498, 499, 502, 504, 505, 506, 508, 532, 533, 535, 536, 538, 539, 541, 542, 543, 548, 550, 551, 553, 555, 556, 557, 558, 565, 566, 567, 568, 569, 570, 572, 573, 575, 580, 581, 583, 584, 586, 587, 589, 590, 591, 592, 593, 595, 596, 603, 604, 606, 607, 608, 610, 611, 615, 616, 620, 621, 623, 625, 626, 627, 628, 630, 631, 632, 633, 635, 636, 637, 638, 644, 646, 647, 649, 651, 652, 653, 654, 656, 658, 659, 663, 664, 668, 669, 671, 673, 675, 676, 684, 688, 689, 690, 692, 693, 695, 696, 701, 709, 710, 711, 712, 713, 714, 716, 717, 719, 721, 722, 723, 724, 726, 727, 728, 729, 731, 732, 733, 734, 736, 737, 738, 740, 741, 743, 744, 749, 752, 753, 755, 756, 757, 758, 761, 764, 788, 789, 790, 793, 794, 795, 796, 798, 799, 805, 806, 807, 808, 809, 810, 812, 813, 815, 820, 822, 823, 824, 825, 827, 829, 830, 836, 837, 838, 841, 842, 843, 844, 846, 847, 848, 849, 850, 852, 856, 858, 859, 862, 865, 866, 867, 868, 870, 871, 872, 873, 875, 876, 877, 878, 880, 882, 883, 886, 888, 889, 890, 892, 901, 902, 903, 904, 905, 906, 908, 909, 911, 913, 914, 915, 916, 918, 919, 920, 921, 923, 924, 925, 926, 928, 929, 930, 932, 933, 935, 936, 941, 944, 945, 947, 948, 949, 950, 953, 956, 964, 966, 967, 968, 969, 971, 973, 974, 976, 978, 979, 982, 984, 985, 986, 988, 992, 993, 995, 996, 997, 998, 1001, 1004, 1009, 1010, 1012, 1016]
/-- Exhaustive coverage of whole-deletion codes using all three anchors. -/
theorem cheap_coverage : ∀ n : Fin 1024, n ∈ syntheticCodes →
    (∀ j : Fin 3, ∃ i : Fin 5, (rowMask (decode n i)).val.testBit j.val = true) →
    n ∈ cheapCodes := by decide
def tails86 : List (List Vertex) := [[5, 3, 4, 0, 1, 2, 6, 7], [7, 0, 2, 5, 1, 6, 3]]
def added86 : List (List Vertex) := [[3, 0, 5]]
def attachments86 : Fin tails86.length → Fin 3 := ![0, 2]
theorem accepted86 : CheapOriginalAccepted (decode 86) 2 1
    tails86 added86 attachments86 := by decide
def tails87 : List (List Vertex) := [[6, 3, 4, 0, 1, 2, 5, 7], [7, 0, 2, 6, 1, 5, 3]]
def added87 : List (List Vertex) := [[3, 0, 6]]
def attachments87 : Fin tails87.length → Fin 3 := ![1, 2]
theorem accepted87 : CheapOriginalAccepted (decode 87) 2 0
    tails87 added87 attachments87 := by decide
def tails88 : List (List Vertex) := [[5, 7, 1, 2, 0, 4, 3, 6], [6, 2, 5, 1, 0, 3]]
def added88 : List (List Vertex) := [[3, 5]]
def attachments88 : Fin tails88.length → Fin 3 := ![0, 1]
theorem accepted88 : CheapOriginalAccepted (decode 88) 0 2
    tails88 added88 attachments88 := by decide
def tails89 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 3, 4], [6, 2, 5, 3, 0, 4]]
def added89 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments89 : Fin tails89.length → Fin 3 := ![0, 1]
theorem accepted89 : CheapOriginalAccepted (decode 89) 1 2
    tails89 added89 attachments89 := by decide
def tails91 : List (List Vertex) := [[6, 3, 4, 0, 2, 5, 1, 7], [7, 0, 1, 2, 6, 5, 3]]
def added91 : List (List Vertex) := [[3, 0, 6]]
def attachments91 : Fin tails91.length → Fin 3 := ![1, 2]
theorem accepted91 : CheapOriginalAccepted (decode 91) 1 0
    tails91 added91 attachments91 := by decide
def tails92 : List (List Vertex) := [[6, 7, 1, 2, 0, 4, 3, 5], [5, 2, 6, 1, 0, 3]]
def added92 : List (List Vertex) := [[3, 6]]
def attachments92 : Fin tails92.length → Fin 3 := ![1, 0]
theorem accepted92 : CheapOriginalAccepted (decode 92) 1 2
    tails92 added92 attachments92 := by decide
def tails93 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 3, 4], [5, 2, 6, 3, 0, 4]]
def added93 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments93 : Fin tails93.length → Fin 3 := ![1, 0]
theorem accepted93 : CheapOriginalAccepted (decode 93) 0 2
    tails93 added93 attachments93 := by decide
def tails94 : List (List Vertex) := [[5, 3, 4, 0, 2, 6, 1, 7], [7, 0, 1, 2, 5, 6, 3]]
def added94 : List (List Vertex) := [[3, 0, 5]]
def attachments94 : Fin tails94.length → Fin 3 := ![0, 2]
theorem accepted94 : CheapOriginalAccepted (decode 94) 0 1
    tails94 added94 attachments94 := by decide
def tails100 : List (List Vertex) := [[5, 7, 2, 1, 0, 4, 3, 6], [6, 1, 5, 2, 0, 3]]
def added100 : List (List Vertex) := [[3, 5]]
def attachments100 : Fin tails100.length → Fin 3 := ![0, 1]
theorem accepted100 : CheapOriginalAccepted (decode 100) 0 2
    tails100 added100 attachments100 := by decide
def tails101 : List (List Vertex) := [[5, 0, 1, 2, 7, 6, 3, 4], [6, 1, 5, 3, 0, 4]]
def added101 : List (List Vertex) := [[5, 2, 0, 6]]
def attachments101 : Fin tails101.length → Fin 3 := ![0, 1]
theorem accepted101 : CheapOriginalAccepted (decode 101) 1 2
    tails101 added101 attachments101 := by decide
def tails103 : List (List Vertex) := [[6, 3, 4, 0, 1, 5, 2, 7], [7, 0, 2, 1, 6, 5, 3]]
def added103 : List (List Vertex) := [[3, 0, 6]]
def attachments103 : Fin tails103.length → Fin 3 := ![1, 2]
theorem accepted103 : CheapOriginalAccepted (decode 103) 1 0
    tails103 added103 attachments103 := by decide
def tails104 : List (List Vertex) := [[5, 1, 7, 2, 0, 4, 3, 6], [6, 5, 2, 1, 0, 3]]
def added104 : List (List Vertex) := [[3, 5]]
def attachments104 : Fin tails104.length → Fin 3 := ![0, 1]
theorem accepted104 : CheapOriginalAccepted (decode 104) 0 1
    tails104 added104 attachments104 := by decide
def tails106 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 3, 4], [7, 2, 5, 3, 0, 4]]
def added106 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments106 : Fin tails106.length → Fin 3 := ![0, 2]
theorem accepted106 : CheapOriginalAccepted (decode 106) 2 1
    tails106 added106 attachments106 := by decide
def tails107 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 5, 2, 0, 3, 6]]
def added107 : List (List Vertex) := [[4, 0, 1, 7]]
def attachments107 : Fin tails107.length → Fin 3 := ![1, 2]
theorem accepted107 : CheapOriginalAccepted (decode 107) 2 0
    tails107 added107 attachments107 := by decide
def tails109 : List (List Vertex) := [[6, 0, 1, 7, 2, 5, 3, 4], [5, 6, 1, 2, 0, 4]]
def added109 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments109 : Fin tails109.length → Fin 3 := ![1, 0]
theorem accepted109 : CheapOriginalAccepted (decode 109) 1 0
    tails109 added109 attachments109 := by decide
def tails110 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 5, 3, 0, 4]]
def added110 : List (List Vertex) := [[5, 2, 0, 1, 7]]
def attachments110 : Fin tails110.length → Fin 3 := ![0, 2]
theorem accepted110 : CheapOriginalAccepted (decode 110) 0 2
    tails110 added110 attachments110 := by decide
def tails111 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 3, 4], [7, 6, 3, 0, 4]]
def added111 : List (List Vertex) := [[6, 1, 0, 2, 7]]
def attachments111 : Fin tails111.length → Fin 3 := ![1, 2]
theorem accepted111 : CheapOriginalAccepted (decode 111) 1 2
    tails111 added111 attachments111 := by decide
def tails116 : List (List Vertex) := [[6, 7, 2, 1, 0, 4, 3, 5], [5, 1, 6, 2, 0, 3]]
def added116 : List (List Vertex) := [[3, 6]]
def attachments116 : Fin tails116.length → Fin 3 := ![1, 0]
theorem accepted116 : CheapOriginalAccepted (decode 116) 1 2
    tails116 added116 attachments116 := by decide
def tails117 : List (List Vertex) := [[6, 0, 1, 2, 7, 5, 3, 4], [5, 1, 6, 3, 0, 4]]
def added117 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments117 : Fin tails117.length → Fin 3 := ![1, 0]
theorem accepted117 : CheapOriginalAccepted (decode 117) 0 2
    tails117 added117 attachments117 := by decide
def tails118 : List (List Vertex) := [[5, 3, 4, 0, 1, 6, 2, 7], [7, 0, 2, 1, 5, 6, 3]]
def added118 : List (List Vertex) := [[3, 0, 5]]
def attachments118 : Fin tails118.length → Fin 3 := ![0, 2]
theorem accepted118 : CheapOriginalAccepted (decode 118) 0 1
    tails118 added118 attachments118 := by decide
def tails121 : List (List Vertex) := [[5, 0, 1, 7, 2, 6, 3, 4], [6, 5, 1, 2, 0, 4]]
def added121 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments121 : Fin tails121.length → Fin 3 := ![0, 1]
theorem accepted121 : CheapOriginalAccepted (decode 121) 0 1
    tails121 added121 attachments121 := by decide
def tails122 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 3, 4], [7, 5, 3, 0, 4]]
def added122 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments122 : Fin tails122.length → Fin 3 := ![0, 2]
theorem accepted122 : CheapOriginalAccepted (decode 122) 0 2
    tails122 added122 attachments122 := by decide
def tails123 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 6, 3, 0, 4]]
def added123 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments123 : Fin tails123.length → Fin 3 := ![1, 2]
theorem accepted123 : CheapOriginalAccepted (decode 123) 1 2
    tails123 added123 attachments123 := by decide
def tails124 : List (List Vertex) := [[6, 1, 7, 2, 0, 4, 3, 5], [5, 6, 2, 1, 0, 3]]
def added124 : List (List Vertex) := [[3, 6]]
def attachments124 : Fin tails124.length → Fin 3 := ![1, 0]
theorem accepted124 : CheapOriginalAccepted (decode 124) 1 0
    tails124 added124 attachments124 := by decide
def tails126 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 6, 2, 0, 3, 5]]
def added126 : List (List Vertex) := [[4, 0, 1, 7]]
def attachments126 : Fin tails126.length → Fin 3 := ![0, 2]
theorem accepted126 : CheapOriginalAccepted (decode 126) 2 1
    tails126 added126 attachments126 := by decide
def tails127 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 3, 4], [7, 2, 6, 3, 0, 4]]
def added127 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments127 : Fin tails127.length → Fin 3 := ![1, 2]
theorem accepted127 : CheapOriginalAccepted (decode 127) 2 0
    tails127 added127 attachments127 := by decide
def tails148 : List (List Vertex) := [[5, 1, 6, 2, 0, 4, 3, 7], [7, 5, 2, 1, 0, 3]]
def added148 : List (List Vertex) := [[3, 5]]
def attachments148 : Fin tails148.length → Fin 3 := ![0, 2]
theorem accepted148 : CheapOriginalAccepted (decode 148) 0 2
    tails148 added148 attachments148 := by decide
def tails149 : List (List Vertex) := [[5, 0, 2, 1, 6, 7, 3, 4], [6, 2, 5, 3, 0, 4]]
def added149 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments149 : Fin tails149.length → Fin 3 := ![0, 1]
theorem accepted149 : CheapOriginalAccepted (decode 149) 1 2
    tails149 added149 attachments149 := by decide
def tails151 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 5, 2, 0, 3, 7]]
def added151 : List (List Vertex) := [[4, 0, 1, 6]]
def attachments151 : Fin tails151.length → Fin 3 := ![2, 1]
theorem accepted151 : CheapOriginalAccepted (decode 151) 1 0
    tails151 added151 attachments151 := by decide
def tails152 : List (List Vertex) := [[5, 6, 2, 1, 0, 4, 3, 7], [7, 1, 5, 2, 0, 3]]
def added152 : List (List Vertex) := [[3, 5]]
def attachments152 : Fin tails152.length → Fin 3 := ![0, 2]
theorem accepted152 : CheapOriginalAccepted (decode 152) 0 1
    tails152 added152 attachments152 := by decide
def tails154 : List (List Vertex) := [[5, 0, 1, 2, 6, 7, 3, 4], [7, 1, 5, 3, 0, 4]]
def added154 : List (List Vertex) := [[5, 2, 0, 7]]
def attachments154 : Fin tails154.length → Fin 3 := ![0, 2]
theorem accepted154 : CheapOriginalAccepted (decode 154) 2 1
    tails154 added154 attachments154 := by decide
def tails155 : List (List Vertex) := [[7, 3, 4, 0, 1, 5, 2, 6], [6, 0, 2, 1, 7, 5, 3]]
def added155 : List (List Vertex) := [[3, 0, 7]]
def attachments155 : Fin tails155.length → Fin 3 := ![2, 1]
theorem accepted155 : CheapOriginalAccepted (decode 155) 2 0
    tails155 added155 attachments155 := by decide
def tails157 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 5, 3, 0, 4]]
def added157 : List (List Vertex) := [[5, 2, 0, 1, 6]]
def attachments157 : Fin tails157.length → Fin 3 := ![0, 1]
theorem accepted157 : CheapOriginalAccepted (decode 157) 0 1
    tails157 added157 attachments157 := by decide
def tails158 : List (List Vertex) := [[7, 0, 1, 6, 2, 5, 3, 4], [5, 7, 1, 2, 0, 4]]
def added158 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments158 : Fin tails158.length → Fin 3 := ![2, 0]
theorem accepted158 : CheapOriginalAccepted (decode 158) 2 0
    tails158 added158 attachments158 := by decide
def tails159 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 3, 4], [6, 7, 3, 0, 4]]
def added159 : List (List Vertex) := [[7, 1, 0, 2, 6]]
def attachments159 : Fin tails159.length → Fin 3 := ![2, 1]
theorem accepted159 : CheapOriginalAccepted (decode 159) 2 1
    tails159 added159 attachments159 := by decide
def tails164 : List (List Vertex) := [[5, 6, 1, 2, 0, 4, 3, 7], [7, 2, 5, 1, 0, 3]]
def added164 : List (List Vertex) := [[3, 5]]
def attachments164 : Fin tails164.length → Fin 3 := ![0, 2]
theorem accepted164 : CheapOriginalAccepted (decode 164) 0 1
    tails164 added164 attachments164 := by decide
def tails166 : List (List Vertex) := [[5, 0, 2, 1, 6, 7, 3, 4], [7, 2, 5, 3, 0, 4]]
def added166 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments166 : Fin tails166.length → Fin 3 := ![0, 2]
theorem accepted166 : CheapOriginalAccepted (decode 166) 2 1
    tails166 added166 attachments166 := by decide
def tails167 : List (List Vertex) := [[7, 3, 4, 0, 2, 5, 1, 6], [6, 0, 1, 2, 7, 5, 3]]
def added167 : List (List Vertex) := [[3, 0, 7]]
def attachments167 : Fin tails167.length → Fin 3 := ![2, 1]
theorem accepted167 : CheapOriginalAccepted (decode 167) 2 0
    tails167 added167 attachments167 := by decide
def tails169 : List (List Vertex) := [[5, 3, 4, 0, 1, 2, 7, 6], [6, 0, 2, 5, 1, 7, 3]]
def added169 : List (List Vertex) := [[3, 0, 5]]
def attachments169 : Fin tails169.length → Fin 3 := ![0, 1]
theorem accepted169 : CheapOriginalAccepted (decode 169) 1 2
    tails169 added169 attachments169 := by decide
def tails171 : List (List Vertex) := [[7, 3, 4, 0, 1, 2, 5, 6], [6, 0, 2, 7, 1, 5, 3]]
def added171 : List (List Vertex) := [[3, 0, 7]]
def attachments171 : Fin tails171.length → Fin 3 := ![2, 1]
theorem accepted171 : CheapOriginalAccepted (decode 171) 1 0
    tails171 added171 attachments171 := by decide
def tails172 : List (List Vertex) := [[7, 6, 1, 2, 0, 4, 3, 5], [5, 2, 7, 1, 0, 3]]
def added172 : List (List Vertex) := [[3, 7]]
def attachments172 : Fin tails172.length → Fin 3 := ![2, 0]
theorem accepted172 : CheapOriginalAccepted (decode 172) 2 1
    tails172 added172 attachments172 := by decide
def tails173 : List (List Vertex) := [[5, 3, 4, 0, 2, 7, 1, 6], [6, 0, 1, 2, 5, 7, 3]]
def added173 : List (List Vertex) := [[3, 0, 5]]
def attachments173 : Fin tails173.length → Fin 3 := ![0, 1]
theorem accepted173 : CheapOriginalAccepted (decode 173) 0 2
    tails173 added173 attachments173 := by decide
def tails174 : List (List Vertex) := [[7, 0, 2, 1, 6, 5, 3, 4], [5, 2, 7, 3, 0, 4]]
def added174 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments174 : Fin tails174.length → Fin 3 := ![2, 0]
theorem accepted174 : CheapOriginalAccepted (decode 174) 0 1
    tails174 added174 attachments174 := by decide
def tails181 : List (List Vertex) := [[5, 0, 6, 1, 2, 7, 3, 4], [6, 5, 3, 0, 4]]
def added181 : List (List Vertex) := [[5, 1, 0, 2, 6]]
def attachments181 : Fin tails181.length → Fin 3 := ![0, 1]
theorem accepted181 : CheapOriginalAccepted (decode 181) 0 1
    tails181 added181 attachments181 := by decide
def tails182 : List (List Vertex) := [[5, 0, 1, 6, 2, 7, 3, 4], [7, 5, 1, 2, 0, 4]]
def added182 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments182 : Fin tails182.length → Fin 3 := ![0, 2]
theorem accepted182 : CheapOriginalAccepted (decode 182) 0 2
    tails182 added182 attachments182 := by decide
def tails183 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 7, 3, 0, 4]]
def added183 : List (List Vertex) := [[7, 2, 0, 1, 6]]
def attachments183 : Fin tails183.length → Fin 3 := ![2, 1]
theorem accepted183 : CheapOriginalAccepted (decode 183) 2 1
    tails183 added183 attachments183 := by decide
def tails184 : List (List Vertex) := [[7, 6, 2, 1, 0, 4, 3, 5], [5, 1, 7, 2, 0, 3]]
def added184 : List (List Vertex) := [[3, 7]]
def attachments184 : Fin tails184.length → Fin 3 := ![2, 0]
theorem accepted184 : CheapOriginalAccepted (decode 184) 2 1
    tails184 added184 attachments184 := by decide
def tails185 : List (List Vertex) := [[5, 3, 4, 0, 1, 7, 2, 6], [6, 0, 2, 1, 5, 7, 3]]
def added185 : List (List Vertex) := [[3, 0, 5]]
def attachments185 : Fin tails185.length → Fin 3 := ![0, 1]
theorem accepted185 : CheapOriginalAccepted (decode 185) 0 2
    tails185 added185 attachments185 := by decide
def tails186 : List (List Vertex) := [[7, 0, 1, 2, 6, 5, 3, 4], [5, 1, 7, 3, 0, 4]]
def added186 : List (List Vertex) := [[7, 2, 0, 5]]
def attachments186 : Fin tails186.length → Fin 3 := ![2, 0]
theorem accepted186 : CheapOriginalAccepted (decode 186) 0 1
    tails186 added186 attachments186 := by decide
def tails188 : List (List Vertex) := [[7, 1, 6, 2, 0, 4, 3, 5], [5, 7, 2, 1, 0, 3]]
def added188 : List (List Vertex) := [[3, 7]]
def attachments188 : Fin tails188.length → Fin 3 := ![2, 0]
theorem accepted188 : CheapOriginalAccepted (decode 188) 2 0
    tails188 added188 attachments188 := by decide
def tails189 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 7, 2, 0, 3, 5]]
def added189 : List (List Vertex) := [[4, 0, 1, 6]]
def attachments189 : Fin tails189.length → Fin 3 := ![0, 1]
theorem accepted189 : CheapOriginalAccepted (decode 189) 1 2
    tails189 added189 attachments189 := by decide
def tails191 : List (List Vertex) := [[7, 0, 2, 1, 6, 5, 3, 4], [6, 2, 7, 3, 0, 4]]
def added191 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments191 : Fin tails191.length → Fin 3 := ![2, 1]
theorem accepted191 : CheapOriginalAccepted (decode 191) 1 0
    tails191 added191 attachments191 := by decide
def tails212 : List (List Vertex) := [[6, 1, 5, 2, 0, 4, 3, 7], [7, 6, 2, 1, 0, 3]]
def added212 : List (List Vertex) := [[3, 6]]
def attachments212 : Fin tails212.length → Fin 3 := ![1, 2]
theorem accepted212 : CheapOriginalAccepted (decode 212) 1 2
    tails212 added212 attachments212 := by decide
def tails213 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 3, 4], [5, 2, 6, 3, 0, 4]]
def added213 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments213 : Fin tails213.length → Fin 3 := ![1, 0]
theorem accepted213 : CheapOriginalAccepted (decode 213) 0 2
    tails213 added213 attachments213 := by decide
def tails214 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 6, 2, 0, 3, 7]]
def added214 : List (List Vertex) := [[4, 0, 1, 5]]
def attachments214 : Fin tails214.length → Fin 3 := ![2, 0]
theorem accepted214 : CheapOriginalAccepted (decode 214) 0 1
    tails214 added214 attachments214 := by decide
def tails217 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 3, 4], [5, 6, 3, 0, 4]]
def added217 : List (List Vertex) := [[6, 2, 0, 1, 5]]
def attachments217 : Fin tails217.length → Fin 3 := ![1, 0]
theorem accepted217 : CheapOriginalAccepted (decode 217) 1 0
    tails217 added217 attachments217 := by decide
def tails218 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 3, 4], [5, 7, 3, 0, 4]]
def added218 : List (List Vertex) := [[7, 1, 0, 2, 5]]
def attachments218 : Fin tails218.length → Fin 3 := ![2, 0]
theorem accepted218 : CheapOriginalAccepted (decode 218) 2 0
    tails218 added218 attachments218 := by decide
def tails219 : List (List Vertex) := [[7, 0, 1, 5, 2, 6, 3, 4], [6, 7, 1, 2, 0, 4]]
def added219 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments219 : Fin tails219.length → Fin 3 := ![2, 1]
theorem accepted219 : CheapOriginalAccepted (decode 219) 2 1
    tails219 added219 attachments219 := by decide
def tails220 : List (List Vertex) := [[6, 5, 2, 1, 0, 4, 3, 7], [7, 1, 6, 2, 0, 3]]
def added220 : List (List Vertex) := [[3, 6]]
def attachments220 : Fin tails220.length → Fin 3 := ![1, 2]
theorem accepted220 : CheapOriginalAccepted (decode 220) 1 0
    tails220 added220 attachments220 := by decide
def tails222 : List (List Vertex) := [[7, 3, 4, 0, 1, 6, 2, 5], [5, 0, 2, 1, 7, 6, 3]]
def added222 : List (List Vertex) := [[3, 0, 7]]
def attachments222 : Fin tails222.length → Fin 3 := ![2, 0]
theorem accepted222 : CheapOriginalAccepted (decode 222) 2 1
    tails222 added222 attachments222 := by decide
def tails223 : List (List Vertex) := [[6, 0, 1, 2, 5, 7, 3, 4], [7, 1, 6, 3, 0, 4]]
def added223 : List (List Vertex) := [[6, 2, 0, 7]]
def attachments223 : Fin tails223.length → Fin 3 := ![1, 2]
theorem accepted223 : CheapOriginalAccepted (decode 223) 2 0
    tails223 added223 attachments223 := by decide
def tails229 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 3, 4], [5, 6, 3, 0, 4]]
def added229 : List (List Vertex) := [[6, 1, 0, 2, 5]]
def attachments229 : Fin tails229.length → Fin 3 := ![1, 0]
theorem accepted229 : CheapOriginalAccepted (decode 229) 1 0
    tails229 added229 attachments229 := by decide
def tails230 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 7, 3, 0, 4]]
def added230 : List (List Vertex) := [[7, 2, 0, 1, 5]]
def attachments230 : Fin tails230.length → Fin 3 := ![2, 0]
theorem accepted230 : CheapOriginalAccepted (decode 230) 2 0
    tails230 added230 attachments230 := by decide
def tails231 : List (List Vertex) := [[6, 0, 1, 5, 2, 7, 3, 4], [7, 6, 1, 2, 0, 4]]
def added231 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments231 : Fin tails231.length → Fin 3 := ![1, 2]
theorem accepted231 : CheapOriginalAccepted (decode 231) 1 2
    tails231 added231 attachments231 := by decide
def tails232 : List (List Vertex) := [[7, 1, 5, 2, 0, 4, 3, 6], [6, 7, 2, 1, 0, 3]]
def added232 : List (List Vertex) := [[3, 7]]
def attachments232 : Fin tails232.length → Fin 3 := ![2, 1]
theorem accepted232 : CheapOriginalAccepted (decode 232) 2 1
    tails232 added232 attachments232 := by decide
def tails233 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 3, 4], [5, 7, 2, 0, 3, 6]]
def added233 : List (List Vertex) := [[4, 0, 1, 5]]
def attachments233 : Fin tails233.length → Fin 3 := ![1, 0]
theorem accepted233 : CheapOriginalAccepted (decode 233) 0 2
    tails233 added233 attachments233 := by decide
def tails234 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 3, 4], [5, 2, 7, 3, 0, 4]]
def added234 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments234 : Fin tails234.length → Fin 3 := ![2, 0]
theorem accepted234 : CheapOriginalAccepted (decode 234) 0 1
    tails234 added234 attachments234 := by decide
def tails236 : List (List Vertex) := [[7, 5, 2, 1, 0, 4, 3, 6], [6, 1, 7, 2, 0, 3]]
def added236 : List (List Vertex) := [[3, 7]]
def attachments236 : Fin tails236.length → Fin 3 := ![2, 1]
theorem accepted236 : CheapOriginalAccepted (decode 236) 2 0
    tails236 added236 attachments236 := by decide
def tails237 : List (List Vertex) := [[6, 3, 4, 0, 1, 7, 2, 5], [5, 0, 2, 1, 6, 7, 3]]
def added237 : List (List Vertex) := [[3, 0, 6]]
def attachments237 : Fin tails237.length → Fin 3 := ![1, 0]
theorem accepted237 : CheapOriginalAccepted (decode 237) 1 2
    tails237 added237 attachments237 := by decide
def tails239 : List (List Vertex) := [[7, 0, 1, 2, 5, 6, 3, 4], [6, 1, 7, 3, 0, 4]]
def added239 : List (List Vertex) := [[7, 2, 0, 6]]
def attachments239 : Fin tails239.length → Fin 3 := ![2, 1]
theorem accepted239 : CheapOriginalAccepted (decode 239) 1 0
    tails239 added239 attachments239 := by decide
def tails244 : List (List Vertex) := [[6, 5, 1, 2, 0, 4, 3, 7], [7, 2, 6, 1, 0, 3]]
def added244 : List (List Vertex) := [[3, 6]]
def attachments244 : Fin tails244.length → Fin 3 := ![1, 2]
theorem accepted244 : CheapOriginalAccepted (decode 244) 1 0
    tails244 added244 attachments244 := by decide
def tails246 : List (List Vertex) := [[7, 3, 4, 0, 2, 6, 1, 5], [5, 0, 1, 2, 7, 6, 3]]
def added246 : List (List Vertex) := [[3, 0, 7]]
def attachments246 : Fin tails246.length → Fin 3 := ![2, 0]
theorem accepted246 : CheapOriginalAccepted (decode 246) 2 1
    tails246 added246 attachments246 := by decide
def tails247 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 3, 4], [7, 2, 6, 3, 0, 4]]
def added247 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments247 : Fin tails247.length → Fin 3 := ![1, 2]
theorem accepted247 : CheapOriginalAccepted (decode 247) 2 0
    tails247 added247 attachments247 := by decide
def tails248 : List (List Vertex) := [[7, 5, 1, 2, 0, 4, 3, 6], [6, 2, 7, 1, 0, 3]]
def added248 : List (List Vertex) := [[3, 7]]
def attachments248 : Fin tails248.length → Fin 3 := ![2, 1]
theorem accepted248 : CheapOriginalAccepted (decode 248) 2 0
    tails248 added248 attachments248 := by decide
def tails249 : List (List Vertex) := [[6, 3, 4, 0, 2, 7, 1, 5], [5, 0, 1, 2, 6, 7, 3]]
def added249 : List (List Vertex) := [[3, 0, 6]]
def attachments249 : Fin tails249.length → Fin 3 := ![1, 0]
theorem accepted249 : CheapOriginalAccepted (decode 249) 1 2
    tails249 added249 attachments249 := by decide
def tails251 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 3, 4], [6, 2, 7, 3, 0, 4]]
def added251 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments251 : Fin tails251.length → Fin 3 := ![2, 1]
theorem accepted251 : CheapOriginalAccepted (decode 251) 1 0
    tails251 added251 attachments251 := by decide
def tails253 : List (List Vertex) := [[6, 3, 4, 0, 1, 2, 7, 5], [5, 0, 2, 6, 1, 7, 3]]
def added253 : List (List Vertex) := [[3, 0, 6]]
def attachments253 : Fin tails253.length → Fin 3 := ![1, 0]
theorem accepted253 : CheapOriginalAccepted (decode 253) 0 2
    tails253 added253 attachments253 := by decide
def tails254 : List (List Vertex) := [[7, 3, 4, 0, 1, 2, 6, 5], [5, 0, 2, 7, 1, 6, 3]]
def added254 : List (List Vertex) := [[3, 0, 7]]
def attachments254 : Fin tails254.length → Fin 3 := ![2, 0]
theorem accepted254 : CheapOriginalAccepted (decode 254) 0 1
    tails254 added254 attachments254 := by decide
def tails278 : List (List Vertex) := [[5, 4, 3, 0, 1, 2, 6, 7], [7, 0, 2, 5, 1, 6, 4]]
def added278 : List (List Vertex) := [[4, 0, 5]]
def attachments278 : Fin tails278.length → Fin 3 := ![0, 2]
theorem accepted278 : CheapOriginalAccepted (decode 278) 2 1
    tails278 added278 attachments278 := by decide
def tails279 : List (List Vertex) := [[6, 4, 3, 0, 1, 2, 5, 7], [7, 0, 2, 6, 1, 5, 4]]
def added279 : List (List Vertex) := [[4, 0, 6]]
def attachments279 : Fin tails279.length → Fin 3 := ![1, 2]
theorem accepted279 : CheapOriginalAccepted (decode 279) 2 0
    tails279 added279 attachments279 := by decide
def tails280 : List (List Vertex) := [[5, 7, 1, 2, 0, 3, 4, 6], [6, 2, 5, 1, 0, 4]]
def added280 : List (List Vertex) := [[4, 5]]
def attachments280 : Fin tails280.length → Fin 3 := ![0, 1]
theorem accepted280 : CheapOriginalAccepted (decode 280) 0 2
    tails280 added280 attachments280 := by decide
def tails281 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 4, 3], [6, 2, 5, 4, 0, 3]]
def added281 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments281 : Fin tails281.length → Fin 3 := ![0, 1]
theorem accepted281 : CheapOriginalAccepted (decode 281) 1 2
    tails281 added281 attachments281 := by decide
def tails283 : List (List Vertex) := [[6, 4, 3, 0, 2, 5, 1, 7], [7, 0, 1, 2, 6, 5, 4]]
def added283 : List (List Vertex) := [[4, 0, 6]]
def attachments283 : Fin tails283.length → Fin 3 := ![1, 2]
theorem accepted283 : CheapOriginalAccepted (decode 283) 1 0
    tails283 added283 attachments283 := by decide
def tails284 : List (List Vertex) := [[6, 7, 1, 2, 0, 3, 4, 5], [5, 2, 6, 1, 0, 4]]
def added284 : List (List Vertex) := [[4, 6]]
def attachments284 : Fin tails284.length → Fin 3 := ![1, 0]
theorem accepted284 : CheapOriginalAccepted (decode 284) 1 2
    tails284 added284 attachments284 := by decide
def tails285 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 4, 3], [5, 2, 6, 4, 0, 3]]
def added285 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments285 : Fin tails285.length → Fin 3 := ![1, 0]
theorem accepted285 : CheapOriginalAccepted (decode 285) 0 2
    tails285 added285 attachments285 := by decide
def tails286 : List (List Vertex) := [[5, 4, 3, 0, 2, 6, 1, 7], [7, 0, 1, 2, 5, 6, 4]]
def added286 : List (List Vertex) := [[4, 0, 5]]
def attachments286 : Fin tails286.length → Fin 3 := ![0, 2]
theorem accepted286 : CheapOriginalAccepted (decode 286) 0 1
    tails286 added286 attachments286 := by decide
def tails292 : List (List Vertex) := [[5, 7, 2, 1, 0, 3, 4, 6], [6, 1, 5, 2, 0, 4]]
def added292 : List (List Vertex) := [[4, 5]]
def attachments292 : Fin tails292.length → Fin 3 := ![0, 1]
theorem accepted292 : CheapOriginalAccepted (decode 292) 0 2
    tails292 added292 attachments292 := by decide
def tails293 : List (List Vertex) := [[5, 0, 1, 2, 7, 6, 4, 3], [6, 1, 5, 4, 0, 3]]
def added293 : List (List Vertex) := [[5, 2, 0, 6]]
def attachments293 : Fin tails293.length → Fin 3 := ![0, 1]
theorem accepted293 : CheapOriginalAccepted (decode 293) 1 2
    tails293 added293 attachments293 := by decide
def tails295 : List (List Vertex) := [[6, 4, 3, 0, 1, 5, 2, 7], [7, 0, 2, 1, 6, 5, 4]]
def added295 : List (List Vertex) := [[4, 0, 6]]
def attachments295 : Fin tails295.length → Fin 3 := ![1, 2]
theorem accepted295 : CheapOriginalAccepted (decode 295) 1 0
    tails295 added295 attachments295 := by decide
def tails296 : List (List Vertex) := [[5, 1, 7, 2, 0, 3, 4, 6], [6, 5, 2, 1, 0, 4]]
def added296 : List (List Vertex) := [[4, 5]]
def attachments296 : Fin tails296.length → Fin 3 := ![0, 1]
theorem accepted296 : CheapOriginalAccepted (decode 296) 0 1
    tails296 added296 attachments296 := by decide
def tails298 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 4, 3], [7, 2, 5, 4, 0, 3]]
def added298 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments298 : Fin tails298.length → Fin 3 := ![0, 2]
theorem accepted298 : CheapOriginalAccepted (decode 298) 2 1
    tails298 added298 attachments298 := by decide
def tails299 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 5, 2, 0, 4, 6]]
def added299 : List (List Vertex) := [[3, 0, 1, 7]]
def attachments299 : Fin tails299.length → Fin 3 := ![1, 2]
theorem accepted299 : CheapOriginalAccepted (decode 299) 2 0
    tails299 added299 attachments299 := by decide
def tails301 : List (List Vertex) := [[6, 0, 1, 7, 2, 5, 4, 3], [5, 6, 1, 2, 0, 3]]
def added301 : List (List Vertex) := [[6, 4, 0, 5]]
def attachments301 : Fin tails301.length → Fin 3 := ![1, 0]
theorem accepted301 : CheapOriginalAccepted (decode 301) 1 0
    tails301 added301 attachments301 := by decide
def tails302 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 5, 4, 0, 3]]
def added302 : List (List Vertex) := [[5, 2, 0, 1, 7]]
def attachments302 : Fin tails302.length → Fin 3 := ![0, 2]
theorem accepted302 : CheapOriginalAccepted (decode 302) 0 2
    tails302 added302 attachments302 := by decide
def tails303 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 4, 3], [7, 6, 4, 0, 3]]
def added303 : List (List Vertex) := [[6, 1, 0, 2, 7]]
def attachments303 : Fin tails303.length → Fin 3 := ![1, 2]
theorem accepted303 : CheapOriginalAccepted (decode 303) 1 2
    tails303 added303 attachments303 := by decide
def tails308 : List (List Vertex) := [[6, 7, 2, 1, 0, 3, 4, 5], [5, 1, 6, 2, 0, 4]]
def added308 : List (List Vertex) := [[4, 6]]
def attachments308 : Fin tails308.length → Fin 3 := ![1, 0]
theorem accepted308 : CheapOriginalAccepted (decode 308) 1 2
    tails308 added308 attachments308 := by decide
def tails309 : List (List Vertex) := [[6, 0, 1, 2, 7, 5, 4, 3], [5, 1, 6, 4, 0, 3]]
def added309 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments309 : Fin tails309.length → Fin 3 := ![1, 0]
theorem accepted309 : CheapOriginalAccepted (decode 309) 0 2
    tails309 added309 attachments309 := by decide
def tails310 : List (List Vertex) := [[5, 4, 3, 0, 1, 6, 2, 7], [7, 0, 2, 1, 5, 6, 4]]
def added310 : List (List Vertex) := [[4, 0, 5]]
def attachments310 : Fin tails310.length → Fin 3 := ![0, 2]
theorem accepted310 : CheapOriginalAccepted (decode 310) 0 1
    tails310 added310 attachments310 := by decide
def tails313 : List (List Vertex) := [[5, 0, 1, 7, 2, 6, 4, 3], [6, 5, 1, 2, 0, 3]]
def added313 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments313 : Fin tails313.length → Fin 3 := ![0, 1]
theorem accepted313 : CheapOriginalAccepted (decode 313) 0 1
    tails313 added313 attachments313 := by decide
def tails314 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 4, 3], [7, 5, 4, 0, 3]]
def added314 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments314 : Fin tails314.length → Fin 3 := ![0, 2]
theorem accepted314 : CheapOriginalAccepted (decode 314) 0 2
    tails314 added314 attachments314 := by decide
def tails315 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 6, 4, 0, 3]]
def added315 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments315 : Fin tails315.length → Fin 3 := ![1, 2]
theorem accepted315 : CheapOriginalAccepted (decode 315) 1 2
    tails315 added315 attachments315 := by decide
def tails316 : List (List Vertex) := [[6, 1, 7, 2, 0, 3, 4, 5], [5, 6, 2, 1, 0, 4]]
def added316 : List (List Vertex) := [[4, 6]]
def attachments316 : Fin tails316.length → Fin 3 := ![1, 0]
theorem accepted316 : CheapOriginalAccepted (decode 316) 1 0
    tails316 added316 attachments316 := by decide
def tails318 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 6, 2, 0, 4, 5]]
def added318 : List (List Vertex) := [[3, 0, 1, 7]]
def attachments318 : Fin tails318.length → Fin 3 := ![0, 2]
theorem accepted318 : CheapOriginalAccepted (decode 318) 2 1
    tails318 added318 attachments318 := by decide
def tails319 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 4, 3], [7, 2, 6, 4, 0, 3]]
def added319 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments319 : Fin tails319.length → Fin 3 := ![1, 2]
theorem accepted319 : CheapOriginalAccepted (decode 319) 2 0
    tails319 added319 attachments319 := by decide
def tails326 : List (List Vertex) := [[5, 1, 2, 0, 3, 4, 6, 7], [7, 0, 4, 5, 3, 6, 1]]
def added326 : List (List Vertex) := [[1, 0, 5]]
def attachments326 : Fin tails326.length → Fin 3 := ![0, 2]
theorem accepted326 : CheapOriginalAccepted (decode 326) 2 1
    tails326 added326 attachments326 := by decide
def tails327 : List (List Vertex) := [[6, 1, 2, 0, 3, 4, 5, 7], [7, 0, 4, 6, 3, 5, 1]]
def added327 : List (List Vertex) := [[1, 0, 6]]
def attachments327 : Fin tails327.length → Fin 3 := ![1, 2]
theorem accepted327 : CheapOriginalAccepted (decode 327) 2 0
    tails327 added327 attachments327 := by decide
def tails328 : List (List Vertex) := [[5, 3, 6, 4, 0, 2, 1, 7], [7, 5, 4, 3, 0, 1]]
def added328 : List (List Vertex) := [[1, 5]]
def attachments328 : Fin tails328.length → Fin 3 := ![0, 2]
theorem accepted328 : CheapOriginalAccepted (decode 328) 0 2
    tails328 added328 attachments328 := by decide
def tails329 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 1, 2], [6, 4, 5, 1, 0, 2]]
def added329 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments329 : Fin tails329.length → Fin 3 := ![0, 1]
theorem accepted329 : CheapOriginalAccepted (decode 329) 1 2
    tails329 added329 attachments329 := by decide
def tails331 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 5, 4, 0, 1, 7]]
def added331 : List (List Vertex) := [[2, 0, 3, 6]]
def attachments331 : Fin tails331.length → Fin 3 := ![2, 1]
theorem accepted331 : CheapOriginalAccepted (decode 331) 1 0
    tails331 added331 attachments331 := by decide
def tails332 : List (List Vertex) := [[6, 3, 5, 4, 0, 2, 1, 7], [7, 6, 4, 3, 0, 1]]
def added332 : List (List Vertex) := [[1, 6]]
def attachments332 : Fin tails332.length → Fin 3 := ![1, 2]
theorem accepted332 : CheapOriginalAccepted (decode 332) 1 2
    tails332 added332 attachments332 := by decide
def tails333 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 1, 2], [5, 4, 6, 1, 0, 2]]
def added333 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments333 : Fin tails333.length → Fin 3 := ![1, 0]
theorem accepted333 : CheapOriginalAccepted (decode 333) 0 2
    tails333 added333 attachments333 := by decide
def tails334 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 6, 4, 0, 1, 7]]
def added334 : List (List Vertex) := [[2, 0, 3, 5]]
def attachments334 : Fin tails334.length → Fin 3 := ![2, 0]
theorem accepted334 : CheapOriginalAccepted (decode 334) 0 1
    tails334 added334 attachments334 := by decide
def tails338 : List (List Vertex) := [[5, 2, 1, 0, 3, 4, 6, 7], [7, 0, 4, 5, 3, 6, 2]]
def added338 : List (List Vertex) := [[2, 0, 5]]
def attachments338 : Fin tails338.length → Fin 3 := ![0, 2]
theorem accepted338 : CheapOriginalAccepted (decode 338) 2 1
    tails338 added338 attachments338 := by decide
def tails339 : List (List Vertex) := [[6, 2, 1, 0, 3, 4, 5, 7], [7, 0, 4, 6, 3, 5, 2]]
def added339 : List (List Vertex) := [[2, 0, 6]]
def attachments339 : Fin tails339.length → Fin 3 := ![1, 2]
theorem accepted339 : CheapOriginalAccepted (decode 339) 2 0
    tails339 added339 attachments339 := by decide
def tails344 : List (List Vertex) := [[5, 2, 0, 1, 7, 6, 4, 3], [6, 2, 1, 5, 4, 0, 3]]
def added344 : List (List Vertex) := [[5, 3, 6]]
def attachments344 : Fin tails344.length → Fin 3 := ![0, 1]
theorem accepted344 : CheapOriginalAccepted (decode 344) 1 2
    tails344 added344 attachments344 := by decide
def tails348 : List (List Vertex) := [[6, 2, 0, 1, 7, 5, 4, 3], [5, 2, 1, 6, 4, 0, 3]]
def added348 : List (List Vertex) := [[6, 3, 5]]
def attachments348 : Fin tails348.length → Fin 3 := ![1, 0]
theorem accepted348 : CheapOriginalAccepted (decode 348) 0 2
    tails348 added348 attachments348 := by decide
def tails352 : List (List Vertex) := [[5, 3, 6, 4, 0, 1, 2, 7], [7, 5, 4, 3, 0, 2]]
def added352 : List (List Vertex) := [[2, 5]]
def attachments352 : Fin tails352.length → Fin 3 := ![0, 2]
theorem accepted352 : CheapOriginalAccepted (decode 352) 0 2
    tails352 added352 attachments352 := by decide
def tails353 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 2, 1], [6, 4, 5, 2, 0, 1]]
def added353 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments353 : Fin tails353.length → Fin 3 := ![0, 1]
theorem accepted353 : CheapOriginalAccepted (decode 353) 1 2
    tails353 added353 attachments353 := by decide
def tails355 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 5, 4, 0, 2, 7]]
def added355 : List (List Vertex) := [[1, 0, 3, 6]]
def attachments355 : Fin tails355.length → Fin 3 := ![2, 1]
theorem accepted355 : CheapOriginalAccepted (decode 355) 1 0
    tails355 added355 attachments355 := by decide
def tails356 : List (List Vertex) := [[5, 1, 0, 2, 7, 6, 4, 3], [6, 1, 2, 5, 4, 0, 3]]
def added356 : List (List Vertex) := [[5, 3, 6]]
def attachments356 : Fin tails356.length → Fin 3 := ![0, 1]
theorem accepted356 : CheapOriginalAccepted (decode 356) 1 2
    tails356 added356 attachments356 := by decide
def tails363 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 7, 2, 0, 4, 5, 1]]
def added363 : List (List Vertex) := [[7, 1, 0, 3, 6]]
def attachments363 : Fin tails363.length → Fin 3 := ![2, 1]
theorem accepted363 : CheapOriginalAccepted (decode 363) 2 1
    tails363 added363 attachments363 := by decide
def tails364 : List (List Vertex) := [[6, 5, 2, 7, 1, 0, 4, 3], [5, 4, 6, 1, 2, 0, 3]]
def added364 : List (List Vertex) := [[6, 3, 5]]
def attachments364 : Fin tails364.length → Fin 3 := ![1, 0]
theorem accepted364 : CheapOriginalAccepted (decode 364) 1 0
    tails364 added364 attachments364 := by decide
def tails366 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 3, 0, 4, 6, 7, 2]]
def added366 : List (List Vertex) := [[7, 1, 0, 2, 5]]
def attachments366 : Fin tails366.length → Fin 3 := ![2, 0]
theorem accepted366 : CheapOriginalAccepted (decode 366) 2 1
    tails366 added366 attachments366 := by decide
def tails367 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 3, 0, 4, 5, 7, 1]]
def added367 : List (List Vertex) := [[7, 2, 0, 1, 6]]
def attachments367 : Fin tails367.length → Fin 3 := ![2, 1]
theorem accepted367 : CheapOriginalAccepted (decode 367) 2 0
    tails367 added367 attachments367 := by decide
def tails368 : List (List Vertex) := [[6, 3, 5, 4, 0, 1, 2, 7], [7, 6, 4, 3, 0, 2]]
def added368 : List (List Vertex) := [[2, 6]]
def attachments368 : Fin tails368.length → Fin 3 := ![1, 2]
theorem accepted368 : CheapOriginalAccepted (decode 368) 1 2
    tails368 added368 attachments368 := by decide
def tails369 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 2, 1], [5, 4, 6, 2, 0, 1]]
def added369 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments369 : Fin tails369.length → Fin 3 := ![1, 0]
theorem accepted369 : CheapOriginalAccepted (decode 369) 0 2
    tails369 added369 attachments369 := by decide
def tails370 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 6, 4, 0, 2, 7]]
def added370 : List (List Vertex) := [[1, 0, 3, 5]]
def attachments370 : Fin tails370.length → Fin 3 := ![2, 0]
theorem accepted370 : CheapOriginalAccepted (decode 370) 0 1
    tails370 added370 attachments370 := by decide
def tails372 : List (List Vertex) := [[6, 1, 0, 2, 7, 5, 4, 3], [5, 1, 2, 6, 4, 0, 3]]
def added372 : List (List Vertex) := [[6, 3, 5]]
def attachments372 : Fin tails372.length → Fin 3 := ![1, 0]
theorem accepted372 : CheapOriginalAccepted (decode 372) 0 2
    tails372 added372 attachments372 := by decide
def tails376 : List (List Vertex) := [[5, 6, 2, 7, 1, 0, 4, 3], [6, 4, 5, 1, 2, 0, 3]]
def added376 : List (List Vertex) := [[5, 3, 6]]
def attachments376 : Fin tails376.length → Fin 3 := ![0, 1]
theorem accepted376 : CheapOriginalAccepted (decode 376) 0 1
    tails376 added376 attachments376 := by decide
def tails378 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 3, 0, 4, 6, 7, 1]]
def added378 : List (List Vertex) := [[7, 2, 0, 1, 5]]
def attachments378 : Fin tails378.length → Fin 3 := ![2, 0]
theorem accepted378 : CheapOriginalAccepted (decode 378) 2 1
    tails378 added378 attachments378 := by decide
def tails379 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 3, 0, 4, 5, 7, 2]]
def added379 : List (List Vertex) := [[7, 1, 0, 2, 6]]
def attachments379 : Fin tails379.length → Fin 3 := ![2, 1]
theorem accepted379 : CheapOriginalAccepted (decode 379) 2 0
    tails379 added379 attachments379 := by decide
def tails382 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 7, 2, 0, 4, 6, 1]]
def added382 : List (List Vertex) := [[7, 1, 0, 3, 5]]
def attachments382 : Fin tails382.length → Fin 3 := ![2, 0]
theorem accepted382 : CheapOriginalAccepted (decode 382) 2 0
    tails382 added382 attachments382 := by decide
def tails388 : List (List Vertex) := [[5, 7, 3, 4, 0, 2, 1, 6], [6, 4, 5, 3, 0, 1]]
def added388 : List (List Vertex) := [[1, 5]]
def attachments388 : Fin tails388.length → Fin 3 := ![0, 1]
theorem accepted388 : CheapOriginalAccepted (decode 388) 0 2
    tails388 added388 attachments388 := by decide
def tails389 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 1, 2], [6, 4, 5, 1, 0, 2]]
def added389 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments389 : Fin tails389.length → Fin 3 := ![0, 1]
theorem accepted389 : CheapOriginalAccepted (decode 389) 1 2
    tails389 added389 attachments389 := by decide
def tails391 : List (List Vertex) := [[6, 1, 2, 0, 4, 5, 3, 7], [7, 0, 3, 4, 6, 5, 1]]
def added391 : List (List Vertex) := [[1, 0, 6]]
def attachments391 : Fin tails391.length → Fin 3 := ![1, 2]
theorem accepted391 : CheapOriginalAccepted (decode 391) 1 0
    tails391 added391 attachments391 := by decide
def tails392 : List (List Vertex) := [[5, 6, 4, 3, 0, 2, 1, 7], [7, 3, 5, 4, 0, 1]]
def added392 : List (List Vertex) := [[1, 5]]
def attachments392 : Fin tails392.length → Fin 3 := ![0, 2]
theorem accepted392 : CheapOriginalAccepted (decode 392) 0 1
    tails392 added392 attachments392 := by decide
def tails394 : List (List Vertex) := [[5, 0, 3, 4, 6, 7, 1, 2], [7, 3, 5, 1, 0, 2]]
def added394 : List (List Vertex) := [[5, 4, 0, 7]]
def attachments394 : Fin tails394.length → Fin 3 := ![0, 2]
theorem accepted394 : CheapOriginalAccepted (decode 394) 2 1
    tails394 added394 attachments394 := by decide
def tails395 : List (List Vertex) := [[7, 1, 2, 0, 3, 5, 4, 6], [6, 0, 4, 3, 7, 5, 1]]
def added395 : List (List Vertex) := [[1, 0, 7]]
def attachments395 : Fin tails395.length → Fin 3 := ![2, 1]
theorem accepted395 : CheapOriginalAccepted (decode 395) 2 0
    tails395 added395 attachments395 := by decide
def tails397 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 6, 1, 0, 2]]
def added397 : List (List Vertex) := [[6, 4, 0, 3, 5]]
def attachments397 : Fin tails397.length → Fin 3 := ![1, 0]
theorem accepted397 : CheapOriginalAccepted (decode 397) 1 0
    tails397 added397 attachments397 := by decide
def tails398 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 1, 2], [5, 7, 1, 0, 2]]
def added398 : List (List Vertex) := [[7, 3, 0, 4, 5]]
def attachments398 : Fin tails398.length → Fin 3 := ![2, 0]
theorem accepted398 : CheapOriginalAccepted (decode 398) 2 0
    tails398 added398 attachments398 := by decide
def tails399 : List (List Vertex) := [[7, 0, 3, 5, 4, 6, 1, 2], [6, 7, 3, 4, 0, 2]]
def added399 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments399 : Fin tails399.length → Fin 3 := ![2, 1]
theorem accepted399 : CheapOriginalAccepted (decode 399) 2 1
    tails399 added399 attachments399 := by decide
def tails400 : List (List Vertex) := [[5, 7, 3, 4, 0, 1, 2, 6], [6, 4, 5, 3, 0, 2]]
def added400 : List (List Vertex) := [[2, 5]]
def attachments400 : Fin tails400.length → Fin 3 := ![0, 1]
theorem accepted400 : CheapOriginalAccepted (decode 400) 0 2
    tails400 added400 attachments400 := by decide
def tails401 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 2, 1], [6, 4, 5, 2, 0, 1]]
def added401 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments401 : Fin tails401.length → Fin 3 := ![0, 1]
theorem accepted401 : CheapOriginalAccepted (decode 401) 1 2
    tails401 added401 attachments401 := by decide
def tails403 : List (List Vertex) := [[6, 2, 1, 0, 4, 5, 3, 7], [7, 0, 3, 4, 6, 5, 2]]
def added403 : List (List Vertex) := [[2, 0, 6]]
def attachments403 : Fin tails403.length → Fin 3 := ![1, 2]
theorem accepted403 : CheapOriginalAccepted (decode 403) 1 0
    tails403 added403 attachments403 := by decide
def tails404 : List (List Vertex) := [[5, 4, 0, 3, 7, 6, 2, 1], [6, 4, 3, 5, 2, 0, 1]]
def added404 : List (List Vertex) := [[5, 1, 6]]
def attachments404 : Fin tails404.length → Fin 3 := ![0, 1]
theorem accepted404 : CheapOriginalAccepted (decode 404) 1 2
    tails404 added404 attachments404 := by decide
def tails411 : List (List Vertex) := [[7, 0, 3, 5, 4, 6, 2, 1], [6, 7, 3, 4, 0, 2, 5, 1]]
def added411 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments411 : Fin tails411.length → Fin 3 := ![2, 1]
theorem accepted411 : CheapOriginalAccepted (decode 411) 2 1
    tails411 added411 attachments411 := by decide
def tails412 : List (List Vertex) := [[6, 5, 4, 0, 3, 7, 1, 2], [5, 3, 4, 6, 1, 0, 2]]
def added412 : List (List Vertex) := [[6, 2, 5]]
def attachments412 : Fin tails412.length → Fin 3 := ![1, 0]
theorem accepted412 : CheapOriginalAccepted (decode 412) 1 0
    tails412 added412 attachments412 := by decide
def tails414 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 4, 3], [7, 6, 1, 0, 4, 5, 3]]
def added414 : List (List Vertex) := [[5, 2, 0, 3, 7]]
def attachments414 : Fin tails414.length → Fin 3 := ![0, 2]
theorem accepted414 : CheapOriginalAccepted (decode 414) 2 1
    tails414 added414 attachments414 := by decide
def tails415 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 2, 1], [7, 5, 3, 0, 2, 6, 1]]
def added415 : List (List Vertex) := [[6, 4, 0, 1, 7]]
def attachments415 : Fin tails415.length → Fin 3 := ![1, 2]
theorem accepted415 : CheapOriginalAccepted (decode 415) 2 0
    tails415 added415 attachments415 := by decide
def tails416 : List (List Vertex) := [[5, 6, 4, 3, 0, 1, 2, 7], [7, 3, 5, 4, 0, 2]]
def added416 : List (List Vertex) := [[2, 5]]
def attachments416 : Fin tails416.length → Fin 3 := ![0, 2]
theorem accepted416 : CheapOriginalAccepted (decode 416) 0 1
    tails416 added416 attachments416 := by decide
def tails418 : List (List Vertex) := [[5, 0, 3, 4, 6, 7, 2, 1], [7, 3, 5, 2, 0, 1]]
def added418 : List (List Vertex) := [[5, 4, 0, 7]]
def attachments418 : Fin tails418.length → Fin 3 := ![0, 2]
theorem accepted418 : CheapOriginalAccepted (decode 418) 2 1
    tails418 added418 attachments418 := by decide
def tails419 : List (List Vertex) := [[7, 2, 1, 0, 3, 5, 4, 6], [6, 0, 4, 3, 7, 5, 2]]
def added419 : List (List Vertex) := [[2, 0, 7]]
def attachments419 : Fin tails419.length → Fin 3 := ![2, 1]
theorem accepted419 : CheapOriginalAccepted (decode 419) 2 0
    tails419 added419 attachments419 := by decide
def tails423 : List (List Vertex) := [[6, 0, 4, 5, 3, 7, 2, 1], [7, 6, 4, 3, 0, 2, 5, 1]]
def added423 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments423 : Fin tails423.length → Fin 3 := ![1, 2]
theorem accepted423 : CheapOriginalAccepted (decode 423) 1 2
    tails423 added423 attachments423 := by decide
def tails424 : List (List Vertex) := [[5, 3, 0, 4, 6, 7, 2, 1], [7, 3, 4, 5, 2, 0, 1]]
def added424 : List (List Vertex) := [[5, 1, 7]]
def attachments424 : Fin tails424.length → Fin 3 := ![0, 2]
theorem accepted424 : CheapOriginalAccepted (decode 424) 2 1
    tails424 added424 attachments424 := by decide
def tails428 : List (List Vertex) := [[7, 5, 3, 0, 4, 6, 1, 2], [5, 4, 3, 7, 1, 0, 2]]
def added428 : List (List Vertex) := [[7, 2, 5]]
def attachments428 : Fin tails428.length → Fin 3 := ![2, 0]
theorem accepted428 : CheapOriginalAccepted (decode 428) 2 0
    tails428 added428 attachments428 := by decide
def tails429 : List (List Vertex) := [[5, 0, 6, 1, 2, 7, 3, 4], [6, 7, 1, 0, 3, 5, 4]]
def added429 : List (List Vertex) := [[5, 2, 0, 4, 6]]
def attachments429 : Fin tails429.length → Fin 3 := ![0, 1]
theorem accepted429 : CheapOriginalAccepted (decode 429) 1 2
    tails429 added429 attachments429 := by decide
def tails431 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 5, 4, 0, 2, 7, 1]]
def added431 : List (List Vertex) := [[7, 3, 0, 1, 6]]
def attachments431 : Fin tails431.length → Fin 3 := ![2, 1]
theorem accepted431 : CheapOriginalAccepted (decode 431) 1 0
    tails431 added431 attachments431 := by decide
def tails433 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 6, 2, 0, 1]]
def added433 : List (List Vertex) := [[6, 4, 0, 3, 5]]
def attachments433 : Fin tails433.length → Fin 3 := ![1, 0]
theorem accepted433 : CheapOriginalAccepted (decode 433) 1 0
    tails433 added433 attachments433 := by decide
def tails434 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 2, 1], [5, 7, 2, 0, 1]]
def added434 : List (List Vertex) := [[7, 3, 0, 4, 5]]
def attachments434 : Fin tails434.length → Fin 3 := ![2, 0]
theorem accepted434 : CheapOriginalAccepted (decode 434) 2 0
    tails434 added434 attachments434 := by decide
def tails435 : List (List Vertex) := [[7, 0, 3, 5, 4, 6, 2, 1], [6, 7, 3, 4, 0, 1]]
def added435 : List (List Vertex) := [[7, 2, 0, 6]]
def attachments435 : Fin tails435.length → Fin 3 := ![2, 1]
theorem accepted435 : CheapOriginalAccepted (decode 435) 2 1
    tails435 added435 attachments435 := by decide
def tails436 : List (List Vertex) := [[6, 5, 4, 0, 3, 7, 2, 1], [5, 3, 4, 6, 2, 0, 1]]
def added436 : List (List Vertex) := [[6, 1, 5]]
def attachments436 : Fin tails436.length → Fin 3 := ![1, 0]
theorem accepted436 : CheapOriginalAccepted (decode 436) 1 0
    tails436 added436 attachments436 := by decide
def tails438 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 6, 2, 0, 4, 5, 3]]
def added438 : List (List Vertex) := [[5, 1, 0, 3, 7]]
def attachments438 : Fin tails438.length → Fin 3 := ![0, 2]
theorem accepted438 : CheapOriginalAccepted (decode 438) 2 1
    tails438 added438 attachments438 := by decide
def tails439 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 1, 2], [7, 5, 3, 0, 1, 6, 2]]
def added439 : List (List Vertex) := [[6, 4, 0, 2, 7]]
def attachments439 : Fin tails439.length → Fin 3 := ![1, 2]
theorem accepted439 : CheapOriginalAccepted (decode 439) 2 0
    tails439 added439 attachments439 := by decide
def tails440 : List (List Vertex) := [[7, 5, 3, 0, 4, 6, 2, 1], [5, 4, 3, 7, 2, 0, 1]]
def added440 : List (List Vertex) := [[7, 1, 5]]
def attachments440 : Fin tails440.length → Fin 3 := ![2, 0]
theorem accepted440 : CheapOriginalAccepted (decode 440) 2 0
    tails440 added440 attachments440 := by decide
def tails441 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 7, 2, 0, 3, 5, 4]]
def added441 : List (List Vertex) := [[5, 1, 0, 4, 6]]
def attachments441 : Fin tails441.length → Fin 3 := ![0, 1]
theorem accepted441 : CheapOriginalAccepted (decode 441) 1 2
    tails441 added441 attachments441 := by decide
def tails443 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 5, 4, 0, 1, 7, 2]]
def added443 : List (List Vertex) := [[7, 3, 0, 2, 6]]
def attachments443 : Fin tails443.length → Fin 3 := ![2, 1]
theorem accepted443 : CheapOriginalAccepted (decode 443) 1 0
    tails443 added443 attachments443 := by decide
def tails444 : List (List Vertex) := [[7, 6, 4, 5, 3, 0, 2, 1], [6, 2, 7, 3, 4, 0, 1]]
def added444 : List (List Vertex) := [[7, 1, 6]]
def attachments444 : Fin tails444.length → Fin 3 := ![2, 1]
theorem accepted444 : CheapOriginalAccepted (decode 444) 2 1
    tails444 added444 attachments444 := by decide
def tails445 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 1, 0, 2, 7, 5, 4]]
def added445 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments445 : Fin tails445.length → Fin 3 := ![0, 1]
theorem accepted445 : CheapOriginalAccepted (decode 445) 0 2
    tails445 added445 attachments445 := by decide
def tails446 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 1, 0, 2, 6, 5, 3]]
def added446 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments446 : Fin tails446.length → Fin 3 := ![0, 2]
theorem accepted446 : CheapOriginalAccepted (decode 446) 0 1
    tails446 added446 attachments446 := by decide
def tails452 : List (List Vertex) := [[6, 7, 3, 4, 0, 2, 1, 5], [5, 4, 6, 3, 0, 1]]
def added452 : List (List Vertex) := [[1, 6]]
def attachments452 : Fin tails452.length → Fin 3 := ![1, 0]
theorem accepted452 : CheapOriginalAccepted (decode 452) 1 2
    tails452 added452 attachments452 := by decide
def tails453 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 1, 2], [5, 4, 6, 1, 0, 2]]
def added453 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments453 : Fin tails453.length → Fin 3 := ![1, 0]
theorem accepted453 : CheapOriginalAccepted (decode 453) 0 2
    tails453 added453 attachments453 := by decide
def tails454 : List (List Vertex) := [[5, 1, 2, 0, 4, 6, 3, 7], [7, 0, 3, 4, 5, 6, 1]]
def added454 : List (List Vertex) := [[1, 0, 5]]
def attachments454 : Fin tails454.length → Fin 3 := ![0, 2]
theorem accepted454 : CheapOriginalAccepted (decode 454) 0 1
    tails454 added454 attachments454 := by decide
def tails457 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 5, 1, 0, 2]]
def added457 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments457 : Fin tails457.length → Fin 3 := ![0, 1]
theorem accepted457 : CheapOriginalAccepted (decode 457) 0 1
    tails457 added457 attachments457 := by decide
def tails458 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 1, 2], [5, 7, 3, 4, 0, 2]]
def added458 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments458 : Fin tails458.length → Fin 3 := ![2, 0]
theorem accepted458 : CheapOriginalAccepted (decode 458) 2 0
    tails458 added458 attachments458 := by decide
def tails459 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 1, 2], [6, 7, 1, 0, 2]]
def added459 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments459 : Fin tails459.length → Fin 3 := ![2, 1]
theorem accepted459 : CheapOriginalAccepted (decode 459) 2 1
    tails459 added459 attachments459 := by decide
def tails460 : List (List Vertex) := [[6, 5, 4, 3, 0, 2, 1, 7], [7, 3, 6, 4, 0, 1]]
def added460 : List (List Vertex) := [[1, 6]]
def attachments460 : Fin tails460.length → Fin 3 := ![1, 2]
theorem accepted460 : CheapOriginalAccepted (decode 460) 1 0
    tails460 added460 attachments460 := by decide
def tails462 : List (List Vertex) := [[7, 1, 2, 0, 3, 6, 4, 5], [5, 0, 4, 3, 7, 6, 1]]
def added462 : List (List Vertex) := [[1, 0, 7]]
def attachments462 : Fin tails462.length → Fin 3 := ![2, 0]
theorem accepted462 : CheapOriginalAccepted (decode 462) 2 1
    tails462 added462 attachments462 := by decide
def tails463 : List (List Vertex) := [[6, 0, 3, 4, 5, 7, 1, 2], [7, 3, 6, 1, 0, 2]]
def added463 : List (List Vertex) := [[6, 4, 0, 7]]
def attachments463 : Fin tails463.length → Fin 3 := ![1, 2]
theorem accepted463 : CheapOriginalAccepted (decode 463) 2 0
    tails463 added463 attachments463 := by decide
def tails464 : List (List Vertex) := [[6, 7, 3, 4, 0, 1, 2, 5], [5, 4, 6, 3, 0, 2]]
def added464 : List (List Vertex) := [[2, 6]]
def attachments464 : Fin tails464.length → Fin 3 := ![1, 0]
theorem accepted464 : CheapOriginalAccepted (decode 464) 1 2
    tails464 added464 attachments464 := by decide
def tails465 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 2, 1], [5, 4, 6, 2, 0, 1]]
def added465 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments465 : Fin tails465.length → Fin 3 := ![1, 0]
theorem accepted465 : CheapOriginalAccepted (decode 465) 0 2
    tails465 added465 attachments465 := by decide
def tails466 : List (List Vertex) := [[5, 2, 1, 0, 4, 6, 3, 7], [7, 0, 3, 4, 5, 6, 2]]
def added466 : List (List Vertex) := [[2, 0, 5]]
def attachments466 : Fin tails466.length → Fin 3 := ![0, 2]
theorem accepted466 : CheapOriginalAccepted (decode 466) 0 1
    tails466 added466 attachments466 := by decide
def tails468 : List (List Vertex) := [[6, 4, 0, 3, 7, 5, 2, 1], [5, 4, 3, 6, 2, 0, 1]]
def added468 : List (List Vertex) := [[6, 1, 5]]
def attachments468 : Fin tails468.length → Fin 3 := ![1, 0]
theorem accepted468 : CheapOriginalAccepted (decode 468) 0 2
    tails468 added468 attachments468 := by decide
def tails472 : List (List Vertex) := [[5, 6, 4, 0, 3, 7, 1, 2], [6, 3, 4, 5, 1, 0, 2]]
def added472 : List (List Vertex) := [[5, 2, 6]]
def attachments472 : Fin tails472.length → Fin 3 := ![0, 1]
theorem accepted472 : CheapOriginalAccepted (decode 472) 0 1
    tails472 added472 attachments472 := by decide
def tails474 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 2, 1], [7, 6, 3, 0, 2, 5, 1]]
def added474 : List (List Vertex) := [[5, 4, 0, 1, 7]]
def attachments474 : Fin tails474.length → Fin 3 := ![0, 2]
theorem accepted474 : CheapOriginalAccepted (decode 474) 2 1
    tails474 added474 attachments474 := by decide
def tails475 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 4, 3], [7, 5, 1, 0, 4, 6, 3]]
def added475 : List (List Vertex) := [[6, 2, 0, 3, 7]]
def attachments475 : Fin tails475.length → Fin 3 := ![1, 2]
theorem accepted475 : CheapOriginalAccepted (decode 475) 2 0
    tails475 added475 attachments475 := by decide
def tails478 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 2, 1], [5, 7, 3, 4, 0, 2, 6, 1]]
def added478 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments478 : Fin tails478.length → Fin 3 := ![2, 0]
theorem accepted478 : CheapOriginalAccepted (decode 478) 2 0
    tails478 added478 attachments478 := by decide
def tails481 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 5, 2, 0, 1]]
def added481 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments481 : Fin tails481.length → Fin 3 := ![0, 1]
theorem accepted481 : CheapOriginalAccepted (decode 481) 0 1
    tails481 added481 attachments481 := by decide
def tails482 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 2, 1], [5, 7, 3, 4, 0, 1]]
def added482 : List (List Vertex) := [[7, 2, 0, 5]]
def attachments482 : Fin tails482.length → Fin 3 := ![2, 0]
theorem accepted482 : CheapOriginalAccepted (decode 482) 2 0
    tails482 added482 attachments482 := by decide
def tails483 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 2, 1], [6, 7, 2, 0, 1]]
def added483 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments483 : Fin tails483.length → Fin 3 := ![2, 1]
theorem accepted483 : CheapOriginalAccepted (decode 483) 2 1
    tails483 added483 attachments483 := by decide
def tails484 : List (List Vertex) := [[5, 6, 4, 0, 3, 7, 2, 1], [6, 3, 4, 5, 2, 0, 1]]
def added484 : List (List Vertex) := [[5, 1, 6]]
def attachments484 : Fin tails484.length → Fin 3 := ![0, 1]
theorem accepted484 : CheapOriginalAccepted (decode 484) 0 1
    tails484 added484 attachments484 := by decide
def tails486 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 1, 2], [7, 6, 3, 0, 1, 5, 2]]
def added486 : List (List Vertex) := [[5, 4, 0, 2, 7]]
def attachments486 : Fin tails486.length → Fin 3 := ![0, 2]
theorem accepted486 : CheapOriginalAccepted (decode 486) 2 1
    tails486 added486 attachments486 := by decide
def tails487 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 5, 2, 0, 4, 6, 3]]
def added487 : List (List Vertex) := [[6, 1, 0, 3, 7]]
def attachments487 : Fin tails487.length → Fin 3 := ![1, 2]
theorem accepted487 : CheapOriginalAccepted (decode 487) 2 0
    tails487 added487 attachments487 := by decide
def tails488 : List (List Vertex) := [[7, 5, 4, 6, 3, 0, 2, 1], [5, 2, 7, 3, 4, 0, 1]]
def added488 : List (List Vertex) := [[7, 1, 5]]
def attachments488 : Fin tails488.length → Fin 3 := ![2, 0]
theorem accepted488 : CheapOriginalAccepted (decode 488) 2 0
    tails488 added488 attachments488 := by decide
def tails489 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 3, 4], [5, 1, 0, 2, 7, 6, 4]]
def added489 : List (List Vertex) := [[6, 3, 0, 4, 5]]
def attachments489 : Fin tails489.length → Fin 3 := ![1, 0]
theorem accepted489 : CheapOriginalAccepted (decode 489) 1 2
    tails489 added489 attachments489 := by decide
def tails491 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 1, 0, 2, 5, 6, 3]]
def added491 : List (List Vertex) := [[6, 4, 0, 3, 7]]
def attachments491 : Fin tails491.length → Fin 3 := ![1, 2]
theorem accepted491 : CheapOriginalAccepted (decode 491) 1 0
    tails491 added491 attachments491 := by decide
def tails492 : List (List Vertex) := [[7, 6, 3, 0, 4, 5, 2, 1], [6, 4, 3, 7, 2, 0, 1]]
def added492 : List (List Vertex) := [[7, 1, 6]]
def attachments492 : Fin tails492.length → Fin 3 := ![2, 1]
theorem accepted492 : CheapOriginalAccepted (decode 492) 2 1
    tails492 added492 attachments492 := by decide
def tails493 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 3, 4], [5, 7, 2, 0, 3, 6, 4]]
def added493 : List (List Vertex) := [[6, 1, 0, 4, 5]]
def attachments493 : Fin tails493.length → Fin 3 := ![1, 0]
theorem accepted493 : CheapOriginalAccepted (decode 493) 0 2
    tails493 added493 attachments493 := by decide
def tails494 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 6, 4, 0, 1, 7, 2]]
def added494 : List (List Vertex) := [[7, 3, 0, 2, 5]]
def attachments494 : Fin tails494.length → Fin 3 := ![2, 0]
theorem accepted494 : CheapOriginalAccepted (decode 494) 0 1
    tails494 added494 attachments494 := by decide
def tails496 : List (List Vertex) := [[6, 5, 4, 3, 0, 1, 2, 7], [7, 3, 6, 4, 0, 2]]
def added496 : List (List Vertex) := [[2, 6]]
def attachments496 : Fin tails496.length → Fin 3 := ![1, 2]
theorem accepted496 : CheapOriginalAccepted (decode 496) 1 0
    tails496 added496 attachments496 := by decide
def tails498 : List (List Vertex) := [[7, 2, 1, 0, 3, 6, 4, 5], [5, 0, 4, 3, 7, 6, 2]]
def added498 : List (List Vertex) := [[2, 0, 7]]
def attachments498 : Fin tails498.length → Fin 3 := ![2, 0]
theorem accepted498 : CheapOriginalAccepted (decode 498) 2 1
    tails498 added498 attachments498 := by decide
def tails499 : List (List Vertex) := [[6, 0, 3, 4, 5, 7, 2, 1], [7, 3, 6, 2, 0, 1]]
def added499 : List (List Vertex) := [[6, 4, 0, 7]]
def attachments499 : Fin tails499.length → Fin 3 := ![1, 2]
theorem accepted499 : CheapOriginalAccepted (decode 499) 2 0
    tails499 added499 attachments499 := by decide
def tails502 : List (List Vertex) := [[5, 0, 4, 6, 3, 7, 2, 1], [7, 5, 4, 3, 0, 2, 6, 1]]
def added502 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments502 : Fin tails502.length → Fin 3 := ![0, 2]
theorem accepted502 : CheapOriginalAccepted (decode 502) 0 2
    tails502 added502 attachments502 := by decide
def tails504 : List (List Vertex) := [[7, 6, 3, 0, 4, 5, 1, 2], [6, 4, 3, 7, 1, 0, 2]]
def added504 : List (List Vertex) := [[7, 2, 6]]
def attachments504 : Fin tails504.length → Fin 3 := ![2, 1]
theorem accepted504 : CheapOriginalAccepted (decode 504) 2 1
    tails504 added504 attachments504 := by decide
def tails505 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 3, 4], [5, 7, 1, 0, 3, 6, 4]]
def added505 : List (List Vertex) := [[6, 2, 0, 4, 5]]
def attachments505 : Fin tails505.length → Fin 3 := ![1, 0]
theorem accepted505 : CheapOriginalAccepted (decode 505) 0 2
    tails505 added505 attachments505 := by decide
def tails506 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 6, 4, 0, 2, 7, 1]]
def added506 : List (List Vertex) := [[7, 3, 0, 1, 5]]
def attachments506 : Fin tails506.length → Fin 3 := ![2, 0]
theorem accepted506 : CheapOriginalAccepted (decode 506) 0 1
    tails506 added506 attachments506 := by decide
def tails508 : List (List Vertex) := [[6, 3, 0, 4, 5, 7, 2, 1], [7, 3, 4, 6, 2, 0, 1]]
def added508 : List (List Vertex) := [[6, 1, 7]]
def attachments508 : Fin tails508.length → Fin 3 := ![1, 2]
theorem accepted508 : CheapOriginalAccepted (decode 508) 2 0
    tails508 added508 attachments508 := by decide
def tails532 : List (List Vertex) := [[5, 1, 6, 2, 0, 3, 4, 7], [7, 5, 2, 1, 0, 4]]
def added532 : List (List Vertex) := [[4, 5]]
def attachments532 : Fin tails532.length → Fin 3 := ![0, 2]
theorem accepted532 : CheapOriginalAccepted (decode 532) 0 2
    tails532 added532 attachments532 := by decide
def tails533 : List (List Vertex) := [[5, 0, 2, 1, 6, 7, 4, 3], [6, 2, 5, 4, 0, 3]]
def added533 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments533 : Fin tails533.length → Fin 3 := ![0, 1]
theorem accepted533 : CheapOriginalAccepted (decode 533) 1 2
    tails533 added533 attachments533 := by decide
def tails535 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 5, 2, 0, 4, 7]]
def added535 : List (List Vertex) := [[3, 0, 1, 6]]
def attachments535 : Fin tails535.length → Fin 3 := ![2, 1]
theorem accepted535 : CheapOriginalAccepted (decode 535) 1 0
    tails535 added535 attachments535 := by decide
def tails536 : List (List Vertex) := [[5, 6, 2, 1, 0, 3, 4, 7], [7, 1, 5, 2, 0, 4]]
def added536 : List (List Vertex) := [[4, 5]]
def attachments536 : Fin tails536.length → Fin 3 := ![0, 2]
theorem accepted536 : CheapOriginalAccepted (decode 536) 0 1
    tails536 added536 attachments536 := by decide
def tails538 : List (List Vertex) := [[5, 0, 1, 2, 6, 7, 4, 3], [7, 1, 5, 4, 0, 3]]
def added538 : List (List Vertex) := [[5, 2, 0, 7]]
def attachments538 : Fin tails538.length → Fin 3 := ![0, 2]
theorem accepted538 : CheapOriginalAccepted (decode 538) 2 1
    tails538 added538 attachments538 := by decide
def tails539 : List (List Vertex) := [[7, 4, 3, 0, 1, 5, 2, 6], [6, 0, 2, 1, 7, 5, 4]]
def added539 : List (List Vertex) := [[4, 0, 7]]
def attachments539 : Fin tails539.length → Fin 3 := ![2, 1]
theorem accepted539 : CheapOriginalAccepted (decode 539) 2 0
    tails539 added539 attachments539 := by decide
def tails541 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 5, 4, 0, 3]]
def added541 : List (List Vertex) := [[5, 2, 0, 1, 6]]
def attachments541 : Fin tails541.length → Fin 3 := ![0, 1]
theorem accepted541 : CheapOriginalAccepted (decode 541) 0 1
    tails541 added541 attachments541 := by decide
def tails542 : List (List Vertex) := [[7, 0, 1, 6, 2, 5, 4, 3], [5, 7, 1, 2, 0, 3]]
def added542 : List (List Vertex) := [[7, 4, 0, 5]]
def attachments542 : Fin tails542.length → Fin 3 := ![2, 0]
theorem accepted542 : CheapOriginalAccepted (decode 542) 2 0
    tails542 added542 attachments542 := by decide
def tails543 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 4, 3], [6, 7, 4, 0, 3]]
def added543 : List (List Vertex) := [[7, 1, 0, 2, 6]]
def attachments543 : Fin tails543.length → Fin 3 := ![2, 1]
theorem accepted543 : CheapOriginalAccepted (decode 543) 2 1
    tails543 added543 attachments543 := by decide
def tails548 : List (List Vertex) := [[5, 6, 1, 2, 0, 3, 4, 7], [7, 2, 5, 1, 0, 4]]
def added548 : List (List Vertex) := [[4, 5]]
def attachments548 : Fin tails548.length → Fin 3 := ![0, 2]
theorem accepted548 : CheapOriginalAccepted (decode 548) 0 1
    tails548 added548 attachments548 := by decide
def tails550 : List (List Vertex) := [[5, 0, 2, 1, 6, 7, 4, 3], [7, 2, 5, 4, 0, 3]]
def added550 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments550 : Fin tails550.length → Fin 3 := ![0, 2]
theorem accepted550 : CheapOriginalAccepted (decode 550) 2 1
    tails550 added550 attachments550 := by decide
def tails551 : List (List Vertex) := [[7, 4, 3, 0, 2, 5, 1, 6], [6, 0, 1, 2, 7, 5, 4]]
def added551 : List (List Vertex) := [[4, 0, 7]]
def attachments551 : Fin tails551.length → Fin 3 := ![2, 1]
theorem accepted551 : CheapOriginalAccepted (decode 551) 2 0
    tails551 added551 attachments551 := by decide
def tails553 : List (List Vertex) := [[5, 4, 3, 0, 1, 2, 7, 6], [6, 0, 2, 5, 1, 7, 4]]
def added553 : List (List Vertex) := [[4, 0, 5]]
def attachments553 : Fin tails553.length → Fin 3 := ![0, 1]
theorem accepted553 : CheapOriginalAccepted (decode 553) 1 2
    tails553 added553 attachments553 := by decide
def tails555 : List (List Vertex) := [[7, 4, 3, 0, 1, 2, 5, 6], [6, 0, 2, 7, 1, 5, 4]]
def added555 : List (List Vertex) := [[4, 0, 7]]
def attachments555 : Fin tails555.length → Fin 3 := ![2, 1]
theorem accepted555 : CheapOriginalAccepted (decode 555) 1 0
    tails555 added555 attachments555 := by decide
def tails556 : List (List Vertex) := [[7, 6, 1, 2, 0, 3, 4, 5], [5, 2, 7, 1, 0, 4]]
def added556 : List (List Vertex) := [[4, 7]]
def attachments556 : Fin tails556.length → Fin 3 := ![2, 0]
theorem accepted556 : CheapOriginalAccepted (decode 556) 2 1
    tails556 added556 attachments556 := by decide
def tails557 : List (List Vertex) := [[5, 4, 3, 0, 2, 7, 1, 6], [6, 0, 1, 2, 5, 7, 4]]
def added557 : List (List Vertex) := [[4, 0, 5]]
def attachments557 : Fin tails557.length → Fin 3 := ![0, 1]
theorem accepted557 : CheapOriginalAccepted (decode 557) 0 2
    tails557 added557 attachments557 := by decide
def tails558 : List (List Vertex) := [[7, 0, 2, 1, 6, 5, 4, 3], [5, 2, 7, 4, 0, 3]]
def added558 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments558 : Fin tails558.length → Fin 3 := ![2, 0]
theorem accepted558 : CheapOriginalAccepted (decode 558) 0 1
    tails558 added558 attachments558 := by decide
def tails565 : List (List Vertex) := [[5, 0, 6, 1, 2, 7, 4, 3], [6, 5, 4, 0, 3]]
def added565 : List (List Vertex) := [[5, 1, 0, 2, 6]]
def attachments565 : Fin tails565.length → Fin 3 := ![0, 1]
theorem accepted565 : CheapOriginalAccepted (decode 565) 0 1
    tails565 added565 attachments565 := by decide
def tails566 : List (List Vertex) := [[5, 0, 1, 6, 2, 7, 4, 3], [7, 5, 1, 2, 0, 3]]
def added566 : List (List Vertex) := [[5, 4, 0, 7]]
def attachments566 : Fin tails566.length → Fin 3 := ![0, 2]
theorem accepted566 : CheapOriginalAccepted (decode 566) 0 2
    tails566 added566 attachments566 := by decide
def tails567 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 7, 4, 0, 3]]
def added567 : List (List Vertex) := [[7, 2, 0, 1, 6]]
def attachments567 : Fin tails567.length → Fin 3 := ![2, 1]
theorem accepted567 : CheapOriginalAccepted (decode 567) 2 1
    tails567 added567 attachments567 := by decide
def tails568 : List (List Vertex) := [[7, 6, 2, 1, 0, 3, 4, 5], [5, 1, 7, 2, 0, 4]]
def added568 : List (List Vertex) := [[4, 7]]
def attachments568 : Fin tails568.length → Fin 3 := ![2, 0]
theorem accepted568 : CheapOriginalAccepted (decode 568) 2 1
    tails568 added568 attachments568 := by decide
def tails569 : List (List Vertex) := [[5, 4, 3, 0, 1, 7, 2, 6], [6, 0, 2, 1, 5, 7, 4]]
def added569 : List (List Vertex) := [[4, 0, 5]]
def attachments569 : Fin tails569.length → Fin 3 := ![0, 1]
theorem accepted569 : CheapOriginalAccepted (decode 569) 0 2
    tails569 added569 attachments569 := by decide
def tails570 : List (List Vertex) := [[7, 0, 1, 2, 6, 5, 4, 3], [5, 1, 7, 4, 0, 3]]
def added570 : List (List Vertex) := [[7, 2, 0, 5]]
def attachments570 : Fin tails570.length → Fin 3 := ![2, 0]
theorem accepted570 : CheapOriginalAccepted (decode 570) 0 1
    tails570 added570 attachments570 := by decide
def tails572 : List (List Vertex) := [[7, 1, 6, 2, 0, 3, 4, 5], [5, 7, 2, 1, 0, 4]]
def added572 : List (List Vertex) := [[4, 7]]
def attachments572 : Fin tails572.length → Fin 3 := ![2, 0]
theorem accepted572 : CheapOriginalAccepted (decode 572) 2 0
    tails572 added572 attachments572 := by decide
def tails573 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 7, 2, 0, 4, 5]]
def added573 : List (List Vertex) := [[3, 0, 1, 6]]
def attachments573 : Fin tails573.length → Fin 3 := ![0, 1]
theorem accepted573 : CheapOriginalAccepted (decode 573) 1 2
    tails573 added573 attachments573 := by decide
def tails575 : List (List Vertex) := [[7, 0, 2, 1, 6, 5, 4, 3], [6, 2, 7, 4, 0, 3]]
def added575 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments575 : Fin tails575.length → Fin 3 := ![2, 1]
theorem accepted575 : CheapOriginalAccepted (decode 575) 1 0
    tails575 added575 attachments575 := by decide
def tails580 : List (List Vertex) := [[5, 7, 4, 3, 0, 2, 1, 6], [6, 3, 5, 4, 0, 1]]
def added580 : List (List Vertex) := [[1, 5]]
def attachments580 : Fin tails580.length → Fin 3 := ![0, 1]
theorem accepted580 : CheapOriginalAccepted (decode 580) 0 2
    tails580 added580 attachments580 := by decide
def tails581 : List (List Vertex) := [[5, 0, 3, 4, 7, 6, 1, 2], [6, 3, 5, 1, 0, 2]]
def added581 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments581 : Fin tails581.length → Fin 3 := ![0, 1]
theorem accepted581 : CheapOriginalAccepted (decode 581) 1 2
    tails581 added581 attachments581 := by decide
def tails583 : List (List Vertex) := [[6, 1, 2, 0, 3, 5, 4, 7], [7, 0, 4, 3, 6, 5, 1]]
def added583 : List (List Vertex) := [[1, 0, 6]]
def attachments583 : Fin tails583.length → Fin 3 := ![1, 2]
theorem accepted583 : CheapOriginalAccepted (decode 583) 1 0
    tails583 added583 attachments583 := by decide
def tails584 : List (List Vertex) := [[5, 6, 3, 4, 0, 2, 1, 7], [7, 4, 5, 3, 0, 1]]
def added584 : List (List Vertex) := [[1, 5]]
def attachments584 : Fin tails584.length → Fin 3 := ![0, 2]
theorem accepted584 : CheapOriginalAccepted (decode 584) 0 1
    tails584 added584 attachments584 := by decide
def tails586 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 1, 2], [7, 4, 5, 1, 0, 2]]
def added586 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments586 : Fin tails586.length → Fin 3 := ![0, 2]
theorem accepted586 : CheapOriginalAccepted (decode 586) 2 1
    tails586 added586 attachments586 := by decide
def tails587 : List (List Vertex) := [[7, 1, 2, 0, 4, 5, 3, 6], [6, 0, 3, 4, 7, 5, 1]]
def added587 : List (List Vertex) := [[1, 0, 7]]
def attachments587 : Fin tails587.length → Fin 3 := ![2, 1]
theorem accepted587 : CheapOriginalAccepted (decode 587) 2 0
    tails587 added587 attachments587 := by decide
def tails589 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 1, 2], [5, 6, 1, 0, 2]]
def added589 : List (List Vertex) := [[6, 3, 0, 4, 5]]
def attachments589 : Fin tails589.length → Fin 3 := ![1, 0]
theorem accepted589 : CheapOriginalAccepted (decode 589) 1 0
    tails589 added589 attachments589 := by decide
def tails590 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 7, 1, 0, 2]]
def added590 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments590 : Fin tails590.length → Fin 3 := ![2, 0]
theorem accepted590 : CheapOriginalAccepted (decode 590) 2 0
    tails590 added590 attachments590 := by decide
def tails591 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 1, 2], [7, 6, 3, 4, 0, 2]]
def added591 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments591 : Fin tails591.length → Fin 3 := ![1, 2]
theorem accepted591 : CheapOriginalAccepted (decode 591) 1 2
    tails591 added591 attachments591 := by decide
def tails592 : List (List Vertex) := [[5, 7, 4, 3, 0, 1, 2, 6], [6, 3, 5, 4, 0, 2]]
def added592 : List (List Vertex) := [[2, 5]]
def attachments592 : Fin tails592.length → Fin 3 := ![0, 1]
theorem accepted592 : CheapOriginalAccepted (decode 592) 0 2
    tails592 added592 attachments592 := by decide
def tails593 : List (List Vertex) := [[5, 0, 3, 4, 7, 6, 2, 1], [6, 3, 5, 2, 0, 1]]
def added593 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments593 : Fin tails593.length → Fin 3 := ![0, 1]
theorem accepted593 : CheapOriginalAccepted (decode 593) 1 2
    tails593 added593 attachments593 := by decide
def tails595 : List (List Vertex) := [[6, 2, 1, 0, 3, 5, 4, 7], [7, 0, 4, 3, 6, 5, 2]]
def added595 : List (List Vertex) := [[2, 0, 6]]
def attachments595 : Fin tails595.length → Fin 3 := ![1, 2]
theorem accepted595 : CheapOriginalAccepted (decode 595) 1 0
    tails595 added595 attachments595 := by decide
def tails596 : List (List Vertex) := [[5, 3, 0, 4, 7, 6, 2, 1], [6, 3, 4, 5, 2, 0, 1]]
def added596 : List (List Vertex) := [[5, 1, 6]]
def attachments596 : Fin tails596.length → Fin 3 := ![0, 1]
theorem accepted596 : CheapOriginalAccepted (decode 596) 1 2
    tails596 added596 attachments596 := by decide
def tails603 : List (List Vertex) := [[7, 0, 4, 5, 3, 6, 2, 1], [6, 7, 4, 3, 0, 2, 5, 1]]
def added603 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments603 : Fin tails603.length → Fin 3 := ![2, 1]
theorem accepted603 : CheapOriginalAccepted (decode 603) 2 1
    tails603 added603 attachments603 := by decide
def tails604 : List (List Vertex) := [[6, 5, 3, 0, 4, 7, 1, 2], [5, 4, 3, 6, 1, 0, 2]]
def added604 : List (List Vertex) := [[6, 2, 5]]
def attachments604 : Fin tails604.length → Fin 3 := ![1, 0]
theorem accepted604 : CheapOriginalAccepted (decode 604) 1 0
    tails604 added604 attachments604 := by decide
def tails606 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 3, 4], [7, 6, 1, 0, 3, 5, 4]]
def added606 : List (List Vertex) := [[5, 2, 0, 4, 7]]
def attachments606 : Fin tails606.length → Fin 3 := ![0, 2]
theorem accepted606 : CheapOriginalAccepted (decode 606) 2 1
    tails606 added606 attachments606 := by decide
def tails607 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 5, 4, 0, 2, 6, 1]]
def added607 : List (List Vertex) := [[6, 3, 0, 1, 7]]
def attachments607 : Fin tails607.length → Fin 3 := ![1, 2]
theorem accepted607 : CheapOriginalAccepted (decode 607) 2 0
    tails607 added607 attachments607 := by decide
def tails608 : List (List Vertex) := [[5, 6, 3, 4, 0, 1, 2, 7], [7, 4, 5, 3, 0, 2]]
def added608 : List (List Vertex) := [[2, 5]]
def attachments608 : Fin tails608.length → Fin 3 := ![0, 2]
theorem accepted608 : CheapOriginalAccepted (decode 608) 0 1
    tails608 added608 attachments608 := by decide
def tails610 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 2, 1], [7, 4, 5, 2, 0, 1]]
def added610 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments610 : Fin tails610.length → Fin 3 := ![0, 2]
theorem accepted610 : CheapOriginalAccepted (decode 610) 2 1
    tails610 added610 attachments610 := by decide
def tails611 : List (List Vertex) := [[7, 2, 1, 0, 4, 5, 3, 6], [6, 0, 3, 4, 7, 5, 2]]
def added611 : List (List Vertex) := [[2, 0, 7]]
def attachments611 : Fin tails611.length → Fin 3 := ![2, 1]
theorem accepted611 : CheapOriginalAccepted (decode 611) 2 0
    tails611 added611 attachments611 := by decide
def tails615 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 2, 1], [7, 6, 3, 4, 0, 2, 5, 1]]
def added615 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments615 : Fin tails615.length → Fin 3 := ![1, 2]
theorem accepted615 : CheapOriginalAccepted (decode 615) 1 2
    tails615 added615 attachments615 := by decide
def tails616 : List (List Vertex) := [[5, 4, 0, 3, 6, 7, 2, 1], [7, 4, 3, 5, 2, 0, 1]]
def added616 : List (List Vertex) := [[5, 1, 7]]
def attachments616 : Fin tails616.length → Fin 3 := ![0, 2]
theorem accepted616 : CheapOriginalAccepted (decode 616) 2 1
    tails616 added616 attachments616 := by decide
def tails620 : List (List Vertex) := [[7, 5, 4, 0, 3, 6, 1, 2], [5, 3, 4, 7, 1, 0, 2]]
def added620 : List (List Vertex) := [[7, 2, 5]]
def attachments620 : Fin tails620.length → Fin 3 := ![2, 0]
theorem accepted620 : CheapOriginalAccepted (decode 620) 2 0
    tails620 added620 attachments620 := by decide
def tails621 : List (List Vertex) := [[5, 0, 6, 1, 2, 7, 4, 3], [6, 7, 1, 0, 4, 5, 3]]
def added621 : List (List Vertex) := [[5, 2, 0, 3, 6]]
def attachments621 : Fin tails621.length → Fin 3 := ![0, 1]
theorem accepted621 : CheapOriginalAccepted (decode 621) 1 2
    tails621 added621 attachments621 := by decide
def tails623 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 2, 1], [6, 5, 3, 0, 2, 7, 1]]
def added623 : List (List Vertex) := [[7, 4, 0, 1, 6]]
def attachments623 : Fin tails623.length → Fin 3 := ![2, 1]
theorem accepted623 : CheapOriginalAccepted (decode 623) 1 0
    tails623 added623 attachments623 := by decide
def tails625 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 2, 1], [5, 6, 2, 0, 1]]
def added625 : List (List Vertex) := [[6, 3, 0, 4, 5]]
def attachments625 : Fin tails625.length → Fin 3 := ![1, 0]
theorem accepted625 : CheapOriginalAccepted (decode 625) 1 0
    tails625 added625 attachments625 := by decide
def tails626 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 7, 2, 0, 1]]
def added626 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments626 : Fin tails626.length → Fin 3 := ![2, 0]
theorem accepted626 : CheapOriginalAccepted (decode 626) 2 0
    tails626 added626 attachments626 := by decide
def tails627 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 2, 1], [7, 6, 3, 4, 0, 1]]
def added627 : List (List Vertex) := [[6, 2, 0, 7]]
def attachments627 : Fin tails627.length → Fin 3 := ![1, 2]
theorem accepted627 : CheapOriginalAccepted (decode 627) 1 2
    tails627 added627 attachments627 := by decide
def tails628 : List (List Vertex) := [[6, 5, 3, 0, 4, 7, 2, 1], [5, 4, 3, 6, 2, 0, 1]]
def added628 : List (List Vertex) := [[6, 1, 5]]
def attachments628 : Fin tails628.length → Fin 3 := ![1, 0]
theorem accepted628 : CheapOriginalAccepted (decode 628) 1 0
    tails628 added628 attachments628 := by decide
def tails630 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 6, 2, 0, 3, 5, 4]]
def added630 : List (List Vertex) := [[5, 1, 0, 4, 7]]
def attachments630 : Fin tails630.length → Fin 3 := ![0, 2]
theorem accepted630 : CheapOriginalAccepted (decode 630) 2 1
    tails630 added630 attachments630 := by decide
def tails631 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 5, 4, 0, 1, 6, 2]]
def added631 : List (List Vertex) := [[6, 3, 0, 2, 7]]
def attachments631 : Fin tails631.length → Fin 3 := ![1, 2]
theorem accepted631 : CheapOriginalAccepted (decode 631) 2 0
    tails631 added631 attachments631 := by decide
def tails632 : List (List Vertex) := [[7, 5, 4, 0, 3, 6, 2, 1], [5, 3, 4, 7, 2, 0, 1]]
def added632 : List (List Vertex) := [[7, 1, 5]]
def attachments632 : Fin tails632.length → Fin 3 := ![2, 0]
theorem accepted632 : CheapOriginalAccepted (decode 632) 2 0
    tails632 added632 attachments632 := by decide
def tails633 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 7, 2, 0, 4, 5, 3]]
def added633 : List (List Vertex) := [[5, 1, 0, 3, 6]]
def attachments633 : Fin tails633.length → Fin 3 := ![0, 1]
theorem accepted633 : CheapOriginalAccepted (decode 633) 1 2
    tails633 added633 attachments633 := by decide
def tails635 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 1, 2], [6, 5, 3, 0, 1, 7, 2]]
def added635 : List (List Vertex) := [[7, 4, 0, 2, 6]]
def attachments635 : Fin tails635.length → Fin 3 := ![2, 1]
theorem accepted635 : CheapOriginalAccepted (decode 635) 1 0
    tails635 added635 attachments635 := by decide
def tails636 : List (List Vertex) := [[6, 7, 4, 5, 3, 0, 2, 1], [7, 2, 6, 3, 4, 0, 1]]
def added636 : List (List Vertex) := [[6, 1, 7]]
def attachments636 : Fin tails636.length → Fin 3 := ![1, 2]
theorem accepted636 : CheapOriginalAccepted (decode 636) 1 2
    tails636 added636 attachments636 := by decide
def tails637 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 1, 0, 2, 7, 5, 3]]
def added637 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments637 : Fin tails637.length → Fin 3 := ![0, 1]
theorem accepted637 : CheapOriginalAccepted (decode 637) 0 2
    tails637 added637 attachments637 := by decide
def tails638 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 1, 0, 2, 6, 5, 4]]
def added638 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments638 : Fin tails638.length → Fin 3 := ![0, 2]
theorem accepted638 : CheapOriginalAccepted (decode 638) 0 1
    tails638 added638 attachments638 := by decide
def tails644 : List (List Vertex) := [[5, 3, 7, 4, 0, 2, 1, 6], [6, 5, 4, 3, 0, 1]]
def added644 : List (List Vertex) := [[1, 5]]
def attachments644 : Fin tails644.length → Fin 3 := ![0, 1]
theorem accepted644 : CheapOriginalAccepted (decode 644) 0 1
    tails644 added644 attachments644 := by decide
def tails646 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 1, 2], [7, 4, 5, 1, 0, 2]]
def added646 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments646 : Fin tails646.length → Fin 3 := ![0, 2]
theorem accepted646 : CheapOriginalAccepted (decode 646) 2 1
    tails646 added646 attachments646 := by decide
def tails647 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 5, 4, 0, 1, 6]]
def added647 : List (List Vertex) := [[2, 0, 3, 7]]
def attachments647 : Fin tails647.length → Fin 3 := ![1, 2]
theorem accepted647 : CheapOriginalAccepted (decode 647) 2 0
    tails647 added647 attachments647 := by decide
def tails649 : List (List Vertex) := [[5, 1, 2, 0, 3, 4, 7, 6], [6, 0, 4, 5, 3, 7, 1]]
def added649 : List (List Vertex) := [[1, 0, 5]]
def attachments649 : Fin tails649.length → Fin 3 := ![0, 1]
theorem accepted649 : CheapOriginalAccepted (decode 649) 1 2
    tails649 added649 attachments649 := by decide
def tails651 : List (List Vertex) := [[7, 1, 2, 0, 3, 4, 5, 6], [6, 0, 4, 7, 3, 5, 1]]
def added651 : List (List Vertex) := [[1, 0, 7]]
def attachments651 : Fin tails651.length → Fin 3 := ![2, 1]
theorem accepted651 : CheapOriginalAccepted (decode 651) 1 0
    tails651 added651 attachments651 := by decide
def tails652 : List (List Vertex) := [[7, 3, 5, 4, 0, 2, 1, 6], [6, 7, 4, 3, 0, 1]]
def added652 : List (List Vertex) := [[1, 7]]
def attachments652 : Fin tails652.length → Fin 3 := ![2, 1]
theorem accepted652 : CheapOriginalAccepted (decode 652) 2 1
    tails652 added652 attachments652 := by decide
def tails653 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 7, 4, 0, 1, 6]]
def added653 : List (List Vertex) := [[2, 0, 3, 5]]
def attachments653 : Fin tails653.length → Fin 3 := ![1, 0]
theorem accepted653 : CheapOriginalAccepted (decode 653) 0 2
    tails653 added653 attachments653 := by decide
def tails654 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 1, 2], [5, 4, 7, 1, 0, 2]]
def added654 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments654 : Fin tails654.length → Fin 3 := ![2, 0]
theorem accepted654 : CheapOriginalAccepted (decode 654) 0 1
    tails654 added654 attachments654 := by decide
def tails656 : List (List Vertex) := [[5, 3, 7, 4, 0, 1, 2, 6], [6, 5, 4, 3, 0, 2]]
def added656 : List (List Vertex) := [[2, 5]]
def attachments656 : Fin tails656.length → Fin 3 := ![0, 1]
theorem accepted656 : CheapOriginalAccepted (decode 656) 0 1
    tails656 added656 attachments656 := by decide
def tails658 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 2, 1], [7, 4, 5, 2, 0, 1]]
def added658 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments658 : Fin tails658.length → Fin 3 := ![0, 2]
theorem accepted658 : CheapOriginalAccepted (decode 658) 2 1
    tails658 added658 attachments658 := by decide
def tails659 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 5, 4, 0, 2, 6]]
def added659 : List (List Vertex) := [[1, 0, 3, 7]]
def attachments659 : Fin tails659.length → Fin 3 := ![1, 2]
theorem accepted659 : CheapOriginalAccepted (decode 659) 2 0
    tails659 added659 attachments659 := by decide
def tails663 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 6, 2, 0, 4, 5, 1]]
def added663 : List (List Vertex) := [[6, 1, 0, 3, 7]]
def attachments663 : Fin tails663.length → Fin 3 := ![1, 2]
theorem accepted663 : CheapOriginalAccepted (decode 663) 1 2
    tails663 added663 attachments663 := by decide
def tails664 : List (List Vertex) := [[5, 1, 0, 2, 6, 7, 4, 3], [7, 1, 2, 5, 4, 0, 3]]
def added664 : List (List Vertex) := [[5, 3, 7]]
def attachments664 : Fin tails664.length → Fin 3 := ![0, 2]
theorem accepted664 : CheapOriginalAccepted (decode 664) 2 1
    tails664 added664 attachments664 := by decide
def tails668 : List (List Vertex) := [[7, 5, 2, 6, 1, 0, 4, 3], [5, 4, 7, 1, 2, 0, 3]]
def added668 : List (List Vertex) := [[7, 3, 5]]
def attachments668 : Fin tails668.length → Fin 3 := ![2, 0]
theorem accepted668 : CheapOriginalAccepted (decode 668) 2 0
    tails668 added668 attachments668 := by decide
def tails669 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 3, 0, 4, 7, 6, 2]]
def added669 : List (List Vertex) := [[6, 1, 0, 2, 5]]
def attachments669 : Fin tails669.length → Fin 3 := ![1, 0]
theorem accepted669 : CheapOriginalAccepted (decode 669) 1 2
    tails669 added669 attachments669 := by decide
def tails671 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 3, 0, 4, 5, 6, 1]]
def added671 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments671 : Fin tails671.length → Fin 3 := ![1, 2]
theorem accepted671 : CheapOriginalAccepted (decode 671) 1 0
    tails671 added671 attachments671 := by decide
def tails673 : List (List Vertex) := [[5, 2, 1, 0, 3, 4, 7, 6], [6, 0, 4, 5, 3, 7, 2]]
def added673 : List (List Vertex) := [[2, 0, 5]]
def attachments673 : Fin tails673.length → Fin 3 := ![0, 1]
theorem accepted673 : CheapOriginalAccepted (decode 673) 1 2
    tails673 added673 attachments673 := by decide
def tails675 : List (List Vertex) := [[7, 2, 1, 0, 3, 4, 5, 6], [6, 0, 4, 7, 3, 5, 2]]
def added675 : List (List Vertex) := [[2, 0, 7]]
def attachments675 : Fin tails675.length → Fin 3 := ![2, 1]
theorem accepted675 : CheapOriginalAccepted (decode 675) 1 0
    tails675 added675 attachments675 := by decide
def tails676 : List (List Vertex) := [[5, 2, 0, 1, 6, 7, 4, 3], [7, 2, 1, 5, 4, 0, 3]]
def added676 : List (List Vertex) := [[5, 3, 7]]
def attachments676 : Fin tails676.length → Fin 3 := ![0, 2]
theorem accepted676 : CheapOriginalAccepted (decode 676) 2 1
    tails676 added676 attachments676 := by decide
def tails684 : List (List Vertex) := [[7, 2, 0, 1, 6, 5, 4, 3], [5, 2, 1, 7, 4, 0, 3]]
def added684 : List (List Vertex) := [[7, 3, 5]]
def attachments684 : Fin tails684.length → Fin 3 := ![2, 0]
theorem accepted684 : CheapOriginalAccepted (decode 684) 0 1
    tails684 added684 attachments684 := by decide
def tails688 : List (List Vertex) := [[7, 3, 5, 4, 0, 1, 2, 6], [6, 7, 4, 3, 0, 2]]
def added688 : List (List Vertex) := [[2, 7]]
def attachments688 : Fin tails688.length → Fin 3 := ![2, 1]
theorem accepted688 : CheapOriginalAccepted (decode 688) 2 1
    tails688 added688 attachments688 := by decide
def tails689 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 7, 4, 0, 2, 6]]
def added689 : List (List Vertex) := [[1, 0, 3, 5]]
def attachments689 : Fin tails689.length → Fin 3 := ![1, 0]
theorem accepted689 : CheapOriginalAccepted (decode 689) 0 2
    tails689 added689 attachments689 := by decide
def tails690 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 2, 1], [5, 4, 7, 2, 0, 1]]
def added690 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments690 : Fin tails690.length → Fin 3 := ![2, 0]
theorem accepted690 : CheapOriginalAccepted (decode 690) 0 1
    tails690 added690 attachments690 := by decide
def tails692 : List (List Vertex) := [[5, 7, 2, 6, 1, 0, 4, 3], [7, 4, 5, 1, 2, 0, 3]]
def added692 : List (List Vertex) := [[5, 3, 7]]
def attachments692 : Fin tails692.length → Fin 3 := ![0, 2]
theorem accepted692 : CheapOriginalAccepted (decode 692) 0 2
    tails692 added692 attachments692 := by decide
def tails693 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 3, 0, 4, 7, 6, 1]]
def added693 : List (List Vertex) := [[6, 2, 0, 1, 5]]
def attachments693 : Fin tails693.length → Fin 3 := ![1, 0]
theorem accepted693 : CheapOriginalAccepted (decode 693) 1 2
    tails693 added693 attachments693 := by decide
def tails695 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 3, 0, 4, 5, 6, 2]]
def added695 : List (List Vertex) := [[6, 1, 0, 2, 7]]
def attachments695 : Fin tails695.length → Fin 3 := ![1, 2]
theorem accepted695 : CheapOriginalAccepted (decode 695) 1 0
    tails695 added695 attachments695 := by decide
def tails696 : List (List Vertex) := [[7, 1, 0, 2, 6, 5, 4, 3], [5, 1, 2, 7, 4, 0, 3]]
def added696 : List (List Vertex) := [[7, 3, 5]]
def attachments696 : Fin tails696.length → Fin 3 := ![2, 0]
theorem accepted696 : CheapOriginalAccepted (decode 696) 0 1
    tails696 added696 attachments696 := by decide
def tails701 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 6, 2, 0, 4, 7, 1]]
def added701 : List (List Vertex) := [[6, 1, 0, 3, 5]]
def attachments701 : Fin tails701.length → Fin 3 := ![1, 0]
theorem accepted701 : CheapOriginalAccepted (decode 701) 1 0
    tails701 added701 attachments701 := by decide
def tails709 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 1, 2], [5, 6, 3, 4, 0, 2]]
def added709 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments709 : Fin tails709.length → Fin 3 := ![1, 0]
theorem accepted709 : CheapOriginalAccepted (decode 709) 1 0
    tails709 added709 attachments709 := by decide
def tails710 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 5, 1, 0, 2]]
def added710 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments710 : Fin tails710.length → Fin 3 := ![0, 2]
theorem accepted710 : CheapOriginalAccepted (decode 710) 0 2
    tails710 added710 attachments710 := by decide
def tails711 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 1, 2], [7, 6, 1, 0, 2]]
def added711 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments711 : Fin tails711.length → Fin 3 := ![1, 2]
theorem accepted711 : CheapOriginalAccepted (decode 711) 1 2
    tails711 added711 attachments711 := by decide
def tails712 : List (List Vertex) := [[7, 6, 3, 4, 0, 2, 1, 5], [5, 4, 7, 3, 0, 1]]
def added712 : List (List Vertex) := [[1, 7]]
def attachments712 : Fin tails712.length → Fin 3 := ![2, 0]
theorem accepted712 : CheapOriginalAccepted (decode 712) 2 1
    tails712 added712 attachments712 := by decide
def tails713 : List (List Vertex) := [[5, 1, 2, 0, 4, 7, 3, 6], [6, 0, 3, 4, 5, 7, 1]]
def added713 : List (List Vertex) := [[1, 0, 5]]
def attachments713 : Fin tails713.length → Fin 3 := ![0, 1]
theorem accepted713 : CheapOriginalAccepted (decode 713) 0 2
    tails713 added713 attachments713 := by decide
def tails714 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 1, 2], [5, 4, 7, 1, 0, 2]]
def added714 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments714 : Fin tails714.length → Fin 3 := ![2, 0]
theorem accepted714 : CheapOriginalAccepted (decode 714) 0 1
    tails714 added714 attachments714 := by decide
def tails716 : List (List Vertex) := [[7, 5, 4, 3, 0, 2, 1, 6], [6, 3, 7, 4, 0, 1]]
def added716 : List (List Vertex) := [[1, 7]]
def attachments716 : Fin tails716.length → Fin 3 := ![2, 1]
theorem accepted716 : CheapOriginalAccepted (decode 716) 2 0
    tails716 added716 attachments716 := by decide
def tails717 : List (List Vertex) := [[6, 1, 2, 0, 3, 7, 4, 5], [5, 0, 4, 3, 6, 7, 1]]
def added717 : List (List Vertex) := [[1, 0, 6]]
def attachments717 : Fin tails717.length → Fin 3 := ![1, 0]
theorem accepted717 : CheapOriginalAccepted (decode 717) 1 2
    tails717 added717 attachments717 := by decide
def tails719 : List (List Vertex) := [[7, 0, 3, 4, 5, 6, 1, 2], [6, 3, 7, 1, 0, 2]]
def added719 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments719 : Fin tails719.length → Fin 3 := ![2, 1]
theorem accepted719 : CheapOriginalAccepted (decode 719) 1 0
    tails719 added719 attachments719 := by decide
def tails721 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 2, 1], [5, 6, 3, 4, 0, 1]]
def added721 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments721 : Fin tails721.length → Fin 3 := ![1, 0]
theorem accepted721 : CheapOriginalAccepted (decode 721) 1 0
    tails721 added721 attachments721 := by decide
def tails722 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 5, 2, 0, 1]]
def added722 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments722 : Fin tails722.length → Fin 3 := ![0, 2]
theorem accepted722 : CheapOriginalAccepted (decode 722) 0 2
    tails722 added722 attachments722 := by decide
def tails723 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 2, 1], [7, 6, 2, 0, 1]]
def added723 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments723 : Fin tails723.length → Fin 3 := ![1, 2]
theorem accepted723 : CheapOriginalAccepted (decode 723) 1 2
    tails723 added723 attachments723 := by decide
def tails724 : List (List Vertex) := [[6, 5, 4, 7, 3, 0, 2, 1], [5, 2, 6, 3, 4, 0, 1]]
def added724 : List (List Vertex) := [[6, 1, 5]]
def attachments724 : Fin tails724.length → Fin 3 := ![1, 0]
theorem accepted724 : CheapOriginalAccepted (decode 724) 1 0
    tails724 added724 attachments724 := by decide
def tails726 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 1, 0, 2, 6, 7, 4]]
def added726 : List (List Vertex) := [[7, 3, 0, 4, 5]]
def attachments726 : Fin tails726.length → Fin 3 := ![2, 0]
theorem accepted726 : CheapOriginalAccepted (decode 726) 2 1
    tails726 added726 attachments726 := by decide
def tails727 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 1, 0, 2, 5, 7, 3]]
def added727 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments727 : Fin tails727.length → Fin 3 := ![2, 1]
theorem accepted727 : CheapOriginalAccepted (decode 727) 2 0
    tails727 added727 attachments727 := by decide
def tails728 : List (List Vertex) := [[5, 7, 4, 0, 3, 6, 2, 1], [7, 3, 4, 5, 2, 0, 1]]
def added728 : List (List Vertex) := [[5, 1, 7]]
def attachments728 : Fin tails728.length → Fin 3 := ![0, 2]
theorem accepted728 : CheapOriginalAccepted (decode 728) 0 2
    tails728 added728 attachments728 := by decide
def tails729 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 1, 2], [6, 7, 3, 0, 1, 5, 2]]
def added729 : List (List Vertex) := [[5, 4, 0, 2, 6]]
def attachments729 : Fin tails729.length → Fin 3 := ![0, 1]
theorem accepted729 : CheapOriginalAccepted (decode 729) 1 2
    tails729 added729 attachments729 := by decide
def tails731 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 5, 2, 0, 4, 7, 3]]
def added731 : List (List Vertex) := [[7, 1, 0, 3, 6]]
def attachments731 : Fin tails731.length → Fin 3 := ![2, 1]
theorem accepted731 : CheapOriginalAccepted (decode 731) 1 0
    tails731 added731 attachments731 := by decide
def tails732 : List (List Vertex) := [[6, 7, 3, 0, 4, 5, 2, 1], [7, 4, 3, 6, 2, 0, 1]]
def added732 : List (List Vertex) := [[6, 1, 7]]
def attachments732 : Fin tails732.length → Fin 3 := ![1, 2]
theorem accepted732 : CheapOriginalAccepted (decode 732) 1 2
    tails732 added732 attachments732 := by decide
def tails733 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 7, 4, 0, 1, 6, 2]]
def added733 : List (List Vertex) := [[6, 3, 0, 2, 5]]
def attachments733 : Fin tails733.length → Fin 3 := ![1, 0]
theorem accepted733 : CheapOriginalAccepted (decode 733) 0 2
    tails733 added733 attachments733 := by decide
def tails734 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 6, 2, 0, 3, 7, 4]]
def added734 : List (List Vertex) := [[7, 1, 0, 4, 5]]
def attachments734 : Fin tails734.length → Fin 3 := ![2, 0]
theorem accepted734 : CheapOriginalAccepted (decode 734) 0 1
    tails734 added734 attachments734 := by decide
def tails736 : List (List Vertex) := [[7, 6, 3, 4, 0, 1, 2, 5], [5, 4, 7, 3, 0, 2]]
def added736 : List (List Vertex) := [[2, 7]]
def attachments736 : Fin tails736.length → Fin 3 := ![2, 0]
theorem accepted736 : CheapOriginalAccepted (decode 736) 2 1
    tails736 added736 attachments736 := by decide
def tails737 : List (List Vertex) := [[5, 2, 1, 0, 4, 7, 3, 6], [6, 0, 3, 4, 5, 7, 2]]
def added737 : List (List Vertex) := [[2, 0, 5]]
def attachments737 : Fin tails737.length → Fin 3 := ![0, 1]
theorem accepted737 : CheapOriginalAccepted (decode 737) 0 2
    tails737 added737 attachments737 := by decide
def tails738 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 2, 1], [5, 4, 7, 2, 0, 1]]
def added738 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments738 : Fin tails738.length → Fin 3 := ![2, 0]
theorem accepted738 : CheapOriginalAccepted (decode 738) 0 1
    tails738 added738 attachments738 := by decide
def tails740 : List (List Vertex) := [[5, 7, 4, 0, 3, 6, 1, 2], [7, 3, 4, 5, 1, 0, 2]]
def added740 : List (List Vertex) := [[5, 2, 7]]
def attachments740 : Fin tails740.length → Fin 3 := ![0, 2]
theorem accepted740 : CheapOriginalAccepted (decode 740) 0 2
    tails740 added740 attachments740 := by decide
def tails741 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 2, 1], [6, 7, 3, 0, 2, 5, 1]]
def added741 : List (List Vertex) := [[5, 4, 0, 1, 6]]
def attachments741 : Fin tails741.length → Fin 3 := ![0, 1]
theorem accepted741 : CheapOriginalAccepted (decode 741) 1 2
    tails741 added741 attachments741 := by decide
def tails743 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 4, 3], [6, 5, 1, 0, 4, 7, 3]]
def added743 : List (List Vertex) := [[7, 2, 0, 3, 6]]
def attachments743 : Fin tails743.length → Fin 3 := ![2, 1]
theorem accepted743 : CheapOriginalAccepted (decode 743) 1 0
    tails743 added743 attachments743 := by decide
def tails744 : List (List Vertex) := [[7, 4, 0, 3, 6, 5, 2, 1], [5, 4, 3, 7, 2, 0, 1]]
def added744 : List (List Vertex) := [[7, 1, 5]]
def attachments744 : Fin tails744.length → Fin 3 := ![2, 0]
theorem accepted744 : CheapOriginalAccepted (decode 744) 0 1
    tails744 added744 attachments744 := by decide
def tails749 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 2, 1], [5, 6, 3, 4, 0, 2, 7, 1]]
def added749 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments749 : Fin tails749.length → Fin 3 := ![1, 0]
theorem accepted749 : CheapOriginalAccepted (decode 749) 1 0
    tails749 added749 attachments749 := by decide
def tails752 : List (List Vertex) := [[7, 5, 4, 3, 0, 1, 2, 6], [6, 3, 7, 4, 0, 2]]
def added752 : List (List Vertex) := [[2, 7]]
def attachments752 : Fin tails752.length → Fin 3 := ![2, 1]
theorem accepted752 : CheapOriginalAccepted (decode 752) 2 0
    tails752 added752 attachments752 := by decide
def tails753 : List (List Vertex) := [[6, 2, 1, 0, 3, 7, 4, 5], [5, 0, 4, 3, 6, 7, 2]]
def added753 : List (List Vertex) := [[2, 0, 6]]
def attachments753 : Fin tails753.length → Fin 3 := ![1, 0]
theorem accepted753 : CheapOriginalAccepted (decode 753) 1 2
    tails753 added753 attachments753 := by decide
def tails755 : List (List Vertex) := [[7, 0, 3, 4, 5, 6, 2, 1], [6, 3, 7, 2, 0, 1]]
def added755 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments755 : Fin tails755.length → Fin 3 := ![2, 1]
theorem accepted755 : CheapOriginalAccepted (decode 755) 1 0
    tails755 added755 attachments755 := by decide
def tails756 : List (List Vertex) := [[6, 7, 3, 0, 4, 5, 1, 2], [7, 4, 3, 6, 1, 0, 2]]
def added756 : List (List Vertex) := [[6, 2, 7]]
def attachments756 : Fin tails756.length → Fin 3 := ![1, 2]
theorem accepted756 : CheapOriginalAccepted (decode 756) 1 2
    tails756 added756 attachments756 := by decide
def tails757 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 7, 4, 0, 2, 6, 1]]
def added757 : List (List Vertex) := [[6, 3, 0, 1, 5]]
def attachments757 : Fin tails757.length → Fin 3 := ![1, 0]
theorem accepted757 : CheapOriginalAccepted (decode 757) 0 2
    tails757 added757 attachments757 := by decide
def tails758 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 3, 4], [5, 6, 1, 0, 3, 7, 4]]
def added758 : List (List Vertex) := [[7, 2, 0, 4, 5]]
def attachments758 : Fin tails758.length → Fin 3 := ![2, 0]
theorem accepted758 : CheapOriginalAccepted (decode 758) 0 1
    tails758 added758 attachments758 := by decide
def tails761 : List (List Vertex) := [[5, 0, 4, 7, 3, 6, 2, 1], [6, 5, 4, 3, 0, 2, 7, 1]]
def added761 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments761 : Fin tails761.length → Fin 3 := ![0, 1]
theorem accepted761 : CheapOriginalAccepted (decode 761) 0 1
    tails761 added761 attachments761 := by decide
def tails764 : List (List Vertex) := [[7, 3, 0, 4, 5, 6, 2, 1], [6, 3, 4, 7, 2, 0, 1]]
def added764 : List (List Vertex) := [[7, 1, 6]]
def attachments764 : Fin tails764.length → Fin 3 := ![2, 1]
theorem accepted764 : CheapOriginalAccepted (decode 764) 1 0
    tails764 added764 attachments764 := by decide
def tails788 : List (List Vertex) := [[6, 1, 5, 2, 0, 3, 4, 7], [7, 6, 2, 1, 0, 4]]
def added788 : List (List Vertex) := [[4, 6]]
def attachments788 : Fin tails788.length → Fin 3 := ![1, 2]
theorem accepted788 : CheapOriginalAccepted (decode 788) 1 2
    tails788 added788 attachments788 := by decide
def tails789 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 4, 3], [5, 2, 6, 4, 0, 3]]
def added789 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments789 : Fin tails789.length → Fin 3 := ![1, 0]
theorem accepted789 : CheapOriginalAccepted (decode 789) 0 2
    tails789 added789 attachments789 := by decide
def tails790 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 6, 2, 0, 4, 7]]
def added790 : List (List Vertex) := [[3, 0, 1, 5]]
def attachments790 : Fin tails790.length → Fin 3 := ![2, 0]
theorem accepted790 : CheapOriginalAccepted (decode 790) 0 1
    tails790 added790 attachments790 := by decide
def tails793 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 6, 4, 0, 3]]
def added793 : List (List Vertex) := [[6, 2, 0, 1, 5]]
def attachments793 : Fin tails793.length → Fin 3 := ![1, 0]
theorem accepted793 : CheapOriginalAccepted (decode 793) 1 0
    tails793 added793 attachments793 := by decide
def tails794 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 4, 3], [5, 7, 4, 0, 3]]
def added794 : List (List Vertex) := [[7, 1, 0, 2, 5]]
def attachments794 : Fin tails794.length → Fin 3 := ![2, 0]
theorem accepted794 : CheapOriginalAccepted (decode 794) 2 0
    tails794 added794 attachments794 := by decide
def tails795 : List (List Vertex) := [[7, 0, 1, 5, 2, 6, 4, 3], [6, 7, 1, 2, 0, 3]]
def added795 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments795 : Fin tails795.length → Fin 3 := ![2, 1]
theorem accepted795 : CheapOriginalAccepted (decode 795) 2 1
    tails795 added795 attachments795 := by decide
def tails796 : List (List Vertex) := [[6, 5, 2, 1, 0, 3, 4, 7], [7, 1, 6, 2, 0, 4]]
def added796 : List (List Vertex) := [[4, 6]]
def attachments796 : Fin tails796.length → Fin 3 := ![1, 2]
theorem accepted796 : CheapOriginalAccepted (decode 796) 1 0
    tails796 added796 attachments796 := by decide
def tails798 : List (List Vertex) := [[7, 4, 3, 0, 1, 6, 2, 5], [5, 0, 2, 1, 7, 6, 4]]
def added798 : List (List Vertex) := [[4, 0, 7]]
def attachments798 : Fin tails798.length → Fin 3 := ![2, 0]
theorem accepted798 : CheapOriginalAccepted (decode 798) 2 1
    tails798 added798 attachments798 := by decide
def tails799 : List (List Vertex) := [[6, 0, 1, 2, 5, 7, 4, 3], [7, 1, 6, 4, 0, 3]]
def added799 : List (List Vertex) := [[6, 2, 0, 7]]
def attachments799 : Fin tails799.length → Fin 3 := ![1, 2]
theorem accepted799 : CheapOriginalAccepted (decode 799) 2 0
    tails799 added799 attachments799 := by decide
def tails805 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 4, 3], [5, 6, 4, 0, 3]]
def added805 : List (List Vertex) := [[6, 1, 0, 2, 5]]
def attachments805 : Fin tails805.length → Fin 3 := ![1, 0]
theorem accepted805 : CheapOriginalAccepted (decode 805) 1 0
    tails805 added805 attachments805 := by decide
def tails806 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 7, 4, 0, 3]]
def added806 : List (List Vertex) := [[7, 2, 0, 1, 5]]
def attachments806 : Fin tails806.length → Fin 3 := ![2, 0]
theorem accepted806 : CheapOriginalAccepted (decode 806) 2 0
    tails806 added806 attachments806 := by decide
def tails807 : List (List Vertex) := [[6, 0, 1, 5, 2, 7, 4, 3], [7, 6, 1, 2, 0, 3]]
def added807 : List (List Vertex) := [[6, 4, 0, 7]]
def attachments807 : Fin tails807.length → Fin 3 := ![1, 2]
theorem accepted807 : CheapOriginalAccepted (decode 807) 1 2
    tails807 added807 attachments807 := by decide
def tails808 : List (List Vertex) := [[7, 1, 5, 2, 0, 3, 4, 6], [6, 7, 2, 1, 0, 4]]
def added808 : List (List Vertex) := [[4, 7]]
def attachments808 : Fin tails808.length → Fin 3 := ![2, 1]
theorem accepted808 : CheapOriginalAccepted (decode 808) 2 1
    tails808 added808 attachments808 := by decide
def tails809 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 7, 2, 0, 4, 6]]
def added809 : List (List Vertex) := [[3, 0, 1, 5]]
def attachments809 : Fin tails809.length → Fin 3 := ![1, 0]
theorem accepted809 : CheapOriginalAccepted (decode 809) 0 2
    tails809 added809 attachments809 := by decide
def tails810 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 4, 3], [5, 2, 7, 4, 0, 3]]
def added810 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments810 : Fin tails810.length → Fin 3 := ![2, 0]
theorem accepted810 : CheapOriginalAccepted (decode 810) 0 1
    tails810 added810 attachments810 := by decide
def tails812 : List (List Vertex) := [[7, 5, 2, 1, 0, 3, 4, 6], [6, 1, 7, 2, 0, 4]]
def added812 : List (List Vertex) := [[4, 7]]
def attachments812 : Fin tails812.length → Fin 3 := ![2, 1]
theorem accepted812 : CheapOriginalAccepted (decode 812) 2 0
    tails812 added812 attachments812 := by decide
def tails813 : List (List Vertex) := [[6, 4, 3, 0, 1, 7, 2, 5], [5, 0, 2, 1, 6, 7, 4]]
def added813 : List (List Vertex) := [[4, 0, 6]]
def attachments813 : Fin tails813.length → Fin 3 := ![1, 0]
theorem accepted813 : CheapOriginalAccepted (decode 813) 1 2
    tails813 added813 attachments813 := by decide
def tails815 : List (List Vertex) := [[7, 0, 1, 2, 5, 6, 4, 3], [6, 1, 7, 4, 0, 3]]
def added815 : List (List Vertex) := [[7, 2, 0, 6]]
def attachments815 : Fin tails815.length → Fin 3 := ![2, 1]
theorem accepted815 : CheapOriginalAccepted (decode 815) 1 0
    tails815 added815 attachments815 := by decide
def tails820 : List (List Vertex) := [[6, 5, 1, 2, 0, 3, 4, 7], [7, 2, 6, 1, 0, 4]]
def added820 : List (List Vertex) := [[4, 6]]
def attachments820 : Fin tails820.length → Fin 3 := ![1, 2]
theorem accepted820 : CheapOriginalAccepted (decode 820) 1 0
    tails820 added820 attachments820 := by decide
def tails822 : List (List Vertex) := [[7, 4, 3, 0, 2, 6, 1, 5], [5, 0, 1, 2, 7, 6, 4]]
def added822 : List (List Vertex) := [[4, 0, 7]]
def attachments822 : Fin tails822.length → Fin 3 := ![2, 0]
theorem accepted822 : CheapOriginalAccepted (decode 822) 2 1
    tails822 added822 attachments822 := by decide
def tails823 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 4, 3], [7, 2, 6, 4, 0, 3]]
def added823 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments823 : Fin tails823.length → Fin 3 := ![1, 2]
theorem accepted823 : CheapOriginalAccepted (decode 823) 2 0
    tails823 added823 attachments823 := by decide
def tails824 : List (List Vertex) := [[7, 5, 1, 2, 0, 3, 4, 6], [6, 2, 7, 1, 0, 4]]
def added824 : List (List Vertex) := [[4, 7]]
def attachments824 : Fin tails824.length → Fin 3 := ![2, 1]
theorem accepted824 : CheapOriginalAccepted (decode 824) 2 0
    tails824 added824 attachments824 := by decide
def tails825 : List (List Vertex) := [[6, 4, 3, 0, 2, 7, 1, 5], [5, 0, 1, 2, 6, 7, 4]]
def added825 : List (List Vertex) := [[4, 0, 6]]
def attachments825 : Fin tails825.length → Fin 3 := ![1, 0]
theorem accepted825 : CheapOriginalAccepted (decode 825) 1 2
    tails825 added825 attachments825 := by decide
def tails827 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 4, 3], [6, 2, 7, 4, 0, 3]]
def added827 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments827 : Fin tails827.length → Fin 3 := ![2, 1]
theorem accepted827 : CheapOriginalAccepted (decode 827) 1 0
    tails827 added827 attachments827 := by decide
def tails829 : List (List Vertex) := [[6, 4, 3, 0, 1, 2, 7, 5], [5, 0, 2, 6, 1, 7, 4]]
def added829 : List (List Vertex) := [[4, 0, 6]]
def attachments829 : Fin tails829.length → Fin 3 := ![1, 0]
theorem accepted829 : CheapOriginalAccepted (decode 829) 0 2
    tails829 added829 attachments829 := by decide
def tails830 : List (List Vertex) := [[7, 4, 3, 0, 1, 2, 6, 5], [5, 0, 2, 7, 1, 6, 4]]
def added830 : List (List Vertex) := [[4, 0, 7]]
def attachments830 : Fin tails830.length → Fin 3 := ![2, 0]
theorem accepted830 : CheapOriginalAccepted (decode 830) 0 1
    tails830 added830 attachments830 := by decide
def tails836 : List (List Vertex) := [[6, 7, 4, 3, 0, 2, 1, 5], [5, 3, 6, 4, 0, 1]]
def added836 : List (List Vertex) := [[1, 6]]
def attachments836 : Fin tails836.length → Fin 3 := ![1, 0]
theorem accepted836 : CheapOriginalAccepted (decode 836) 1 2
    tails836 added836 attachments836 := by decide
def tails837 : List (List Vertex) := [[6, 0, 3, 4, 7, 5, 1, 2], [5, 3, 6, 1, 0, 2]]
def added837 : List (List Vertex) := [[6, 4, 0, 5]]
def attachments837 : Fin tails837.length → Fin 3 := ![1, 0]
theorem accepted837 : CheapOriginalAccepted (decode 837) 0 2
    tails837 added837 attachments837 := by decide
def tails838 : List (List Vertex) := [[5, 1, 2, 0, 3, 6, 4, 7], [7, 0, 4, 3, 5, 6, 1]]
def added838 : List (List Vertex) := [[1, 0, 5]]
def attachments838 : Fin tails838.length → Fin 3 := ![0, 2]
theorem accepted838 : CheapOriginalAccepted (decode 838) 0 1
    tails838 added838 attachments838 := by decide
def tails841 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 1, 2], [6, 5, 1, 0, 2]]
def added841 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments841 : Fin tails841.length → Fin 3 := ![0, 1]
theorem accepted841 : CheapOriginalAccepted (decode 841) 0 1
    tails841 added841 attachments841 := by decide
def tails842 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 1, 2], [7, 5, 3, 4, 0, 2]]
def added842 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments842 : Fin tails842.length → Fin 3 := ![0, 2]
theorem accepted842 : CheapOriginalAccepted (decode 842) 0 2
    tails842 added842 attachments842 := by decide
def tails843 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 7, 1, 0, 2]]
def added843 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments843 : Fin tails843.length → Fin 3 := ![2, 1]
theorem accepted843 : CheapOriginalAccepted (decode 843) 2 1
    tails843 added843 attachments843 := by decide
def tails844 : List (List Vertex) := [[6, 5, 3, 4, 0, 2, 1, 7], [7, 4, 6, 3, 0, 1]]
def added844 : List (List Vertex) := [[1, 6]]
def attachments844 : Fin tails844.length → Fin 3 := ![1, 2]
theorem accepted844 : CheapOriginalAccepted (decode 844) 1 0
    tails844 added844 attachments844 := by decide
def tails846 : List (List Vertex) := [[7, 1, 2, 0, 4, 6, 3, 5], [5, 0, 3, 4, 7, 6, 1]]
def added846 : List (List Vertex) := [[1, 0, 7]]
def attachments846 : Fin tails846.length → Fin 3 := ![2, 0]
theorem accepted846 : CheapOriginalAccepted (decode 846) 2 1
    tails846 added846 attachments846 := by decide
def tails847 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 1, 2], [7, 4, 6, 1, 0, 2]]
def added847 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments847 : Fin tails847.length → Fin 3 := ![1, 2]
theorem accepted847 : CheapOriginalAccepted (decode 847) 2 0
    tails847 added847 attachments847 := by decide
def tails848 : List (List Vertex) := [[6, 7, 4, 3, 0, 1, 2, 5], [5, 3, 6, 4, 0, 2]]
def added848 : List (List Vertex) := [[2, 6]]
def attachments848 : Fin tails848.length → Fin 3 := ![1, 0]
theorem accepted848 : CheapOriginalAccepted (decode 848) 1 2
    tails848 added848 attachments848 := by decide
def tails849 : List (List Vertex) := [[6, 0, 3, 4, 7, 5, 2, 1], [5, 3, 6, 2, 0, 1]]
def added849 : List (List Vertex) := [[6, 4, 0, 5]]
def attachments849 : Fin tails849.length → Fin 3 := ![1, 0]
theorem accepted849 : CheapOriginalAccepted (decode 849) 0 2
    tails849 added849 attachments849 := by decide
def tails850 : List (List Vertex) := [[5, 2, 1, 0, 3, 6, 4, 7], [7, 0, 4, 3, 5, 6, 2]]
def added850 : List (List Vertex) := [[2, 0, 5]]
def attachments850 : Fin tails850.length → Fin 3 := ![0, 2]
theorem accepted850 : CheapOriginalAccepted (decode 850) 0 1
    tails850 added850 attachments850 := by decide
def tails852 : List (List Vertex) := [[6, 3, 0, 4, 7, 5, 2, 1], [5, 3, 4, 6, 2, 0, 1]]
def added852 : List (List Vertex) := [[6, 1, 5]]
def attachments852 : Fin tails852.length → Fin 3 := ![1, 0]
theorem accepted852 : CheapOriginalAccepted (decode 852) 0 2
    tails852 added852 attachments852 := by decide
def tails856 : List (List Vertex) := [[5, 6, 3, 0, 4, 7, 1, 2], [6, 4, 3, 5, 1, 0, 2]]
def added856 : List (List Vertex) := [[5, 2, 6]]
def attachments856 : Fin tails856.length → Fin 3 := ![0, 1]
theorem accepted856 : CheapOriginalAccepted (decode 856) 0 1
    tails856 added856 attachments856 := by decide
def tails858 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 6, 4, 0, 2, 5, 1]]
def added858 : List (List Vertex) := [[5, 3, 0, 1, 7]]
def attachments858 : Fin tails858.length → Fin 3 := ![0, 2]
theorem accepted858 : CheapOriginalAccepted (decode 858) 2 1
    tails858 added858 attachments858 := by decide
def tails859 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 3, 4], [7, 5, 1, 0, 3, 6, 4]]
def added859 : List (List Vertex) := [[6, 2, 0, 4, 7]]
def attachments859 : Fin tails859.length → Fin 3 := ![1, 2]
theorem accepted859 : CheapOriginalAccepted (decode 859) 2 0
    tails859 added859 attachments859 := by decide
def tails862 : List (List Vertex) := [[7, 0, 4, 6, 3, 5, 2, 1], [5, 7, 4, 3, 0, 2, 6, 1]]
def added862 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments862 : Fin tails862.length → Fin 3 := ![2, 0]
theorem accepted862 : CheapOriginalAccepted (decode 862) 2 0
    tails862 added862 attachments862 := by decide
def tails865 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 2, 1], [6, 5, 2, 0, 1]]
def added865 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments865 : Fin tails865.length → Fin 3 := ![0, 1]
theorem accepted865 : CheapOriginalAccepted (decode 865) 0 1
    tails865 added865 attachments865 := by decide
def tails866 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 2, 1], [7, 5, 3, 4, 0, 1]]
def added866 : List (List Vertex) := [[5, 2, 0, 7]]
def attachments866 : Fin tails866.length → Fin 3 := ![0, 2]
theorem accepted866 : CheapOriginalAccepted (decode 866) 0 2
    tails866 added866 attachments866 := by decide
def tails867 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 7, 2, 0, 1]]
def added867 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments867 : Fin tails867.length → Fin 3 := ![2, 1]
theorem accepted867 : CheapOriginalAccepted (decode 867) 2 1
    tails867 added867 attachments867 := by decide
def tails868 : List (List Vertex) := [[5, 6, 3, 0, 4, 7, 2, 1], [6, 4, 3, 5, 2, 0, 1]]
def added868 : List (List Vertex) := [[5, 1, 6]]
def attachments868 : Fin tails868.length → Fin 3 := ![0, 1]
theorem accepted868 : CheapOriginalAccepted (decode 868) 0 1
    tails868 added868 attachments868 := by decide
def tails870 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 6, 4, 0, 1, 5, 2]]
def added870 : List (List Vertex) := [[5, 3, 0, 2, 7]]
def attachments870 : Fin tails870.length → Fin 3 := ![0, 2]
theorem accepted870 : CheapOriginalAccepted (decode 870) 2 1
    tails870 added870 attachments870 := by decide
def tails871 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 5, 2, 0, 3, 6, 4]]
def added871 : List (List Vertex) := [[6, 1, 0, 4, 7]]
def attachments871 : Fin tails871.length → Fin 3 := ![1, 2]
theorem accepted871 : CheapOriginalAccepted (decode 871) 2 0
    tails871 added871 attachments871 := by decide
def tails872 : List (List Vertex) := [[5, 7, 4, 6, 3, 0, 2, 1], [7, 2, 5, 3, 4, 0, 1]]
def added872 : List (List Vertex) := [[5, 1, 7]]
def attachments872 : Fin tails872.length → Fin 3 := ![0, 2]
theorem accepted872 : CheapOriginalAccepted (decode 872) 0 2
    tails872 added872 attachments872 := by decide
def tails873 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 1, 0, 2, 7, 6, 3]]
def added873 : List (List Vertex) := [[6, 4, 0, 3, 5]]
def attachments873 : Fin tails873.length → Fin 3 := ![1, 0]
theorem accepted873 : CheapOriginalAccepted (decode 873) 1 2
    tails873 added873 attachments873 := by decide
def tails875 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 1, 0, 2, 5, 6, 4]]
def added875 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments875 : Fin tails875.length → Fin 3 := ![1, 2]
theorem accepted875 : CheapOriginalAccepted (decode 875) 1 0
    tails875 added875 attachments875 := by decide
def tails876 : List (List Vertex) := [[7, 6, 4, 0, 3, 5, 2, 1], [6, 3, 4, 7, 2, 0, 1]]
def added876 : List (List Vertex) := [[7, 1, 6]]
def attachments876 : Fin tails876.length → Fin 3 := ![2, 1]
theorem accepted876 : CheapOriginalAccepted (decode 876) 2 1
    tails876 added876 attachments876 := by decide
def tails877 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 7, 2, 0, 4, 6, 3]]
def added877 : List (List Vertex) := [[6, 1, 0, 3, 5]]
def attachments877 : Fin tails877.length → Fin 3 := ![1, 0]
theorem accepted877 : CheapOriginalAccepted (decode 877) 0 2
    tails877 added877 attachments877 := by decide
def tails878 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 1, 2], [5, 6, 3, 0, 1, 7, 2]]
def added878 : List (List Vertex) := [[7, 4, 0, 2, 5]]
def attachments878 : Fin tails878.length → Fin 3 := ![2, 0]
theorem accepted878 : CheapOriginalAccepted (decode 878) 0 1
    tails878 added878 attachments878 := by decide
def tails880 : List (List Vertex) := [[6, 5, 3, 4, 0, 1, 2, 7], [7, 4, 6, 3, 0, 2]]
def added880 : List (List Vertex) := [[2, 6]]
def attachments880 : Fin tails880.length → Fin 3 := ![1, 2]
theorem accepted880 : CheapOriginalAccepted (decode 880) 1 0
    tails880 added880 attachments880 := by decide
def tails882 : List (List Vertex) := [[7, 2, 1, 0, 4, 6, 3, 5], [5, 0, 3, 4, 7, 6, 2]]
def added882 : List (List Vertex) := [[2, 0, 7]]
def attachments882 : Fin tails882.length → Fin 3 := ![2, 0]
theorem accepted882 : CheapOriginalAccepted (decode 882) 2 1
    tails882 added882 attachments882 := by decide
def tails883 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 2, 1], [7, 4, 6, 2, 0, 1]]
def added883 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments883 : Fin tails883.length → Fin 3 := ![1, 2]
theorem accepted883 : CheapOriginalAccepted (decode 883) 2 0
    tails883 added883 attachments883 := by decide
def tails886 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 2, 1], [7, 5, 3, 4, 0, 2, 6, 1]]
def added886 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments886 : Fin tails886.length → Fin 3 := ![0, 2]
theorem accepted886 : CheapOriginalAccepted (decode 886) 0 2
    tails886 added886 attachments886 := by decide
def tails888 : List (List Vertex) := [[7, 6, 4, 0, 3, 5, 1, 2], [6, 3, 4, 7, 1, 0, 2]]
def added888 : List (List Vertex) := [[7, 2, 6]]
def attachments888 : Fin tails888.length → Fin 3 := ![2, 1]
theorem accepted888 : CheapOriginalAccepted (decode 888) 2 1
    tails888 added888 attachments888 := by decide
def tails889 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 4, 3], [5, 7, 1, 0, 4, 6, 3]]
def added889 : List (List Vertex) := [[6, 2, 0, 3, 5]]
def attachments889 : Fin tails889.length → Fin 3 := ![1, 0]
theorem accepted889 : CheapOriginalAccepted (decode 889) 0 2
    tails889 added889 attachments889 := by decide
def tails890 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 2, 1], [5, 6, 3, 0, 2, 7, 1]]
def added890 : List (List Vertex) := [[7, 4, 0, 1, 5]]
def attachments890 : Fin tails890.length → Fin 3 := ![2, 0]
theorem accepted890 : CheapOriginalAccepted (decode 890) 0 1
    tails890 added890 attachments890 := by decide
def tails892 : List (List Vertex) := [[6, 4, 0, 3, 5, 7, 2, 1], [7, 4, 3, 6, 2, 0, 1]]
def added892 : List (List Vertex) := [[6, 1, 7]]
def attachments892 : Fin tails892.length → Fin 3 := ![1, 2]
theorem accepted892 : CheapOriginalAccepted (decode 892) 2 0
    tails892 added892 attachments892 := by decide
def tails901 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 1, 2], [6, 5, 3, 4, 0, 2]]
def added901 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments901 : Fin tails901.length → Fin 3 := ![0, 1]
theorem accepted901 : CheapOriginalAccepted (decode 901) 0 1
    tails901 added901 attachments901 := by decide
def tails902 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 1, 2], [7, 5, 1, 0, 2]]
def added902 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments902 : Fin tails902.length → Fin 3 := ![0, 2]
theorem accepted902 : CheapOriginalAccepted (decode 902) 0 2
    tails902 added902 attachments902 := by decide
def tails903 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 6, 1, 0, 2]]
def added903 : List (List Vertex) := [[6, 4, 0, 3, 7]]
def attachments903 : Fin tails903.length → Fin 3 := ![1, 2]
theorem accepted903 : CheapOriginalAccepted (decode 903) 1 2
    tails903 added903 attachments903 := by decide
def tails904 : List (List Vertex) := [[7, 6, 4, 3, 0, 2, 1, 5], [5, 3, 7, 4, 0, 1]]
def added904 : List (List Vertex) := [[1, 7]]
def attachments904 : Fin tails904.length → Fin 3 := ![2, 0]
theorem accepted904 : CheapOriginalAccepted (decode 904) 2 1
    tails904 added904 attachments904 := by decide
def tails905 : List (List Vertex) := [[5, 1, 2, 0, 3, 7, 4, 6], [6, 0, 4, 3, 5, 7, 1]]
def added905 : List (List Vertex) := [[1, 0, 5]]
def attachments905 : Fin tails905.length → Fin 3 := ![0, 1]
theorem accepted905 : CheapOriginalAccepted (decode 905) 0 2
    tails905 added905 attachments905 := by decide
def tails906 : List (List Vertex) := [[7, 0, 3, 4, 6, 5, 1, 2], [5, 3, 7, 1, 0, 2]]
def added906 : List (List Vertex) := [[7, 4, 0, 5]]
def attachments906 : Fin tails906.length → Fin 3 := ![2, 0]
theorem accepted906 : CheapOriginalAccepted (decode 906) 0 1
    tails906 added906 attachments906 := by decide
def tails908 : List (List Vertex) := [[7, 5, 3, 4, 0, 2, 1, 6], [6, 4, 7, 3, 0, 1]]
def added908 : List (List Vertex) := [[1, 7]]
def attachments908 : Fin tails908.length → Fin 3 := ![2, 1]
theorem accepted908 : CheapOriginalAccepted (decode 908) 2 0
    tails908 added908 attachments908 := by decide
def tails909 : List (List Vertex) := [[6, 1, 2, 0, 4, 7, 3, 5], [5, 0, 3, 4, 6, 7, 1]]
def added909 : List (List Vertex) := [[1, 0, 6]]
def attachments909 : Fin tails909.length → Fin 3 := ![1, 0]
theorem accepted909 : CheapOriginalAccepted (decode 909) 1 2
    tails909 added909 attachments909 := by decide
def tails911 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 1, 2], [6, 4, 7, 1, 0, 2]]
def added911 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments911 : Fin tails911.length → Fin 3 := ![2, 1]
theorem accepted911 : CheapOriginalAccepted (decode 911) 1 0
    tails911 added911 attachments911 := by decide
def tails913 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 2, 1], [6, 5, 3, 4, 0, 1]]
def added913 : List (List Vertex) := [[5, 2, 0, 6]]
def attachments913 : Fin tails913.length → Fin 3 := ![0, 1]
theorem accepted913 : CheapOriginalAccepted (decode 913) 0 1
    tails913 added913 attachments913 := by decide
def tails914 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 2, 1], [7, 5, 2, 0, 1]]
def added914 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments914 : Fin tails914.length → Fin 3 := ![0, 2]
theorem accepted914 : CheapOriginalAccepted (decode 914) 0 2
    tails914 added914 attachments914 := by decide
def tails915 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 6, 2, 0, 1]]
def added915 : List (List Vertex) := [[6, 4, 0, 3, 7]]
def attachments915 : Fin tails915.length → Fin 3 := ![1, 2]
theorem accepted915 : CheapOriginalAccepted (decode 915) 1 2
    tails915 added915 attachments915 := by decide
def tails916 : List (List Vertex) := [[5, 6, 4, 7, 3, 0, 2, 1], [6, 2, 5, 3, 4, 0, 1]]
def added916 : List (List Vertex) := [[5, 1, 6]]
def attachments916 : Fin tails916.length → Fin 3 := ![0, 1]
theorem accepted916 : CheapOriginalAccepted (decode 916) 0 1
    tails916 added916 attachments916 := by decide
def tails918 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 1, 0, 2, 6, 7, 3]]
def added918 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments918 : Fin tails918.length → Fin 3 := ![2, 0]
theorem accepted918 : CheapOriginalAccepted (decode 918) 2 1
    tails918 added918 attachments918 := by decide
def tails919 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 1, 0, 2, 5, 7, 4]]
def added919 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments919 : Fin tails919.length → Fin 3 := ![2, 1]
theorem accepted919 : CheapOriginalAccepted (decode 919) 2 0
    tails919 added919 attachments919 := by decide
def tails920 : List (List Vertex) := [[5, 7, 3, 0, 4, 6, 2, 1], [7, 4, 3, 5, 2, 0, 1]]
def added920 : List (List Vertex) := [[5, 1, 7]]
def attachments920 : Fin tails920.length → Fin 3 := ![0, 2]
theorem accepted920 : CheapOriginalAccepted (decode 920) 0 2
    tails920 added920 attachments920 := by decide
def tails921 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 7, 4, 0, 1, 5, 2]]
def added921 : List (List Vertex) := [[5, 3, 0, 2, 6]]
def attachments921 : Fin tails921.length → Fin 3 := ![0, 1]
theorem accepted921 : CheapOriginalAccepted (decode 921) 1 2
    tails921 added921 attachments921 := by decide
def tails923 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 5, 2, 0, 3, 7, 4]]
def added923 : List (List Vertex) := [[7, 1, 0, 4, 6]]
def attachments923 : Fin tails923.length → Fin 3 := ![2, 1]
theorem accepted923 : CheapOriginalAccepted (decode 923) 1 0
    tails923 added923 attachments923 := by decide
def tails924 : List (List Vertex) := [[6, 7, 4, 0, 3, 5, 2, 1], [7, 3, 4, 6, 2, 0, 1]]
def added924 : List (List Vertex) := [[6, 1, 7]]
def attachments924 : Fin tails924.length → Fin 3 := ![1, 2]
theorem accepted924 : CheapOriginalAccepted (decode 924) 1 2
    tails924 added924 attachments924 := by decide
def tails925 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 1, 2], [5, 7, 3, 0, 1, 6, 2]]
def added925 : List (List Vertex) := [[6, 4, 0, 2, 5]]
def attachments925 : Fin tails925.length → Fin 3 := ![1, 0]
theorem accepted925 : CheapOriginalAccepted (decode 925) 0 2
    tails925 added925 attachments925 := by decide
def tails926 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 6, 2, 0, 4, 7, 3]]
def added926 : List (List Vertex) := [[7, 1, 0, 3, 5]]
def attachments926 : Fin tails926.length → Fin 3 := ![2, 0]
theorem accepted926 : CheapOriginalAccepted (decode 926) 0 1
    tails926 added926 attachments926 := by decide
def tails928 : List (List Vertex) := [[7, 6, 4, 3, 0, 1, 2, 5], [5, 3, 7, 4, 0, 2]]
def added928 : List (List Vertex) := [[2, 7]]
def attachments928 : Fin tails928.length → Fin 3 := ![2, 0]
theorem accepted928 : CheapOriginalAccepted (decode 928) 2 1
    tails928 added928 attachments928 := by decide
def tails929 : List (List Vertex) := [[5, 2, 1, 0, 3, 7, 4, 6], [6, 0, 4, 3, 5, 7, 2]]
def added929 : List (List Vertex) := [[2, 0, 5]]
def attachments929 : Fin tails929.length → Fin 3 := ![0, 1]
theorem accepted929 : CheapOriginalAccepted (decode 929) 0 2
    tails929 added929 attachments929 := by decide
def tails930 : List (List Vertex) := [[7, 0, 3, 4, 6, 5, 2, 1], [5, 3, 7, 2, 0, 1]]
def added930 : List (List Vertex) := [[7, 4, 0, 5]]
def attachments930 : Fin tails930.length → Fin 3 := ![2, 0]
theorem accepted930 : CheapOriginalAccepted (decode 930) 0 1
    tails930 added930 attachments930 := by decide
def tails932 : List (List Vertex) := [[5, 7, 3, 0, 4, 6, 1, 2], [7, 4, 3, 5, 1, 0, 2]]
def added932 : List (List Vertex) := [[5, 2, 7]]
def attachments932 : Fin tails932.length → Fin 3 := ![0, 2]
theorem accepted932 : CheapOriginalAccepted (decode 932) 0 2
    tails932 added932 attachments932 := by decide
def tails933 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 7, 4, 0, 2, 5, 1]]
def added933 : List (List Vertex) := [[5, 3, 0, 1, 6]]
def attachments933 : Fin tails933.length → Fin 3 := ![0, 1]
theorem accepted933 : CheapOriginalAccepted (decode 933) 1 2
    tails933 added933 attachments933 := by decide
def tails935 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 3, 4], [6, 5, 1, 0, 3, 7, 4]]
def added935 : List (List Vertex) := [[7, 2, 0, 4, 6]]
def attachments935 : Fin tails935.length → Fin 3 := ![2, 1]
theorem accepted935 : CheapOriginalAccepted (decode 935) 1 0
    tails935 added935 attachments935 := by decide
def tails936 : List (List Vertex) := [[7, 3, 0, 4, 6, 5, 2, 1], [5, 3, 4, 7, 2, 0, 1]]
def added936 : List (List Vertex) := [[7, 1, 5]]
def attachments936 : Fin tails936.length → Fin 3 := ![2, 0]
theorem accepted936 : CheapOriginalAccepted (decode 936) 0 1
    tails936 added936 attachments936 := by decide
def tails941 : List (List Vertex) := [[6, 0, 4, 7, 3, 5, 2, 1], [5, 6, 4, 3, 0, 2, 7, 1]]
def added941 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments941 : Fin tails941.length → Fin 3 := ![1, 0]
theorem accepted941 : CheapOriginalAccepted (decode 941) 1 0
    tails941 added941 attachments941 := by decide
def tails944 : List (List Vertex) := [[7, 5, 3, 4, 0, 1, 2, 6], [6, 4, 7, 3, 0, 2]]
def added944 : List (List Vertex) := [[2, 7]]
def attachments944 : Fin tails944.length → Fin 3 := ![2, 1]
theorem accepted944 : CheapOriginalAccepted (decode 944) 2 0
    tails944 added944 attachments944 := by decide
def tails945 : List (List Vertex) := [[6, 2, 1, 0, 4, 7, 3, 5], [5, 0, 3, 4, 6, 7, 2]]
def added945 : List (List Vertex) := [[2, 0, 6]]
def attachments945 : Fin tails945.length → Fin 3 := ![1, 0]
theorem accepted945 : CheapOriginalAccepted (decode 945) 1 2
    tails945 added945 attachments945 := by decide
def tails947 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 2, 1], [6, 4, 7, 2, 0, 1]]
def added947 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments947 : Fin tails947.length → Fin 3 := ![2, 1]
theorem accepted947 : CheapOriginalAccepted (decode 947) 1 0
    tails947 added947 attachments947 := by decide
def tails948 : List (List Vertex) := [[6, 7, 4, 0, 3, 5, 1, 2], [7, 3, 4, 6, 1, 0, 2]]
def added948 : List (List Vertex) := [[6, 2, 7]]
def attachments948 : Fin tails948.length → Fin 3 := ![1, 2]
theorem accepted948 : CheapOriginalAccepted (decode 948) 1 2
    tails948 added948 attachments948 := by decide
def tails949 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 2, 1], [5, 7, 3, 0, 2, 6, 1]]
def added949 : List (List Vertex) := [[6, 4, 0, 1, 5]]
def attachments949 : Fin tails949.length → Fin 3 := ![1, 0]
theorem accepted949 : CheapOriginalAccepted (decode 949) 0 2
    tails949 added949 attachments949 := by decide
def tails950 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 4, 3], [5, 6, 1, 0, 4, 7, 3]]
def added950 : List (List Vertex) := [[7, 2, 0, 3, 5]]
def attachments950 : Fin tails950.length → Fin 3 := ![2, 0]
theorem accepted950 : CheapOriginalAccepted (decode 950) 0 1
    tails950 added950 attachments950 := by decide
def tails953 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 2, 1], [6, 5, 3, 4, 0, 2, 7, 1]]
def added953 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments953 : Fin tails953.length → Fin 3 := ![0, 1]
theorem accepted953 : CheapOriginalAccepted (decode 953) 0 1
    tails953 added953 attachments953 := by decide
def tails956 : List (List Vertex) := [[7, 4, 0, 3, 5, 6, 2, 1], [6, 4, 3, 7, 2, 0, 1]]
def added956 : List (List Vertex) := [[7, 1, 6]]
def attachments956 : Fin tails956.length → Fin 3 := ![2, 1]
theorem accepted956 : CheapOriginalAccepted (decode 956) 1 0
    tails956 added956 attachments956 := by decide
def tails964 : List (List Vertex) := [[6, 3, 7, 4, 0, 2, 1, 5], [5, 6, 4, 3, 0, 1]]
def added964 : List (List Vertex) := [[1, 6]]
def attachments964 : Fin tails964.length → Fin 3 := ![1, 0]
theorem accepted964 : CheapOriginalAccepted (decode 964) 1 0
    tails964 added964 attachments964 := by decide
def tails966 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 6, 4, 0, 1, 5]]
def added966 : List (List Vertex) := [[2, 0, 3, 7]]
def attachments966 : Fin tails966.length → Fin 3 := ![0, 2]
theorem accepted966 : CheapOriginalAccepted (decode 966) 2 1
    tails966 added966 attachments966 := by decide
def tails967 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 1, 2], [7, 4, 6, 1, 0, 2]]
def added967 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments967 : Fin tails967.length → Fin 3 := ![1, 2]
theorem accepted967 : CheapOriginalAccepted (decode 967) 2 0
    tails967 added967 attachments967 := by decide
def tails968 : List (List Vertex) := [[7, 3, 6, 4, 0, 2, 1, 5], [5, 7, 4, 3, 0, 1]]
def added968 : List (List Vertex) := [[1, 7]]
def attachments968 : Fin tails968.length → Fin 3 := ![2, 0]
theorem accepted968 : CheapOriginalAccepted (decode 968) 2 0
    tails968 added968 attachments968 := by decide
def tails969 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 7, 4, 0, 1, 5]]
def added969 : List (List Vertex) := [[2, 0, 3, 6]]
def attachments969 : Fin tails969.length → Fin 3 := ![0, 1]
theorem accepted969 : CheapOriginalAccepted (decode 969) 1 2
    tails969 added969 attachments969 := by decide
def tails971 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 1, 2], [6, 4, 7, 1, 0, 2]]
def added971 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments971 : Fin tails971.length → Fin 3 := ![2, 1]
theorem accepted971 : CheapOriginalAccepted (decode 971) 1 0
    tails971 added971 attachments971 := by decide
def tails973 : List (List Vertex) := [[6, 1, 2, 0, 3, 4, 7, 5], [5, 0, 4, 6, 3, 7, 1]]
def added973 : List (List Vertex) := [[1, 0, 6]]
def attachments973 : Fin tails973.length → Fin 3 := ![1, 0]
theorem accepted973 : CheapOriginalAccepted (decode 973) 0 2
    tails973 added973 attachments973 := by decide
def tails974 : List (List Vertex) := [[7, 1, 2, 0, 3, 4, 6, 5], [5, 0, 4, 7, 3, 6, 1]]
def added974 : List (List Vertex) := [[1, 0, 7]]
def attachments974 : Fin tails974.length → Fin 3 := ![2, 0]
theorem accepted974 : CheapOriginalAccepted (decode 974) 0 1
    tails974 added974 attachments974 := by decide
def tails976 : List (List Vertex) := [[6, 3, 7, 4, 0, 1, 2, 5], [5, 6, 4, 3, 0, 2]]
def added976 : List (List Vertex) := [[2, 6]]
def attachments976 : Fin tails976.length → Fin 3 := ![1, 0]
theorem accepted976 : CheapOriginalAccepted (decode 976) 1 0
    tails976 added976 attachments976 := by decide
def tails978 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 6, 4, 0, 2, 5]]
def added978 : List (List Vertex) := [[1, 0, 3, 7]]
def attachments978 : Fin tails978.length → Fin 3 := ![0, 2]
theorem accepted978 : CheapOriginalAccepted (decode 978) 2 1
    tails978 added978 attachments978 := by decide
def tails979 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 2, 1], [7, 4, 6, 2, 0, 1]]
def added979 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments979 : Fin tails979.length → Fin 3 := ![1, 2]
theorem accepted979 : CheapOriginalAccepted (decode 979) 2 0
    tails979 added979 attachments979 := by decide
def tails982 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 5, 2, 0, 4, 6, 1]]
def added982 : List (List Vertex) := [[5, 1, 0, 3, 7]]
def attachments982 : Fin tails982.length → Fin 3 := ![0, 2]
theorem accepted982 : CheapOriginalAccepted (decode 982) 0 2
    tails982 added982 attachments982 := by decide
def tails984 : List (List Vertex) := [[7, 6, 2, 5, 1, 0, 4, 3], [6, 4, 7, 1, 2, 0, 3]]
def added984 : List (List Vertex) := [[7, 3, 6]]
def attachments984 : Fin tails984.length → Fin 3 := ![2, 1]
theorem accepted984 : CheapOriginalAccepted (decode 984) 2 1
    tails984 added984 attachments984 := by decide
def tails985 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 3, 0, 4, 7, 5, 2]]
def added985 : List (List Vertex) := [[5, 1, 0, 2, 6]]
def attachments985 : Fin tails985.length → Fin 3 := ![0, 1]
theorem accepted985 : CheapOriginalAccepted (decode 985) 0 2
    tails985 added985 attachments985 := by decide
def tails986 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 3, 0, 4, 6, 5, 1]]
def added986 : List (List Vertex) := [[5, 2, 0, 1, 7]]
def attachments986 : Fin tails986.length → Fin 3 := ![0, 2]
theorem accepted986 : CheapOriginalAccepted (decode 986) 0 1
    tails986 added986 attachments986 := by decide
def tails988 : List (List Vertex) := [[6, 1, 0, 2, 5, 7, 4, 3], [7, 1, 2, 6, 4, 0, 3]]
def added988 : List (List Vertex) := [[6, 3, 7]]
def attachments988 : Fin tails988.length → Fin 3 := ![1, 2]
theorem accepted988 : CheapOriginalAccepted (decode 988) 2 0
    tails988 added988 attachments988 := by decide
def tails992 : List (List Vertex) := [[7, 3, 6, 4, 0, 1, 2, 5], [5, 7, 4, 3, 0, 2]]
def added992 : List (List Vertex) := [[2, 7]]
def attachments992 : Fin tails992.length → Fin 3 := ![2, 0]
theorem accepted992 : CheapOriginalAccepted (decode 992) 2 0
    tails992 added992 attachments992 := by decide
def tails993 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 7, 4, 0, 2, 5]]
def added993 : List (List Vertex) := [[1, 0, 3, 6]]
def attachments993 : Fin tails993.length → Fin 3 := ![0, 1]
theorem accepted993 : CheapOriginalAccepted (decode 993) 1 2
    tails993 added993 attachments993 := by decide
def tails995 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 2, 1], [6, 4, 7, 2, 0, 1]]
def added995 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments995 : Fin tails995.length → Fin 3 := ![2, 1]
theorem accepted995 : CheapOriginalAccepted (decode 995) 1 0
    tails995 added995 attachments995 := by decide
def tails996 : List (List Vertex) := [[6, 7, 2, 5, 1, 0, 4, 3], [7, 4, 6, 1, 2, 0, 3]]
def added996 : List (List Vertex) := [[6, 3, 7]]
def attachments996 : Fin tails996.length → Fin 3 := ![1, 2]
theorem accepted996 : CheapOriginalAccepted (decode 996) 1 2
    tails996 added996 attachments996 := by decide
def tails997 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 3, 0, 4, 7, 5, 1]]
def added997 : List (List Vertex) := [[5, 2, 0, 1, 6]]
def attachments997 : Fin tails997.length → Fin 3 := ![0, 1]
theorem accepted997 : CheapOriginalAccepted (decode 997) 0 2
    tails997 added997 attachments997 := by decide
def tails998 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 3, 0, 4, 6, 5, 2]]
def added998 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments998 : Fin tails998.length → Fin 3 := ![0, 2]
theorem accepted998 : CheapOriginalAccepted (decode 998) 0 1
    tails998 added998 attachments998 := by decide
def tails1001 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 5, 2, 0, 4, 7, 1]]
def added1001 : List (List Vertex) := [[5, 1, 0, 3, 6]]
def attachments1001 : Fin tails1001.length → Fin 3 := ![0, 1]
theorem accepted1001 : CheapOriginalAccepted (decode 1001) 0 1
    tails1001 added1001 attachments1001 := by decide
def tails1004 : List (List Vertex) := [[7, 1, 0, 2, 5, 6, 4, 3], [6, 1, 2, 7, 4, 0, 3]]
def added1004 : List (List Vertex) := [[7, 3, 6]]
def attachments1004 : Fin tails1004.length → Fin 3 := ![2, 1]
theorem accepted1004 : CheapOriginalAccepted (decode 1004) 1 0
    tails1004 added1004 attachments1004 := by decide
def tails1009 : List (List Vertex) := [[6, 2, 1, 0, 3, 4, 7, 5], [5, 0, 4, 6, 3, 7, 2]]
def added1009 : List (List Vertex) := [[2, 0, 6]]
def attachments1009 : Fin tails1009.length → Fin 3 := ![1, 0]
theorem accepted1009 : CheapOriginalAccepted (decode 1009) 0 2
    tails1009 added1009 attachments1009 := by decide
def tails1010 : List (List Vertex) := [[7, 2, 1, 0, 3, 4, 6, 5], [5, 0, 4, 7, 3, 6, 2]]
def added1010 : List (List Vertex) := [[2, 0, 7]]
def attachments1010 : Fin tails1010.length → Fin 3 := ![2, 0]
theorem accepted1010 : CheapOriginalAccepted (decode 1010) 0 1
    tails1010 added1010 attachments1010 := by decide
def tails1012 : List (List Vertex) := [[6, 2, 0, 1, 5, 7, 4, 3], [7, 2, 1, 6, 4, 0, 3]]
def added1012 : List (List Vertex) := [[6, 3, 7]]
def attachments1012 : Fin tails1012.length → Fin 3 := ![1, 2]
theorem accepted1012 : CheapOriginalAccepted (decode 1012) 2 0
    tails1012 added1012 attachments1012 := by decide
def tails1016 : List (List Vertex) := [[7, 2, 0, 1, 5, 6, 4, 3], [6, 2, 1, 7, 4, 0, 3]]
def added1016 : List (List Vertex) := [[7, 3, 6]]
def attachments1016 : Fin tails1016.length → Fin 3 := ![2, 1]
theorem accepted1016 : CheapOriginalAccepted (decode 1016) 1 0
    tails1016 added1016 attachments1016 := by decide
end Gallai.Certificate.ThreeAnchor.CheapOrbits
