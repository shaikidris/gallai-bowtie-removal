/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def decode (n : Fin 1024) : State := fun i =>
  ⟨n.val / 4 ^ i.val % 4, Nat.mod_lt _ (by decide)⟩
def highPair (n : Fin 1024) : Prop :=
  3 ≤ (Finset.univ.filter fun i : Fin 5 => i ≠ 0 ∧ decode n i ≠ 0).card ∧
    (syndrome (decode n)).card = 2
instance (n : Fin 1024) : Decidable (highPair n) := by
  unfold highPair; infer_instance
def syntheticCodes : List (Fin 1024) := [84, 86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109, 110, 111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154, 155, 157, 158, 159, 164, 166, 167, 168, 169, 171, 172, 173, 174, 181, 182, 183, 184, 185, 186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229, 230, 231, 232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 252, 253, 254, 276, 278, 279, 280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299, 301, 302, 303, 308, 309, 310, 313, 314, 315, 316, 318, 319, 324, 326, 327, 328, 329, 331, 332, 333, 334, 336, 338, 339, 344, 348, 352, 353, 355, 356, 363, 364, 366, 367, 368, 369, 370, 372, 376, 378, 379, 382, 388, 389, 391, 392, 394, 395, 397, 398, 399, 400, 401, 403, 404, 411, 412, 414, 415, 416, 418, 419, 423, 424, 428, 429, 431, 433, 434, 435, 436, 438, 439, 440, 441, 443, 444, 445, 446, 452, 453, 454, 457, 458, 459, 460, 462, 463, 464, 465, 466, 468, 472, 474, 475, 478, 481, 482, 483, 484, 486, 487, 488, 489, 491, 492, 493, 494, 496, 498, 499, 502, 504, 505, 506, 508, 532, 533, 535, 536, 538, 539, 541, 542, 543, 548, 550, 551, 552, 553, 555, 556, 557, 558, 565, 566, 567, 568, 569, 570, 572, 573, 575, 580, 581, 583, 584, 586, 587, 589, 590, 591, 592, 593, 595, 596, 603, 604, 606, 607, 608, 610, 611, 615, 616, 620, 621, 623, 625, 626, 627, 628, 630, 631, 632, 633, 635, 636, 637, 638, 644, 646, 647, 648, 649, 651, 652, 653, 654, 656, 658, 659, 663, 664, 668, 669, 671, 672, 673, 675, 676, 684, 688, 689, 690, 692, 693, 695, 696, 701, 709, 710, 711, 712, 713, 714, 716, 717, 719, 721, 722, 723, 724, 726, 727, 728, 729, 731, 732, 733, 734, 736, 737, 738, 740, 741, 743, 744, 749, 752, 753, 755, 756, 757, 758, 761, 764, 788, 789, 790, 793, 794, 795, 796, 798, 799, 805, 806, 807, 808, 809, 810, 812, 813, 815, 820, 822, 823, 824, 825, 827, 828, 829, 830, 836, 837, 838, 841, 842, 843, 844, 846, 847, 848, 849, 850, 852, 856, 858, 859, 862, 865, 866, 867, 868, 870, 871, 872, 873, 875, 876, 877, 878, 880, 882, 883, 886, 888, 889, 890, 892, 901, 902, 903, 904, 905, 906, 908, 909, 911, 913, 914, 915, 916, 918, 919, 920, 921, 923, 924, 925, 926, 928, 929, 930, 932, 933, 935, 936, 941, 944, 945, 947, 948, 949, 950, 953, 956, 964, 966, 967, 968, 969, 971, 972, 973, 974, 976, 978, 979, 982, 984, 985, 986, 988, 992, 993, 995, 996, 997, 998, 1001, 1004, 1008, 1009, 1010, 1012, 1016]
def retainedCodes : List (Fin 1024) := [341, 342, 343, 345, 346, 349, 351, 357, 358, 361, 362, 373, 375, 381, 383, 405, 406, 409, 410, 421, 422, 425, 426, 469, 471, 477, 479, 501, 503, 509, 511, 597, 598, 601, 602, 613, 614, 617, 618, 661, 662, 665, 666, 677, 678, 681, 682, 683, 686, 687, 698, 699, 702, 703, 746, 747, 750, 751, 762, 763, 766, 767, 853, 855, 861, 863, 885, 887, 893, 895, 938, 939, 942, 943, 954, 955, 958, 959, 981, 983, 989, 991, 1002, 1003, 1006, 1007, 1013, 1015, 1018, 1019, 1021, 1022, 1023]
/-- Exhaustive classification of the pair-syndrome domain. -/
theorem pair_partition : ∀ n : Fin 1024, highPair n →
    n ∈ syntheticCodes ∨ n ∈ retainedCodes := by decide

def connector84 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added84 : List (List Vertex) := [[3, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted84 : SyntheticAccepted (decode 84) 0 1
    connector84 added84 := by decide

def connector86 : List Vertex := [7, 0, 4, 3, 6]
def added86 : List (List Vertex) := [[3, 5, 1, 0, 2, 6], [3, 0, 5, 2, 1, 6]]
theorem accepted86 : SyntheticAccepted (decode 86) 2 1
    connector86 added86 := by decide

def connector87 : List Vertex := [7, 0, 4, 3, 5]
def added87 : List (List Vertex) := [[3, 6, 1, 0, 2, 5], [3, 0, 6, 2, 1, 5]]
theorem accepted87 : SyntheticAccepted (decode 87) 2 0
    connector87 added87 := by decide

def connector88 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added88 : List (List Vertex) := [[3, 6, 2, 5, 1, 0], [3, 0]]
theorem accepted88 : SyntheticAccepted (decode 88) 0 2
    connector88 added88 := by decide

def connector89 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added89 : List (List Vertex) := [[3, 5, 2, 6, 0, 1], [3, 0, 5, 1]]
theorem accepted89 : SyntheticAccepted (decode 89) 1 2
    connector89 added89 := by decide

def connector91 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added91 : List (List Vertex) := [[3, 5, 2, 6, 0, 1, 7], [3, 0, 7]]
theorem accepted91 : SyntheticAccepted (decode 91) 1 0
    connector91 added91 := by decide

def connector92 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added92 : List (List Vertex) := [[3, 5, 2, 6, 1, 0], [3, 0]]
theorem accepted92 : SyntheticAccepted (decode 92) 1 2
    connector92 added92 := by decide

def connector93 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added93 : List (List Vertex) := [[3, 6, 2, 5, 0, 1], [3, 0, 6, 1]]
theorem accepted93 : SyntheticAccepted (decode 93) 0 2
    connector93 added93 := by decide

def connector94 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added94 : List (List Vertex) := [[3, 6, 2, 5, 0, 1, 7], [3, 0, 7]]
theorem accepted94 : SyntheticAccepted (decode 94) 0 1
    connector94 added94 := by decide

def connector100 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added100 : List (List Vertex) := [[3, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted100 : SyntheticAccepted (decode 100) 0 2
    connector100 added100 := by decide

def connector101 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added101 : List (List Vertex) := [[3, 5, 1, 6, 0, 2], [3, 0, 5, 2]]
theorem accepted101 : SyntheticAccepted (decode 101) 1 2
    connector101 added101 := by decide

def connector103 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added103 : List (List Vertex) := [[3, 5, 1, 6, 0, 2, 7], [3, 0, 7]]
theorem accepted103 : SyntheticAccepted (decode 103) 1 0
    connector103 added103 := by decide

def connector104 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added104 : List (List Vertex) := [[3, 5, 2, 7, 1, 0], [3, 0]]
theorem accepted104 : SyntheticAccepted (decode 104) 0 1
    connector104 added104 := by decide

def connector106 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added106 : List (List Vertex) := [[3, 5, 1, 0, 7, 2], [3, 0, 5, 2]]
theorem accepted106 : SyntheticAccepted (decode 106) 2 1
    connector106 added106 := by decide

def connector107 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added107 : List (List Vertex) := [[3, 6, 0, 1, 5, 2, 7], [3, 0, 7]]
theorem accepted107 : SyntheticAccepted (decode 107) 2 0
    connector107 added107 := by decide

def connector109 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added109 : List (List Vertex) := [[3, 5, 0, 2, 7, 1, 6], [3, 0, 6]]
theorem accepted109 : SyntheticAccepted (decode 109) 1 0
    connector109 added109 := by decide

def connector110 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added110 : List (List Vertex) := [[3, 6, 1, 0, 5, 2, 7], [3, 0, 7]]
theorem accepted110 : SyntheticAccepted (decode 110) 0 2
    connector110 added110 := by decide

def connector111 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added111 : List (List Vertex) := [[3, 5, 2, 0, 6, 1, 7], [3, 0, 7]]
theorem accepted111 : SyntheticAccepted (decode 111) 1 2
    connector111 added111 := by decide

def connector116 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added116 : List (List Vertex) := [[3, 5, 1, 6, 2, 0], [3, 0]]
theorem accepted116 : SyntheticAccepted (decode 116) 1 2
    connector116 added116 := by decide

def connector117 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added117 : List (List Vertex) := [[3, 6, 1, 5, 0, 2], [3, 0, 6, 2]]
theorem accepted117 : SyntheticAccepted (decode 117) 0 2
    connector117 added117 := by decide

def connector118 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added118 : List (List Vertex) := [[3, 6, 1, 5, 0, 2, 7], [3, 0, 7]]
theorem accepted118 : SyntheticAccepted (decode 118) 0 1
    connector118 added118 := by decide

def connector121 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added121 : List (List Vertex) := [[3, 6, 0, 2, 7, 1, 5], [3, 0, 5]]
theorem accepted121 : SyntheticAccepted (decode 121) 0 1
    connector121 added121 := by decide

def connector122 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added122 : List (List Vertex) := [[3, 6, 2, 0, 5, 1, 7], [3, 0, 7]]
theorem accepted122 : SyntheticAccepted (decode 122) 0 2
    connector122 added122 := by decide

def connector123 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added123 : List (List Vertex) := [[3, 5, 1, 0, 6, 2, 7], [3, 0, 7]]
theorem accepted123 : SyntheticAccepted (decode 123) 1 2
    connector123 added123 := by decide

def connector124 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added124 : List (List Vertex) := [[3, 6, 2, 7, 1, 0], [3, 0]]
theorem accepted124 : SyntheticAccepted (decode 124) 1 0
    connector124 added124 := by decide

def connector126 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added126 : List (List Vertex) := [[3, 5, 0, 1, 6, 2, 7], [3, 0, 7]]
theorem accepted126 : SyntheticAccepted (decode 126) 2 1
    connector126 added126 := by decide

def connector127 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added127 : List (List Vertex) := [[3, 6, 1, 0, 7, 2], [3, 0, 6, 2]]
theorem accepted127 : SyntheticAccepted (decode 127) 2 0
    connector127 added127 := by decide

def connector148 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added148 : List (List Vertex) := [[3, 5, 2, 6, 1, 0], [3, 0]]
theorem accepted148 : SyntheticAccepted (decode 148) 0 2
    connector148 added148 := by decide

def connector149 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added149 : List (List Vertex) := [[3, 5, 1, 0, 6, 2], [3, 0, 5, 2]]
theorem accepted149 : SyntheticAccepted (decode 149) 1 2
    connector149 added149 := by decide

def connector151 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added151 : List (List Vertex) := [[3, 7, 0, 1, 5, 2, 6], [3, 0, 6]]
theorem accepted151 : SyntheticAccepted (decode 151) 1 0
    connector151 added151 := by decide

def connector152 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added152 : List (List Vertex) := [[3, 7, 1, 5, 2, 0], [3, 0]]
theorem accepted152 : SyntheticAccepted (decode 152) 0 1
    connector152 added152 := by decide

def connector154 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added154 : List (List Vertex) := [[3, 5, 1, 7, 0, 2], [3, 0, 5, 2]]
theorem accepted154 : SyntheticAccepted (decode 154) 2 1
    connector154 added154 := by decide

def connector155 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added155 : List (List Vertex) := [[3, 5, 1, 7, 0, 2, 6], [3, 0, 6]]
theorem accepted155 : SyntheticAccepted (decode 155) 2 0
    connector155 added155 := by decide

def connector157 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added157 : List (List Vertex) := [[3, 7, 1, 0, 5, 2, 6], [3, 0, 6]]
theorem accepted157 : SyntheticAccepted (decode 157) 0 1
    connector157 added157 := by decide

def connector158 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added158 : List (List Vertex) := [[3, 5, 0, 2, 6, 1, 7], [3, 0, 7]]
theorem accepted158 : SyntheticAccepted (decode 158) 2 0
    connector158 added158 := by decide

def connector159 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added159 : List (List Vertex) := [[3, 5, 2, 0, 7, 1, 6], [3, 0, 6]]
theorem accepted159 : SyntheticAccepted (decode 159) 2 1
    connector159 added159 := by decide

def connector164 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added164 : List (List Vertex) := [[3, 7, 2, 5, 1, 0], [3, 0]]
theorem accepted164 : SyntheticAccepted (decode 164) 0 1
    connector164 added164 := by decide

def connector166 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added166 : List (List Vertex) := [[3, 5, 2, 7, 0, 1], [3, 0, 5, 1]]
theorem accepted166 : SyntheticAccepted (decode 166) 2 1
    connector166 added166 := by decide

def connector167 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added167 : List (List Vertex) := [[3, 5, 2, 7, 0, 1, 6], [3, 0, 6]]
theorem accepted167 : SyntheticAccepted (decode 167) 2 0
    connector167 added167 := by decide

def connector168 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added168 : List (List Vertex) := [[3, 7, 1, 5, 2, 0], [3, 0]]
theorem accepted168 : SyntheticAccepted (decode 168) 0 2
    connector168 added168 := by decide

def connector169 : List Vertex := [6, 0, 4, 3, 7]
def added169 : List (List Vertex) := [[3, 5, 1, 0, 2, 7], [3, 0, 5, 2, 1, 7]]
theorem accepted169 : SyntheticAccepted (decode 169) 1 2
    connector169 added169 := by decide

def connector171 : List Vertex := [6, 0, 4, 3, 5]
def added171 : List (List Vertex) := [[3, 7, 1, 0, 2, 5], [3, 0, 7, 2, 1, 5]]
theorem accepted171 : SyntheticAccepted (decode 171) 1 0
    connector171 added171 := by decide

def connector172 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added172 : List (List Vertex) := [[3, 5, 2, 7, 1, 0], [3, 0]]
theorem accepted172 : SyntheticAccepted (decode 172) 2 1
    connector172 added172 := by decide

def connector173 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added173 : List (List Vertex) := [[3, 7, 2, 5, 0, 1, 6], [3, 0, 6]]
theorem accepted173 : SyntheticAccepted (decode 173) 0 2
    connector173 added173 := by decide

def connector174 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added174 : List (List Vertex) := [[3, 7, 2, 5, 0, 1], [3, 0, 7, 1]]
theorem accepted174 : SyntheticAccepted (decode 174) 0 1
    connector174 added174 := by decide

def connector181 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added181 : List (List Vertex) := [[3, 7, 2, 0, 5, 1, 6], [3, 0, 6]]
theorem accepted181 : SyntheticAccepted (decode 181) 0 1
    connector181 added181 := by decide

def connector182 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added182 : List (List Vertex) := [[3, 7, 0, 2, 6, 1, 5], [3, 0, 5]]
theorem accepted182 : SyntheticAccepted (decode 182) 0 2
    connector182 added182 := by decide

def connector183 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added183 : List (List Vertex) := [[3, 5, 1, 0, 7, 2, 6], [3, 0, 6]]
theorem accepted183 : SyntheticAccepted (decode 183) 2 1
    connector183 added183 := by decide

def connector184 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added184 : List (List Vertex) := [[3, 5, 1, 7, 2, 0], [3, 0]]
theorem accepted184 : SyntheticAccepted (decode 184) 2 1
    connector184 added184 := by decide

def connector185 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added185 : List (List Vertex) := [[3, 7, 1, 5, 0, 2, 6], [3, 0, 6]]
theorem accepted185 : SyntheticAccepted (decode 185) 0 2
    connector185 added185 := by decide

def connector186 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added186 : List (List Vertex) := [[3, 7, 1, 5, 0, 2], [3, 0, 7, 2]]
theorem accepted186 : SyntheticAccepted (decode 186) 0 1
    connector186 added186 := by decide

def connector188 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added188 : List (List Vertex) := [[3, 7, 2, 6, 1, 0], [3, 0]]
theorem accepted188 : SyntheticAccepted (decode 188) 2 0
    connector188 added188 := by decide

def connector189 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added189 : List (List Vertex) := [[3, 5, 0, 1, 7, 2, 6], [3, 0, 6]]
theorem accepted189 : SyntheticAccepted (decode 189) 1 2
    connector189 added189 := by decide

def connector191 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added191 : List (List Vertex) := [[3, 7, 1, 0, 6, 2], [3, 0, 7, 2]]
theorem accepted191 : SyntheticAccepted (decode 191) 1 0
    connector191 added191 := by decide

def connector212 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added212 : List (List Vertex) := [[3, 6, 2, 5, 1, 0], [3, 0]]
theorem accepted212 : SyntheticAccepted (decode 212) 1 2
    connector212 added212 := by decide

def connector213 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added213 : List (List Vertex) := [[3, 6, 1, 0, 5, 2], [3, 0, 6, 2]]
theorem accepted213 : SyntheticAccepted (decode 213) 0 2
    connector213 added213 := by decide

def connector214 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added214 : List (List Vertex) := [[3, 7, 0, 1, 6, 2, 5], [3, 0, 5]]
theorem accepted214 : SyntheticAccepted (decode 214) 0 1
    connector214 added214 := by decide

def connector217 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added217 : List (List Vertex) := [[3, 7, 1, 0, 6, 2, 5], [3, 0, 5]]
theorem accepted217 : SyntheticAccepted (decode 217) 1 0
    connector217 added217 := by decide

def connector218 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added218 : List (List Vertex) := [[3, 6, 2, 0, 7, 1, 5], [3, 0, 5]]
theorem accepted218 : SyntheticAccepted (decode 218) 2 0
    connector218 added218 := by decide

def connector219 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added219 : List (List Vertex) := [[3, 6, 0, 2, 5, 1, 7], [3, 0, 7]]
theorem accepted219 : SyntheticAccepted (decode 219) 2 1
    connector219 added219 := by decide

def connector220 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added220 : List (List Vertex) := [[3, 7, 1, 6, 2, 0], [3, 0]]
theorem accepted220 : SyntheticAccepted (decode 220) 1 0
    connector220 added220 := by decide

def connector222 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added222 : List (List Vertex) := [[3, 6, 1, 7, 0, 2, 5], [3, 0, 5]]
theorem accepted222 : SyntheticAccepted (decode 222) 2 1
    connector222 added222 := by decide

def connector223 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added223 : List (List Vertex) := [[3, 6, 1, 7, 0, 2], [3, 0, 6, 2]]
theorem accepted223 : SyntheticAccepted (decode 223) 2 0
    connector223 added223 := by decide

def connector229 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added229 : List (List Vertex) := [[3, 7, 2, 0, 6, 1, 5], [3, 0, 5]]
theorem accepted229 : SyntheticAccepted (decode 229) 1 0
    connector229 added229 := by decide

def connector230 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added230 : List (List Vertex) := [[3, 6, 1, 0, 7, 2, 5], [3, 0, 5]]
theorem accepted230 : SyntheticAccepted (decode 230) 2 0
    connector230 added230 := by decide

def connector231 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added231 : List (List Vertex) := [[3, 7, 0, 2, 5, 1, 6], [3, 0, 6]]
theorem accepted231 : SyntheticAccepted (decode 231) 1 2
    connector231 added231 := by decide

def connector232 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added232 : List (List Vertex) := [[3, 7, 2, 5, 1, 0], [3, 0]]
theorem accepted232 : SyntheticAccepted (decode 232) 2 1
    connector232 added232 := by decide

def connector233 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added233 : List (List Vertex) := [[3, 6, 0, 1, 7, 2, 5], [3, 0, 5]]
theorem accepted233 : SyntheticAccepted (decode 233) 0 2
    connector233 added233 := by decide

def connector234 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added234 : List (List Vertex) := [[3, 7, 1, 0, 5, 2], [3, 0, 7, 2]]
theorem accepted234 : SyntheticAccepted (decode 234) 0 1
    connector234 added234 := by decide

def connector236 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added236 : List (List Vertex) := [[3, 6, 1, 7, 2, 0], [3, 0]]
theorem accepted236 : SyntheticAccepted (decode 236) 2 0
    connector236 added236 := by decide

def connector237 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added237 : List (List Vertex) := [[3, 7, 1, 6, 0, 2, 5], [3, 0, 5]]
theorem accepted237 : SyntheticAccepted (decode 237) 1 2
    connector237 added237 := by decide

def connector239 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added239 : List (List Vertex) := [[3, 7, 1, 6, 0, 2], [3, 0, 7, 2]]
theorem accepted239 : SyntheticAccepted (decode 239) 1 0
    connector239 added239 := by decide

def connector244 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added244 : List (List Vertex) := [[3, 7, 2, 6, 1, 0], [3, 0]]
theorem accepted244 : SyntheticAccepted (decode 244) 1 0
    connector244 added244 := by decide

def connector246 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added246 : List (List Vertex) := [[3, 6, 2, 7, 0, 1, 5], [3, 0, 5]]
theorem accepted246 : SyntheticAccepted (decode 246) 2 1
    connector246 added246 := by decide

def connector247 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added247 : List (List Vertex) := [[3, 6, 2, 7, 0, 1], [3, 0, 6, 1]]
theorem accepted247 : SyntheticAccepted (decode 247) 2 0
    connector247 added247 := by decide

def connector248 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added248 : List (List Vertex) := [[3, 6, 2, 7, 1, 0], [3, 0]]
theorem accepted248 : SyntheticAccepted (decode 248) 2 0
    connector248 added248 := by decide

def connector249 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added249 : List (List Vertex) := [[3, 7, 2, 6, 0, 1, 5], [3, 0, 5]]
theorem accepted249 : SyntheticAccepted (decode 249) 1 2
    connector249 added249 := by decide

def connector251 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added251 : List (List Vertex) := [[3, 7, 2, 6, 0, 1], [3, 0, 7, 1]]
theorem accepted251 : SyntheticAccepted (decode 251) 1 0
    connector251 added251 := by decide

def connector252 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added252 : List (List Vertex) := [[3, 7, 1, 6, 2, 0], [3, 0]]
theorem accepted252 : SyntheticAccepted (decode 252) 1 2
    connector252 added252 := by decide

def connector253 : List Vertex := [5, 0, 4, 3, 7]
def added253 : List (List Vertex) := [[3, 6, 1, 0, 2, 7], [3, 0, 6, 2, 1, 7]]
theorem accepted253 : SyntheticAccepted (decode 253) 0 2
    connector253 added253 := by decide

def connector254 : List Vertex := [5, 0, 4, 3, 6]
def added254 : List (List Vertex) := [[3, 7, 1, 0, 2, 6], [3, 0, 7, 2, 1, 6]]
theorem accepted254 : SyntheticAccepted (decode 254) 0 1
    connector254 added254 := by decide

def connector276 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added276 : List (List Vertex) := [[4, 6, 1, 5, 2, 0], [4, 0]]
theorem accepted276 : SyntheticAccepted (decode 276) 0 1
    connector276 added276 := by decide

def connector278 : List Vertex := [7, 0, 3, 4, 6]
def added278 : List (List Vertex) := [[4, 5, 1, 0, 2, 6], [4, 0, 5, 2, 1, 6]]
theorem accepted278 : SyntheticAccepted (decode 278) 2 1
    connector278 added278 := by decide

def connector279 : List Vertex := [7, 0, 3, 4, 5]
def added279 : List (List Vertex) := [[4, 6, 1, 0, 2, 5], [4, 0, 6, 2, 1, 5]]
theorem accepted279 : SyntheticAccepted (decode 279) 2 0
    connector279 added279 := by decide

def connector280 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added280 : List (List Vertex) := [[4, 6, 2, 5, 1, 0], [4, 0]]
theorem accepted280 : SyntheticAccepted (decode 280) 0 2
    connector280 added280 := by decide

def connector281 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added281 : List (List Vertex) := [[4, 5, 2, 6, 0, 1], [4, 0, 5, 1]]
theorem accepted281 : SyntheticAccepted (decode 281) 1 2
    connector281 added281 := by decide

def connector283 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added283 : List (List Vertex) := [[4, 5, 2, 6, 0, 1, 7], [4, 0, 7]]
theorem accepted283 : SyntheticAccepted (decode 283) 1 0
    connector283 added283 := by decide

def connector284 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added284 : List (List Vertex) := [[4, 5, 2, 6, 1, 0], [4, 0]]
theorem accepted284 : SyntheticAccepted (decode 284) 1 2
    connector284 added284 := by decide

def connector285 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added285 : List (List Vertex) := [[4, 6, 2, 5, 0, 1], [4, 0, 6, 1]]
theorem accepted285 : SyntheticAccepted (decode 285) 0 2
    connector285 added285 := by decide

def connector286 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added286 : List (List Vertex) := [[4, 6, 2, 5, 0, 1, 7], [4, 0, 7]]
theorem accepted286 : SyntheticAccepted (decode 286) 0 1
    connector286 added286 := by decide

def connector292 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added292 : List (List Vertex) := [[4, 6, 1, 5, 2, 0], [4, 0]]
theorem accepted292 : SyntheticAccepted (decode 292) 0 2
    connector292 added292 := by decide

def connector293 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added293 : List (List Vertex) := [[4, 5, 1, 6, 0, 2], [4, 0, 5, 2]]
theorem accepted293 : SyntheticAccepted (decode 293) 1 2
    connector293 added293 := by decide

def connector295 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added295 : List (List Vertex) := [[4, 5, 1, 6, 0, 2, 7], [4, 0, 7]]
theorem accepted295 : SyntheticAccepted (decode 295) 1 0
    connector295 added295 := by decide

def connector296 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added296 : List (List Vertex) := [[4, 5, 2, 7, 1, 0], [4, 0]]
theorem accepted296 : SyntheticAccepted (decode 296) 0 1
    connector296 added296 := by decide

def connector298 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added298 : List (List Vertex) := [[4, 5, 1, 0, 7, 2], [4, 0, 5, 2]]
theorem accepted298 : SyntheticAccepted (decode 298) 2 1
    connector298 added298 := by decide

def connector299 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added299 : List (List Vertex) := [[4, 6, 0, 1, 5, 2, 7], [4, 0, 7]]
theorem accepted299 : SyntheticAccepted (decode 299) 2 0
    connector299 added299 := by decide

def connector301 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added301 : List (List Vertex) := [[4, 5, 0, 2, 7, 1, 6], [4, 0, 6]]
theorem accepted301 : SyntheticAccepted (decode 301) 1 0
    connector301 added301 := by decide

def connector302 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added302 : List (List Vertex) := [[4, 6, 1, 0, 5, 2, 7], [4, 0, 7]]
theorem accepted302 : SyntheticAccepted (decode 302) 0 2
    connector302 added302 := by decide

def connector303 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added303 : List (List Vertex) := [[4, 5, 2, 0, 6, 1, 7], [4, 0, 7]]
theorem accepted303 : SyntheticAccepted (decode 303) 1 2
    connector303 added303 := by decide

def connector308 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added308 : List (List Vertex) := [[4, 5, 1, 6, 2, 0], [4, 0]]
theorem accepted308 : SyntheticAccepted (decode 308) 1 2
    connector308 added308 := by decide

def connector309 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added309 : List (List Vertex) := [[4, 6, 1, 5, 0, 2], [4, 0, 6, 2]]
theorem accepted309 : SyntheticAccepted (decode 309) 0 2
    connector309 added309 := by decide

def connector310 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added310 : List (List Vertex) := [[4, 6, 1, 5, 0, 2, 7], [4, 0, 7]]
theorem accepted310 : SyntheticAccepted (decode 310) 0 1
    connector310 added310 := by decide

def connector313 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added313 : List (List Vertex) := [[4, 6, 0, 2, 7, 1, 5], [4, 0, 5]]
theorem accepted313 : SyntheticAccepted (decode 313) 0 1
    connector313 added313 := by decide

def connector314 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added314 : List (List Vertex) := [[4, 6, 2, 0, 5, 1, 7], [4, 0, 7]]
theorem accepted314 : SyntheticAccepted (decode 314) 0 2
    connector314 added314 := by decide

def connector315 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added315 : List (List Vertex) := [[4, 5, 1, 0, 6, 2, 7], [4, 0, 7]]
theorem accepted315 : SyntheticAccepted (decode 315) 1 2
    connector315 added315 := by decide

def connector316 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added316 : List (List Vertex) := [[4, 6, 2, 7, 1, 0], [4, 0]]
theorem accepted316 : SyntheticAccepted (decode 316) 1 0
    connector316 added316 := by decide

def connector318 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added318 : List (List Vertex) := [[4, 5, 0, 1, 6, 2, 7], [4, 0, 7]]
theorem accepted318 : SyntheticAccepted (decode 318) 2 1
    connector318 added318 := by decide

def connector319 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added319 : List (List Vertex) := [[4, 6, 1, 0, 7, 2], [4, 0, 6, 2]]
theorem accepted319 : SyntheticAccepted (decode 319) 2 0
    connector319 added319 := by decide

def connector324 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added324 : List (List Vertex) := [[1, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted324 : SyntheticAccepted (decode 324) 0 1
    connector324 added324 := by decide

def connector326 : List Vertex := [7, 0, 2, 1, 6]
def added326 : List (List Vertex) := [[1, 5, 3, 0, 4, 6], [1, 0, 5, 4, 3, 6]]
theorem accepted326 : SyntheticAccepted (decode 326) 2 1
    connector326 added326 := by decide

def connector327 : List Vertex := [7, 0, 2, 1, 5]
def added327 : List (List Vertex) := [[1, 6, 3, 0, 4, 5], [1, 0, 6, 4, 3, 5]]
theorem accepted327 : SyntheticAccepted (decode 327) 2 0
    connector327 added327 := by decide

def connector328 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added328 : List (List Vertex) := [[1, 5, 4, 6, 3, 0], [1, 0]]
theorem accepted328 : SyntheticAccepted (decode 328) 0 2
    connector328 added328 := by decide

def connector329 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added329 : List (List Vertex) := [[1, 5, 3, 0, 6, 4], [1, 0, 5, 4]]
theorem accepted329 : SyntheticAccepted (decode 329) 1 2
    connector329 added329 := by decide

def connector331 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added331 : List (List Vertex) := [[1, 7, 0, 3, 5, 4, 6], [1, 0, 6]]
theorem accepted331 : SyntheticAccepted (decode 331) 1 0
    connector331 added331 := by decide

def connector332 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added332 : List (List Vertex) := [[1, 6, 4, 5, 3, 0], [1, 0]]
theorem accepted332 : SyntheticAccepted (decode 332) 1 2
    connector332 added332 := by decide

def connector333 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added333 : List (List Vertex) := [[1, 6, 3, 0, 5, 4], [1, 0, 6, 4]]
theorem accepted333 : SyntheticAccepted (decode 333) 0 2
    connector333 added333 := by decide

def connector334 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added334 : List (List Vertex) := [[1, 7, 0, 3, 6, 4, 5], [1, 0, 5]]
theorem accepted334 : SyntheticAccepted (decode 334) 0 1
    connector334 added334 := by decide

def connector336 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added336 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted336 : SyntheticAccepted (decode 336) 0 1
    connector336 added336 := by decide

def connector338 : List Vertex := [7, 0, 1, 2, 6]
def added338 : List (List Vertex) := [[2, 5, 3, 0, 4, 6], [2, 0, 5, 4, 3, 6]]
theorem accepted338 : SyntheticAccepted (decode 338) 2 1
    connector338 added338 := by decide

def connector339 : List Vertex := [7, 0, 1, 2, 5]
def added339 : List (List Vertex) := [[2, 6, 3, 0, 4, 5], [2, 0, 6, 4, 3, 5]]
theorem accepted339 : SyntheticAccepted (decode 339) 2 0
    connector339 added339 := by decide

def connector344 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added344 : List (List Vertex) := [[3, 0, 1, 5, 4, 6, 2], [3, 5, 2]]
theorem accepted344 : SyntheticAccepted (decode 344) 1 2
    connector344 added344 := by decide

def connector348 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added348 : List (List Vertex) := [[3, 0, 1, 6, 4, 5, 2], [3, 6, 2]]
theorem accepted348 : SyntheticAccepted (decode 348) 0 2
    connector348 added348 := by decide

def connector352 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added352 : List (List Vertex) := [[2, 5, 4, 6, 3, 0], [2, 0]]
theorem accepted352 : SyntheticAccepted (decode 352) 0 2
    connector352 added352 := by decide

def connector353 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added353 : List (List Vertex) := [[2, 5, 3, 0, 6, 4], [2, 0, 5, 4]]
theorem accepted353 : SyntheticAccepted (decode 353) 1 2
    connector353 added353 := by decide

def connector355 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added355 : List (List Vertex) := [[2, 7, 0, 3, 5, 4, 6], [2, 0, 6]]
theorem accepted355 : SyntheticAccepted (decode 355) 1 0
    connector355 added355 := by decide

def connector356 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added356 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 1], [3, 5, 1]]
theorem accepted356 : SyntheticAccepted (decode 356) 1 2
    connector356 added356 := by decide

def connector363 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added363 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 3], [1, 0, 4, 5, 3]]
theorem accepted363 : SyntheticAccepted (decode 363) 2 1
    connector363 added363 := by decide

def connector364 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added364 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 2, 0], [3, 0]]
theorem accepted364 : SyntheticAccepted (decode 364) 1 0
    connector364 added364 := by decide

def connector366 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added366 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 0, 4], [2, 0, 5, 4]]
theorem accepted366 : SyntheticAccepted (decode 366) 2 1
    connector366 added366 := by decide

def connector367 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added367 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 0, 4], [1, 0, 6, 4]]
theorem accepted367 : SyntheticAccepted (decode 367) 2 0
    connector367 added367 := by decide

def connector368 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added368 : List (List Vertex) := [[2, 6, 4, 5, 3, 0], [2, 0]]
theorem accepted368 : SyntheticAccepted (decode 368) 1 2
    connector368 added368 := by decide

def connector369 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added369 : List (List Vertex) := [[2, 6, 3, 0, 5, 4], [2, 0, 6, 4]]
theorem accepted369 : SyntheticAccepted (decode 369) 0 2
    connector369 added369 := by decide

def connector370 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added370 : List (List Vertex) := [[2, 7, 0, 3, 6, 4, 5], [2, 0, 5]]
theorem accepted370 : SyntheticAccepted (decode 370) 0 1
    connector370 added370 := by decide

def connector372 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added372 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [3, 6, 1]]
theorem accepted372 : SyntheticAccepted (decode 372) 0 2
    connector372 added372 := by decide

def connector376 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added376 : List (List Vertex) := [[3, 6, 4, 5, 1, 7, 2, 0], [3, 0]]
theorem accepted376 : SyntheticAccepted (decode 376) 0 1
    connector376 added376 := by decide

def connector378 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added378 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 0, 4], [1, 0, 5, 4]]
theorem accepted378 : SyntheticAccepted (decode 378) 2 1
    connector378 added378 := by decide

def connector379 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added379 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 0, 4], [2, 0, 6, 4]]
theorem accepted379 : SyntheticAccepted (decode 379) 2 0
    connector379 added379 := by decide

def connector382 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added382 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 3], [1, 0, 4, 6, 3]]
theorem accepted382 : SyntheticAccepted (decode 382) 2 0
    connector382 added382 := by decide

def connector388 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added388 : List (List Vertex) := [[1, 6, 4, 5, 3, 0], [1, 0]]
theorem accepted388 : SyntheticAccepted (decode 388) 0 2
    connector388 added388 := by decide

def connector389 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added389 : List (List Vertex) := [[1, 5, 4, 6, 0, 3], [1, 0, 5, 3]]
theorem accepted389 : SyntheticAccepted (decode 389) 1 2
    connector389 added389 := by decide

def connector391 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added391 : List (List Vertex) := [[1, 5, 4, 6, 0, 3, 7], [1, 0, 7]]
theorem accepted391 : SyntheticAccepted (decode 391) 1 0
    connector391 added391 := by decide

def connector392 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added392 : List (List Vertex) := [[1, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted392 : SyntheticAccepted (decode 392) 0 1
    connector392 added392 := by decide

def connector394 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added394 : List (List Vertex) := [[1, 5, 3, 7, 0, 4], [1, 0, 5, 4]]
theorem accepted394 : SyntheticAccepted (decode 394) 2 1
    connector394 added394 := by decide

def connector395 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added395 : List (List Vertex) := [[1, 5, 3, 7, 0, 4, 6], [1, 0, 6]]
theorem accepted395 : SyntheticAccepted (decode 395) 2 0
    connector395 added395 := by decide

def connector397 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added397 : List (List Vertex) := [[1, 7, 3, 0, 6, 4, 5], [1, 0, 5]]
theorem accepted397 : SyntheticAccepted (decode 397) 1 0
    connector397 added397 := by decide

def connector398 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added398 : List (List Vertex) := [[1, 6, 4, 0, 7, 3, 5], [1, 0, 5]]
theorem accepted398 : SyntheticAccepted (decode 398) 2 0
    connector398 added398 := by decide

def connector399 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added399 : List (List Vertex) := [[1, 6, 0, 4, 5, 3, 7], [1, 0, 7]]
theorem accepted399 : SyntheticAccepted (decode 399) 2 1
    connector399 added399 := by decide

def connector400 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added400 : List (List Vertex) := [[2, 6, 4, 5, 3, 0], [2, 0]]
theorem accepted400 : SyntheticAccepted (decode 400) 0 2
    connector400 added400 := by decide

def connector401 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added401 : List (List Vertex) := [[2, 5, 4, 6, 0, 3], [2, 0, 5, 3]]
theorem accepted401 : SyntheticAccepted (decode 401) 1 2
    connector401 added401 := by decide

def connector403 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added403 : List (List Vertex) := [[2, 5, 4, 6, 0, 3, 7], [2, 0, 7]]
theorem accepted403 : SyntheticAccepted (decode 403) 1 0
    connector403 added403 := by decide

def connector404 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added404 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 4], [1, 5, 4]]
theorem accepted404 : SyntheticAccepted (decode 404) 1 2
    connector404 added404 := by decide

def connector411 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added411 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 3], [1, 0, 4, 5, 3]]
theorem accepted411 : SyntheticAccepted (decode 411) 2 1
    connector411 added411 := by decide

def connector412 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added412 : List (List Vertex) := [[2, 5, 4, 6, 1, 7, 3, 0], [2, 0]]
theorem accepted412 : SyntheticAccepted (decode 412) 1 0
    connector412 added412 := by decide

def connector414 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added414 : List (List Vertex) := [[4, 6, 2, 5, 3, 0, 1, 7], [4, 5, 0, 7]]
theorem accepted414 : SyntheticAccepted (decode 414) 2 1
    connector414 added414 := by decide

def connector415 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added415 : List (List Vertex) := [[2, 5, 4, 6, 1, 0, 3, 7], [2, 6, 0, 7]]
theorem accepted415 : SyntheticAccepted (decode 415) 2 0
    connector415 added415 := by decide

def connector416 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added416 : List (List Vertex) := [[2, 7, 3, 5, 4, 0], [2, 0]]
theorem accepted416 : SyntheticAccepted (decode 416) 0 1
    connector416 added416 := by decide

def connector418 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added418 : List (List Vertex) := [[2, 5, 3, 7, 0, 4], [2, 0, 5, 4]]
theorem accepted418 : SyntheticAccepted (decode 418) 2 1
    connector418 added418 := by decide

def connector419 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added419 : List (List Vertex) := [[2, 5, 3, 7, 0, 4, 6], [2, 0, 6]]
theorem accepted419 : SyntheticAccepted (decode 419) 2 0
    connector419 added419 := by decide

def connector423 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added423 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 4], [1, 0, 3, 5, 4]]
theorem accepted423 : SyntheticAccepted (decode 423) 1 2
    connector423 added423 := by decide

def connector424 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added424 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [1, 5, 3]]
theorem accepted424 : SyntheticAccepted (decode 424) 2 1
    connector424 added424 := by decide

def connector428 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added428 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 4, 0], [2, 0]]
theorem accepted428 : SyntheticAccepted (decode 428) 2 0
    connector428 added428 := by decide

def connector429 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added429 : List (List Vertex) := [[3, 7, 2, 5, 4, 0, 1, 6], [3, 5, 0, 6]]
theorem accepted429 : SyntheticAccepted (decode 429) 1 2
    connector429 added429 := by decide

def connector431 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added431 : List (List Vertex) := [[2, 5, 3, 7, 1, 0, 4, 6], [2, 7, 0, 6]]
theorem accepted431 : SyntheticAccepted (decode 431) 1 0
    connector431 added431 := by decide

def connector433 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added433 : List (List Vertex) := [[2, 7, 3, 0, 6, 4, 5], [2, 0, 5]]
theorem accepted433 : SyntheticAccepted (decode 433) 1 0
    connector433 added433 := by decide

def connector434 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added434 : List (List Vertex) := [[2, 6, 4, 0, 7, 3, 5], [2, 0, 5]]
theorem accepted434 : SyntheticAccepted (decode 434) 2 0
    connector434 added434 := by decide

def connector435 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added435 : List (List Vertex) := [[2, 6, 0, 4, 5, 3, 7], [2, 0, 7]]
theorem accepted435 : SyntheticAccepted (decode 435) 2 1
    connector435 added435 := by decide

def connector436 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added436 : List (List Vertex) := [[1, 5, 4, 6, 2, 7, 3, 0], [1, 0]]
theorem accepted436 : SyntheticAccepted (decode 436) 1 0
    connector436 added436 := by decide

def connector438 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added438 : List (List Vertex) := [[4, 6, 1, 5, 3, 0, 2, 7], [4, 5, 0, 7]]
theorem accepted438 : SyntheticAccepted (decode 438) 2 1
    connector438 added438 := by decide

def connector439 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added439 : List (List Vertex) := [[1, 5, 4, 6, 2, 0, 3, 7], [1, 6, 0, 7]]
theorem accepted439 : SyntheticAccepted (decode 439) 2 0
    connector439 added439 := by decide

def connector440 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added440 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 4, 0], [1, 0]]
theorem accepted440 : SyntheticAccepted (decode 440) 2 0
    connector440 added440 := by decide

def connector441 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added441 : List (List Vertex) := [[3, 7, 1, 5, 4, 0, 2, 6], [3, 5, 0, 6]]
theorem accepted441 : SyntheticAccepted (decode 441) 1 2
    connector441 added441 := by decide

def connector443 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added443 : List (List Vertex) := [[1, 5, 3, 7, 2, 0, 4, 6], [1, 7, 0, 6]]
theorem accepted443 : SyntheticAccepted (decode 443) 1 0
    connector443 added443 := by decide

def connector444 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added444 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted444 : SyntheticAccepted (decode 444) 2 1
    connector444 added444 := by decide

def connector445 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added445 : List (List Vertex) := [[4, 6, 1, 7, 3, 5, 0, 2], [4, 0, 6, 2]]
theorem accepted445 : SyntheticAccepted (decode 445) 0 2
    connector445 added445 := by decide

def connector446 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added446 : List (List Vertex) := [[3, 7, 1, 6, 4, 5, 0, 2], [3, 0, 7, 2]]
theorem accepted446 : SyntheticAccepted (decode 446) 0 1
    connector446 added446 := by decide

def connector452 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added452 : List (List Vertex) := [[1, 5, 4, 6, 3, 0], [1, 0]]
theorem accepted452 : SyntheticAccepted (decode 452) 1 2
    connector452 added452 := by decide

def connector453 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added453 : List (List Vertex) := [[1, 6, 4, 5, 0, 3], [1, 0, 6, 3]]
theorem accepted453 : SyntheticAccepted (decode 453) 0 2
    connector453 added453 := by decide

def connector454 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added454 : List (List Vertex) := [[1, 6, 4, 5, 0, 3, 7], [1, 0, 7]]
theorem accepted454 : SyntheticAccepted (decode 454) 0 1
    connector454 added454 := by decide

def connector457 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added457 : List (List Vertex) := [[1, 7, 3, 0, 5, 4, 6], [1, 0, 6]]
theorem accepted457 : SyntheticAccepted (decode 457) 0 1
    connector457 added457 := by decide

def connector458 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added458 : List (List Vertex) := [[1, 5, 0, 4, 6, 3, 7], [1, 0, 7]]
theorem accepted458 : SyntheticAccepted (decode 458) 2 0
    connector458 added458 := by decide

def connector459 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added459 : List (List Vertex) := [[1, 5, 4, 0, 7, 3, 6], [1, 0, 6]]
theorem accepted459 : SyntheticAccepted (decode 459) 2 1
    connector459 added459 := by decide

def connector460 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added460 : List (List Vertex) := [[1, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted460 : SyntheticAccepted (decode 460) 1 0
    connector460 added460 := by decide

def connector462 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added462 : List (List Vertex) := [[1, 6, 3, 7, 0, 4, 5], [1, 0, 5]]
theorem accepted462 : SyntheticAccepted (decode 462) 2 1
    connector462 added462 := by decide

def connector463 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added463 : List (List Vertex) := [[1, 6, 3, 7, 0, 4], [1, 0, 6, 4]]
theorem accepted463 : SyntheticAccepted (decode 463) 2 0
    connector463 added463 := by decide

def connector464 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added464 : List (List Vertex) := [[2, 5, 4, 6, 3, 0], [2, 0]]
theorem accepted464 : SyntheticAccepted (decode 464) 1 2
    connector464 added464 := by decide

def connector465 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added465 : List (List Vertex) := [[2, 6, 4, 5, 0, 3], [2, 0, 6, 3]]
theorem accepted465 : SyntheticAccepted (decode 465) 0 2
    connector465 added465 := by decide

def connector466 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added466 : List (List Vertex) := [[2, 6, 4, 5, 0, 3, 7], [2, 0, 7]]
theorem accepted466 : SyntheticAccepted (decode 466) 0 1
    connector466 added466 := by decide

def connector468 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added468 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 4], [1, 6, 4]]
theorem accepted468 : SyntheticAccepted (decode 468) 0 2
    connector468 added468 := by decide

def connector472 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added472 : List (List Vertex) := [[2, 6, 4, 5, 1, 7, 3, 0], [2, 0]]
theorem accepted472 : SyntheticAccepted (decode 472) 0 1
    connector472 added472 := by decide

def connector474 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added474 : List (List Vertex) := [[2, 6, 4, 5, 1, 0, 3, 7], [2, 5, 0, 7]]
theorem accepted474 : SyntheticAccepted (decode 474) 2 1
    connector474 added474 := by decide

def connector475 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added475 : List (List Vertex) := [[4, 5, 2, 6, 3, 0, 1, 7], [4, 6, 0, 7]]
theorem accepted475 : SyntheticAccepted (decode 475) 2 0
    connector475 added475 := by decide

def connector478 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added478 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 3], [1, 0, 4, 6, 3]]
theorem accepted478 : SyntheticAccepted (decode 478) 2 0
    connector478 added478 := by decide

def connector481 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added481 : List (List Vertex) := [[2, 7, 3, 0, 5, 4, 6], [2, 0, 6]]
theorem accepted481 : SyntheticAccepted (decode 481) 0 1
    connector481 added481 := by decide

def connector482 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added482 : List (List Vertex) := [[2, 5, 0, 4, 6, 3, 7], [2, 0, 7]]
theorem accepted482 : SyntheticAccepted (decode 482) 2 0
    connector482 added482 := by decide

def connector483 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added483 : List (List Vertex) := [[2, 5, 4, 0, 7, 3, 6], [2, 0, 6]]
theorem accepted483 : SyntheticAccepted (decode 483) 2 1
    connector483 added483 := by decide

def connector484 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added484 : List (List Vertex) := [[1, 6, 4, 5, 2, 7, 3, 0], [1, 0]]
theorem accepted484 : SyntheticAccepted (decode 484) 0 1
    connector484 added484 := by decide

def connector486 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added486 : List (List Vertex) := [[1, 6, 4, 5, 2, 0, 3, 7], [1, 5, 0, 7]]
theorem accepted486 : SyntheticAccepted (decode 486) 2 1
    connector486 added486 := by decide

def connector487 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added487 : List (List Vertex) := [[4, 5, 1, 6, 3, 0, 2, 7], [4, 6, 0, 7]]
theorem accepted487 : SyntheticAccepted (decode 487) 2 0
    connector487 added487 := by decide

def connector488 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added488 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted488 : SyntheticAccepted (decode 488) 2 0
    connector488 added488 := by decide

def connector489 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added489 : List (List Vertex) := [[4, 5, 1, 7, 3, 6, 0, 2], [4, 0, 5, 2]]
theorem accepted489 : SyntheticAccepted (decode 489) 1 2
    connector489 added489 := by decide

def connector491 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added491 : List (List Vertex) := [[3, 7, 1, 5, 4, 6, 0, 2], [3, 0, 7, 2]]
theorem accepted491 : SyntheticAccepted (decode 491) 1 0
    connector491 added491 := by decide

def connector492 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added492 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 4, 0], [1, 0]]
theorem accepted492 : SyntheticAccepted (decode 492) 2 1
    connector492 added492 := by decide

def connector493 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added493 : List (List Vertex) := [[3, 7, 1, 6, 4, 0, 2, 5], [3, 6, 0, 5]]
theorem accepted493 : SyntheticAccepted (decode 493) 0 2
    connector493 added493 := by decide

def connector494 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added494 : List (List Vertex) := [[1, 6, 3, 7, 2, 0, 4, 5], [1, 7, 0, 5]]
theorem accepted494 : SyntheticAccepted (decode 494) 0 1
    connector494 added494 := by decide

def connector496 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added496 : List (List Vertex) := [[2, 7, 3, 6, 4, 0], [2, 0]]
theorem accepted496 : SyntheticAccepted (decode 496) 1 0
    connector496 added496 := by decide

def connector498 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added498 : List (List Vertex) := [[2, 6, 3, 7, 0, 4, 5], [2, 0, 5]]
theorem accepted498 : SyntheticAccepted (decode 498) 2 1
    connector498 added498 := by decide

def connector499 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added499 : List (List Vertex) := [[2, 6, 3, 7, 0, 4], [2, 0, 6, 4]]
theorem accepted499 : SyntheticAccepted (decode 499) 2 0
    connector499 added499 := by decide

def connector502 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added502 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 4], [1, 0, 3, 6, 4]]
theorem accepted502 : SyntheticAccepted (decode 502) 0 2
    connector502 added502 := by decide

def connector504 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added504 : List (List Vertex) := [[2, 6, 3, 7, 1, 5, 4, 0], [2, 0]]
theorem accepted504 : SyntheticAccepted (decode 504) 2 1
    connector504 added504 := by decide

def connector505 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added505 : List (List Vertex) := [[3, 7, 2, 6, 4, 0, 1, 5], [3, 6, 0, 5]]
theorem accepted505 : SyntheticAccepted (decode 505) 0 2
    connector505 added505 := by decide

def connector506 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added506 : List (List Vertex) := [[2, 6, 3, 7, 1, 0, 4, 5], [2, 7, 0, 5]]
theorem accepted506 : SyntheticAccepted (decode 506) 0 1
    connector506 added506 := by decide

def connector508 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added508 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 3], [1, 6, 3]]
theorem accepted508 : SyntheticAccepted (decode 508) 2 0
    connector508 added508 := by decide

def connector532 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added532 : List (List Vertex) := [[4, 5, 2, 6, 1, 0], [4, 0]]
theorem accepted532 : SyntheticAccepted (decode 532) 0 2
    connector532 added532 := by decide

def connector533 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added533 : List (List Vertex) := [[4, 5, 1, 0, 6, 2], [4, 0, 5, 2]]
theorem accepted533 : SyntheticAccepted (decode 533) 1 2
    connector533 added533 := by decide

def connector535 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added535 : List (List Vertex) := [[4, 7, 0, 1, 5, 2, 6], [4, 0, 6]]
theorem accepted535 : SyntheticAccepted (decode 535) 1 0
    connector535 added535 := by decide

def connector536 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added536 : List (List Vertex) := [[4, 7, 1, 5, 2, 0], [4, 0]]
theorem accepted536 : SyntheticAccepted (decode 536) 0 1
    connector536 added536 := by decide

def connector538 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added538 : List (List Vertex) := [[4, 5, 1, 7, 0, 2], [4, 0, 5, 2]]
theorem accepted538 : SyntheticAccepted (decode 538) 2 1
    connector538 added538 := by decide

def connector539 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added539 : List (List Vertex) := [[4, 5, 1, 7, 0, 2, 6], [4, 0, 6]]
theorem accepted539 : SyntheticAccepted (decode 539) 2 0
    connector539 added539 := by decide

def connector541 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added541 : List (List Vertex) := [[4, 7, 1, 0, 5, 2, 6], [4, 0, 6]]
theorem accepted541 : SyntheticAccepted (decode 541) 0 1
    connector541 added541 := by decide

def connector542 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added542 : List (List Vertex) := [[4, 5, 0, 2, 6, 1, 7], [4, 0, 7]]
theorem accepted542 : SyntheticAccepted (decode 542) 2 0
    connector542 added542 := by decide

def connector543 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added543 : List (List Vertex) := [[4, 5, 2, 0, 7, 1, 6], [4, 0, 6]]
theorem accepted543 : SyntheticAccepted (decode 543) 2 1
    connector543 added543 := by decide

def connector548 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added548 : List (List Vertex) := [[4, 7, 2, 5, 1, 0], [4, 0]]
theorem accepted548 : SyntheticAccepted (decode 548) 0 1
    connector548 added548 := by decide

def connector550 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added550 : List (List Vertex) := [[4, 5, 2, 7, 0, 1], [4, 0, 5, 1]]
theorem accepted550 : SyntheticAccepted (decode 550) 2 1
    connector550 added550 := by decide

def connector551 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added551 : List (List Vertex) := [[4, 5, 2, 7, 0, 1, 6], [4, 0, 6]]
theorem accepted551 : SyntheticAccepted (decode 551) 2 0
    connector551 added551 := by decide

def connector552 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added552 : List (List Vertex) := [[4, 7, 1, 5, 2, 0], [4, 0]]
theorem accepted552 : SyntheticAccepted (decode 552) 0 2
    connector552 added552 := by decide

def connector553 : List Vertex := [6, 0, 3, 4, 7]
def added553 : List (List Vertex) := [[4, 5, 1, 0, 2, 7], [4, 0, 5, 2, 1, 7]]
theorem accepted553 : SyntheticAccepted (decode 553) 1 2
    connector553 added553 := by decide

def connector555 : List Vertex := [6, 0, 3, 4, 5]
def added555 : List (List Vertex) := [[4, 7, 1, 0, 2, 5], [4, 0, 7, 2, 1, 5]]
theorem accepted555 : SyntheticAccepted (decode 555) 1 0
    connector555 added555 := by decide

def connector556 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added556 : List (List Vertex) := [[4, 5, 2, 7, 1, 0], [4, 0]]
theorem accepted556 : SyntheticAccepted (decode 556) 2 1
    connector556 added556 := by decide

def connector557 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added557 : List (List Vertex) := [[4, 7, 2, 5, 0, 1, 6], [4, 0, 6]]
theorem accepted557 : SyntheticAccepted (decode 557) 0 2
    connector557 added557 := by decide

def connector558 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added558 : List (List Vertex) := [[4, 7, 2, 5, 0, 1], [4, 0, 7, 1]]
theorem accepted558 : SyntheticAccepted (decode 558) 0 1
    connector558 added558 := by decide

def connector565 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added565 : List (List Vertex) := [[4, 7, 2, 0, 5, 1, 6], [4, 0, 6]]
theorem accepted565 : SyntheticAccepted (decode 565) 0 1
    connector565 added565 := by decide

def connector566 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added566 : List (List Vertex) := [[4, 7, 0, 2, 6, 1, 5], [4, 0, 5]]
theorem accepted566 : SyntheticAccepted (decode 566) 0 2
    connector566 added566 := by decide

def connector567 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added567 : List (List Vertex) := [[4, 5, 1, 0, 7, 2, 6], [4, 0, 6]]
theorem accepted567 : SyntheticAccepted (decode 567) 2 1
    connector567 added567 := by decide

def connector568 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added568 : List (List Vertex) := [[4, 5, 1, 7, 2, 0], [4, 0]]
theorem accepted568 : SyntheticAccepted (decode 568) 2 1
    connector568 added568 := by decide

def connector569 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added569 : List (List Vertex) := [[4, 7, 1, 5, 0, 2, 6], [4, 0, 6]]
theorem accepted569 : SyntheticAccepted (decode 569) 0 2
    connector569 added569 := by decide

def connector570 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added570 : List (List Vertex) := [[4, 7, 1, 5, 0, 2], [4, 0, 7, 2]]
theorem accepted570 : SyntheticAccepted (decode 570) 0 1
    connector570 added570 := by decide

def connector572 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added572 : List (List Vertex) := [[4, 7, 2, 6, 1, 0], [4, 0]]
theorem accepted572 : SyntheticAccepted (decode 572) 2 0
    connector572 added572 := by decide

def connector573 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added573 : List (List Vertex) := [[4, 5, 0, 1, 7, 2, 6], [4, 0, 6]]
theorem accepted573 : SyntheticAccepted (decode 573) 1 2
    connector573 added573 := by decide

def connector575 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added575 : List (List Vertex) := [[4, 7, 1, 0, 6, 2], [4, 0, 7, 2]]
theorem accepted575 : SyntheticAccepted (decode 575) 1 0
    connector575 added575 := by decide

def connector580 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added580 : List (List Vertex) := [[1, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted580 : SyntheticAccepted (decode 580) 0 2
    connector580 added580 := by decide

def connector581 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added581 : List (List Vertex) := [[1, 5, 3, 6, 0, 4], [1, 0, 5, 4]]
theorem accepted581 : SyntheticAccepted (decode 581) 1 2
    connector581 added581 := by decide

def connector583 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added583 : List (List Vertex) := [[1, 5, 3, 6, 0, 4, 7], [1, 0, 7]]
theorem accepted583 : SyntheticAccepted (decode 583) 1 0
    connector583 added583 := by decide

def connector584 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added584 : List (List Vertex) := [[1, 7, 4, 5, 3, 0], [1, 0]]
theorem accepted584 : SyntheticAccepted (decode 584) 0 1
    connector584 added584 := by decide

def connector586 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added586 : List (List Vertex) := [[1, 5, 4, 7, 0, 3], [1, 0, 5, 3]]
theorem accepted586 : SyntheticAccepted (decode 586) 2 1
    connector586 added586 := by decide

def connector587 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added587 : List (List Vertex) := [[1, 5, 4, 7, 0, 3, 6], [1, 0, 6]]
theorem accepted587 : SyntheticAccepted (decode 587) 2 0
    connector587 added587 := by decide

def connector589 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added589 : List (List Vertex) := [[1, 7, 4, 0, 6, 3, 5], [1, 0, 5]]
theorem accepted589 : SyntheticAccepted (decode 589) 1 0
    connector589 added589 := by decide

def connector590 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added590 : List (List Vertex) := [[1, 6, 3, 0, 7, 4, 5], [1, 0, 5]]
theorem accepted590 : SyntheticAccepted (decode 590) 2 0
    connector590 added590 := by decide

def connector591 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added591 : List (List Vertex) := [[1, 7, 0, 4, 5, 3, 6], [1, 0, 6]]
theorem accepted591 : SyntheticAccepted (decode 591) 1 2
    connector591 added591 := by decide

def connector592 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added592 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted592 : SyntheticAccepted (decode 592) 0 2
    connector592 added592 := by decide

def connector593 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added593 : List (List Vertex) := [[2, 5, 3, 6, 0, 4], [2, 0, 5, 4]]
theorem accepted593 : SyntheticAccepted (decode 593) 1 2
    connector593 added593 := by decide

def connector595 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added595 : List (List Vertex) := [[2, 5, 3, 6, 0, 4, 7], [2, 0, 7]]
theorem accepted595 : SyntheticAccepted (decode 595) 1 0
    connector595 added595 := by decide

def connector596 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added596 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [1, 5, 3]]
theorem accepted596 : SyntheticAccepted (decode 596) 1 2
    connector596 added596 := by decide

def connector603 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added603 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 4], [1, 0, 3, 5, 4]]
theorem accepted603 : SyntheticAccepted (decode 603) 2 1
    connector603 added603 := by decide

def connector604 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added604 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 4, 0], [2, 0]]
theorem accepted604 : SyntheticAccepted (decode 604) 1 0
    connector604 added604 := by decide

def connector606 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added606 : List (List Vertex) := [[3, 6, 2, 5, 4, 0, 1, 7], [3, 5, 0, 7]]
theorem accepted606 : SyntheticAccepted (decode 606) 2 1
    connector606 added606 := by decide

def connector607 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added607 : List (List Vertex) := [[2, 5, 3, 6, 1, 0, 4, 7], [2, 6, 0, 7]]
theorem accepted607 : SyntheticAccepted (decode 607) 2 0
    connector607 added607 := by decide

def connector608 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added608 : List (List Vertex) := [[2, 7, 4, 5, 3, 0], [2, 0]]
theorem accepted608 : SyntheticAccepted (decode 608) 0 1
    connector608 added608 := by decide

def connector610 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added610 : List (List Vertex) := [[2, 5, 4, 7, 0, 3], [2, 0, 5, 3]]
theorem accepted610 : SyntheticAccepted (decode 610) 2 1
    connector610 added610 := by decide

def connector611 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added611 : List (List Vertex) := [[2, 5, 4, 7, 0, 3, 6], [2, 0, 6]]
theorem accepted611 : SyntheticAccepted (decode 611) 2 0
    connector611 added611 := by decide

def connector615 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added615 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 3], [1, 0, 4, 5, 3]]
theorem accepted615 : SyntheticAccepted (decode 615) 1 2
    connector615 added615 := by decide

def connector616 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added616 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 4], [1, 5, 4]]
theorem accepted616 : SyntheticAccepted (decode 616) 2 1
    connector616 added616 := by decide

def connector620 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added620 : List (List Vertex) := [[2, 5, 4, 7, 1, 6, 3, 0], [2, 0]]
theorem accepted620 : SyntheticAccepted (decode 620) 2 0
    connector620 added620 := by decide

def connector621 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added621 : List (List Vertex) := [[4, 7, 2, 5, 3, 0, 1, 6], [4, 5, 0, 6]]
theorem accepted621 : SyntheticAccepted (decode 621) 1 2
    connector621 added621 := by decide

def connector623 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added623 : List (List Vertex) := [[2, 5, 4, 7, 1, 0, 3, 6], [2, 7, 0, 6]]
theorem accepted623 : SyntheticAccepted (decode 623) 1 0
    connector623 added623 := by decide

def connector625 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added625 : List (List Vertex) := [[2, 7, 4, 0, 6, 3, 5], [2, 0, 5]]
theorem accepted625 : SyntheticAccepted (decode 625) 1 0
    connector625 added625 := by decide

def connector626 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added626 : List (List Vertex) := [[2, 6, 3, 0, 7, 4, 5], [2, 0, 5]]
theorem accepted626 : SyntheticAccepted (decode 626) 2 0
    connector626 added626 := by decide

def connector627 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added627 : List (List Vertex) := [[2, 7, 0, 4, 5, 3, 6], [2, 0, 6]]
theorem accepted627 : SyntheticAccepted (decode 627) 1 2
    connector627 added627 := by decide

def connector628 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added628 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 4, 0], [1, 0]]
theorem accepted628 : SyntheticAccepted (decode 628) 1 0
    connector628 added628 := by decide

def connector630 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added630 : List (List Vertex) := [[3, 6, 1, 5, 4, 0, 2, 7], [3, 5, 0, 7]]
theorem accepted630 : SyntheticAccepted (decode 630) 2 1
    connector630 added630 := by decide

def connector631 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added631 : List (List Vertex) := [[1, 5, 3, 6, 2, 0, 4, 7], [1, 6, 0, 7]]
theorem accepted631 : SyntheticAccepted (decode 631) 2 0
    connector631 added631 := by decide

def connector632 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added632 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 3, 0], [1, 0]]
theorem accepted632 : SyntheticAccepted (decode 632) 2 0
    connector632 added632 := by decide

def connector633 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added633 : List (List Vertex) := [[4, 7, 1, 5, 3, 0, 2, 6], [4, 5, 0, 6]]
theorem accepted633 : SyntheticAccepted (decode 633) 1 2
    connector633 added633 := by decide

def connector635 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added635 : List (List Vertex) := [[1, 5, 4, 7, 2, 0, 3, 6], [1, 7, 0, 6]]
theorem accepted635 : SyntheticAccepted (decode 635) 1 0
    connector635 added635 := by decide

def connector636 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added636 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted636 : SyntheticAccepted (decode 636) 1 2
    connector636 added636 := by decide

def connector637 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added637 : List (List Vertex) := [[3, 6, 1, 7, 4, 5, 0, 2], [3, 0, 6, 2]]
theorem accepted637 : SyntheticAccepted (decode 637) 0 2
    connector637 added637 := by decide

def connector638 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added638 : List (List Vertex) := [[4, 7, 1, 6, 3, 5, 0, 2], [4, 0, 7, 2]]
theorem accepted638 : SyntheticAccepted (decode 638) 0 1
    connector638 added638 := by decide

def connector644 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added644 : List (List Vertex) := [[1, 5, 4, 7, 3, 0], [1, 0]]
theorem accepted644 : SyntheticAccepted (decode 644) 0 1
    connector644 added644 := by decide

def connector646 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added646 : List (List Vertex) := [[1, 5, 3, 0, 7, 4], [1, 0, 5, 4]]
theorem accepted646 : SyntheticAccepted (decode 646) 2 1
    connector646 added646 := by decide

def connector647 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added647 : List (List Vertex) := [[1, 6, 0, 3, 5, 4, 7], [1, 0, 7]]
theorem accepted647 : SyntheticAccepted (decode 647) 2 0
    connector647 added647 := by decide

def connector648 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added648 : List (List Vertex) := [[1, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted648 : SyntheticAccepted (decode 648) 0 2
    connector648 added648 := by decide

def connector649 : List Vertex := [6, 0, 2, 1, 7]
def added649 : List (List Vertex) := [[1, 5, 3, 0, 4, 7], [1, 0, 5, 4, 3, 7]]
theorem accepted649 : SyntheticAccepted (decode 649) 1 2
    connector649 added649 := by decide

def connector651 : List Vertex := [6, 0, 2, 1, 5]
def added651 : List (List Vertex) := [[1, 7, 3, 0, 4, 5], [1, 0, 7, 4, 3, 5]]
theorem accepted651 : SyntheticAccepted (decode 651) 1 0
    connector651 added651 := by decide

def connector652 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added652 : List (List Vertex) := [[1, 7, 4, 5, 3, 0], [1, 0]]
theorem accepted652 : SyntheticAccepted (decode 652) 2 1
    connector652 added652 := by decide

def connector653 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added653 : List (List Vertex) := [[1, 6, 0, 3, 7, 4, 5], [1, 0, 5]]
theorem accepted653 : SyntheticAccepted (decode 653) 0 2
    connector653 added653 := by decide

def connector654 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added654 : List (List Vertex) := [[1, 7, 3, 0, 5, 4], [1, 0, 7, 4]]
theorem accepted654 : SyntheticAccepted (decode 654) 0 1
    connector654 added654 := by decide

def connector656 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added656 : List (List Vertex) := [[2, 5, 4, 7, 3, 0], [2, 0]]
theorem accepted656 : SyntheticAccepted (decode 656) 0 1
    connector656 added656 := by decide

def connector658 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added658 : List (List Vertex) := [[2, 5, 3, 0, 7, 4], [2, 0, 5, 4]]
theorem accepted658 : SyntheticAccepted (decode 658) 2 1
    connector658 added658 := by decide

def connector659 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added659 : List (List Vertex) := [[2, 6, 0, 3, 5, 4, 7], [2, 0, 7]]
theorem accepted659 : SyntheticAccepted (decode 659) 2 0
    connector659 added659 := by decide

def connector663 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added663 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 3], [1, 0, 4, 5, 3]]
theorem accepted663 : SyntheticAccepted (decode 663) 1 2
    connector663 added663 := by decide

def connector664 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added664 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 1], [3, 5, 1]]
theorem accepted664 : SyntheticAccepted (decode 664) 2 1
    connector664 added664 := by decide

def connector668 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added668 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 2, 0], [3, 0]]
theorem accepted668 : SyntheticAccepted (decode 668) 2 0
    connector668 added668 := by decide

def connector669 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added669 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 0, 4], [2, 0, 5, 4]]
theorem accepted669 : SyntheticAccepted (decode 669) 1 2
    connector669 added669 := by decide

def connector671 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added671 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 0, 4], [1, 0, 7, 4]]
theorem accepted671 : SyntheticAccepted (decode 671) 1 0
    connector671 added671 := by decide

def connector672 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added672 : List (List Vertex) := [[2, 7, 3, 5, 4, 0], [2, 0]]
theorem accepted672 : SyntheticAccepted (decode 672) 0 2
    connector672 added672 := by decide

def connector673 : List Vertex := [6, 0, 1, 2, 7]
def added673 : List (List Vertex) := [[2, 5, 3, 0, 4, 7], [2, 0, 5, 4, 3, 7]]
theorem accepted673 : SyntheticAccepted (decode 673) 1 2
    connector673 added673 := by decide

def connector675 : List Vertex := [6, 0, 1, 2, 5]
def added675 : List (List Vertex) := [[2, 7, 3, 0, 4, 5], [2, 0, 7, 4, 3, 5]]
theorem accepted675 : SyntheticAccepted (decode 675) 1 0
    connector675 added675 := by decide

def connector676 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added676 : List (List Vertex) := [[3, 0, 1, 5, 4, 7, 2], [3, 5, 2]]
theorem accepted676 : SyntheticAccepted (decode 676) 2 1
    connector676 added676 := by decide

def connector684 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added684 : List (List Vertex) := [[3, 0, 1, 7, 4, 5, 2], [3, 7, 2]]
theorem accepted684 : SyntheticAccepted (decode 684) 0 1
    connector684 added684 := by decide

def connector688 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added688 : List (List Vertex) := [[2, 7, 4, 5, 3, 0], [2, 0]]
theorem accepted688 : SyntheticAccepted (decode 688) 2 1
    connector688 added688 := by decide

def connector689 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added689 : List (List Vertex) := [[2, 6, 0, 3, 7, 4, 5], [2, 0, 5]]
theorem accepted689 : SyntheticAccepted (decode 689) 0 2
    connector689 added689 := by decide

def connector690 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added690 : List (List Vertex) := [[2, 7, 3, 0, 5, 4], [2, 0, 7, 4]]
theorem accepted690 : SyntheticAccepted (decode 690) 0 1
    connector690 added690 := by decide

def connector692 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added692 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 2, 0], [3, 0]]
theorem accepted692 : SyntheticAccepted (decode 692) 0 2
    connector692 added692 := by decide

def connector693 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added693 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 0, 4], [1, 0, 5, 4]]
theorem accepted693 : SyntheticAccepted (decode 693) 1 2
    connector693 added693 := by decide

def connector695 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added695 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 0, 4], [2, 0, 7, 4]]
theorem accepted695 : SyntheticAccepted (decode 695) 1 0
    connector695 added695 := by decide

def connector696 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added696 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [3, 7, 1]]
theorem accepted696 : SyntheticAccepted (decode 696) 0 1
    connector696 added696 := by decide

def connector701 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added701 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 3], [1, 0, 4, 7, 3]]
theorem accepted701 : SyntheticAccepted (decode 701) 1 0
    connector701 added701 := by decide

def connector709 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added709 : List (List Vertex) := [[1, 5, 0, 4, 7, 3, 6], [1, 0, 6]]
theorem accepted709 : SyntheticAccepted (decode 709) 1 0
    connector709 added709 := by decide

def connector710 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added710 : List (List Vertex) := [[1, 6, 3, 0, 5, 4, 7], [1, 0, 7]]
theorem accepted710 : SyntheticAccepted (decode 710) 0 2
    connector710 added710 := by decide

def connector711 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added711 : List (List Vertex) := [[1, 5, 4, 0, 6, 3, 7], [1, 0, 7]]
theorem accepted711 : SyntheticAccepted (decode 711) 1 2
    connector711 added711 := by decide

def connector712 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added712 : List (List Vertex) := [[1, 5, 4, 7, 3, 0], [1, 0]]
theorem accepted712 : SyntheticAccepted (decode 712) 2 1
    connector712 added712 := by decide

def connector713 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added713 : List (List Vertex) := [[1, 7, 4, 5, 0, 3, 6], [1, 0, 6]]
theorem accepted713 : SyntheticAccepted (decode 713) 0 2
    connector713 added713 := by decide

def connector714 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added714 : List (List Vertex) := [[1, 7, 4, 5, 0, 3], [1, 0, 7, 3]]
theorem accepted714 : SyntheticAccepted (decode 714) 0 1
    connector714 added714 := by decide

def connector716 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added716 : List (List Vertex) := [[1, 6, 3, 7, 4, 0], [1, 0]]
theorem accepted716 : SyntheticAccepted (decode 716) 2 0
    connector716 added716 := by decide

def connector717 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added717 : List (List Vertex) := [[1, 7, 3, 6, 0, 4, 5], [1, 0, 5]]
theorem accepted717 : SyntheticAccepted (decode 717) 1 2
    connector717 added717 := by decide

def connector719 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added719 : List (List Vertex) := [[1, 7, 3, 6, 0, 4], [1, 0, 7, 4]]
theorem accepted719 : SyntheticAccepted (decode 719) 1 0
    connector719 added719 := by decide

def connector721 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added721 : List (List Vertex) := [[2, 5, 0, 4, 7, 3, 6], [2, 0, 6]]
theorem accepted721 : SyntheticAccepted (decode 721) 1 0
    connector721 added721 := by decide

def connector722 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added722 : List (List Vertex) := [[2, 6, 3, 0, 5, 4, 7], [2, 0, 7]]
theorem accepted722 : SyntheticAccepted (decode 722) 0 2
    connector722 added722 := by decide

def connector723 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added723 : List (List Vertex) := [[2, 5, 4, 0, 6, 3, 7], [2, 0, 7]]
theorem accepted723 : SyntheticAccepted (decode 723) 1 2
    connector723 added723 := by decide

def connector724 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added724 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 4, 0], [1, 0]]
theorem accepted724 : SyntheticAccepted (decode 724) 1 0
    connector724 added724 := by decide

def connector726 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added726 : List (List Vertex) := [[4, 5, 1, 6, 3, 7, 0, 2], [4, 0, 5, 2]]
theorem accepted726 : SyntheticAccepted (decode 726) 2 1
    connector726 added726 := by decide

def connector727 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added727 : List (List Vertex) := [[3, 6, 1, 5, 4, 7, 0, 2], [3, 0, 6, 2]]
theorem accepted727 : SyntheticAccepted (decode 727) 2 0
    connector727 added727 := by decide

def connector728 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added728 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 3, 0], [1, 0]]
theorem accepted728 : SyntheticAccepted (decode 728) 0 2
    connector728 added728 := by decide

def connector729 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added729 : List (List Vertex) := [[1, 7, 4, 5, 2, 0, 3, 6], [1, 5, 0, 6]]
theorem accepted729 : SyntheticAccepted (decode 729) 1 2
    connector729 added729 := by decide

def connector731 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added731 : List (List Vertex) := [[4, 5, 1, 7, 3, 0, 2, 6], [4, 7, 0, 6]]
theorem accepted731 : SyntheticAccepted (decode 731) 1 0
    connector731 added731 := by decide

def connector732 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added732 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 4, 0], [1, 0]]
theorem accepted732 : SyntheticAccepted (decode 732) 1 2
    connector732 added732 := by decide

def connector733 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added733 : List (List Vertex) := [[1, 7, 3, 6, 2, 0, 4, 5], [1, 6, 0, 5]]
theorem accepted733 : SyntheticAccepted (decode 733) 0 2
    connector733 added733 := by decide

def connector734 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added734 : List (List Vertex) := [[3, 6, 1, 7, 4, 0, 2, 5], [3, 7, 0, 5]]
theorem accepted734 : SyntheticAccepted (decode 734) 0 1
    connector734 added734 := by decide

def connector736 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added736 : List (List Vertex) := [[2, 5, 4, 7, 3, 0], [2, 0]]
theorem accepted736 : SyntheticAccepted (decode 736) 2 1
    connector736 added736 := by decide

def connector737 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added737 : List (List Vertex) := [[2, 7, 4, 5, 0, 3, 6], [2, 0, 6]]
theorem accepted737 : SyntheticAccepted (decode 737) 0 2
    connector737 added737 := by decide

def connector738 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added738 : List (List Vertex) := [[2, 7, 4, 5, 0, 3], [2, 0, 7, 3]]
theorem accepted738 : SyntheticAccepted (decode 738) 0 1
    connector738 added738 := by decide

def connector740 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added740 : List (List Vertex) := [[2, 7, 4, 5, 1, 6, 3, 0], [2, 0]]
theorem accepted740 : SyntheticAccepted (decode 740) 0 2
    connector740 added740 := by decide

def connector741 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added741 : List (List Vertex) := [[2, 7, 4, 5, 1, 0, 3, 6], [2, 5, 0, 6]]
theorem accepted741 : SyntheticAccepted (decode 741) 1 2
    connector741 added741 := by decide

def connector743 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added743 : List (List Vertex) := [[4, 5, 2, 7, 3, 0, 1, 6], [4, 7, 0, 6]]
theorem accepted743 : SyntheticAccepted (decode 743) 1 0
    connector743 added743 := by decide

def connector744 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added744 : List (List Vertex) := [[1, 0, 3, 7, 2, 5, 4], [1, 7, 4]]
theorem accepted744 : SyntheticAccepted (decode 744) 0 1
    connector744 added744 := by decide

def connector749 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added749 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 3], [1, 0, 4, 7, 3]]
theorem accepted749 : SyntheticAccepted (decode 749) 1 0
    connector749 added749 := by decide

def connector752 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added752 : List (List Vertex) := [[2, 6, 3, 7, 4, 0], [2, 0]]
theorem accepted752 : SyntheticAccepted (decode 752) 2 0
    connector752 added752 := by decide

def connector753 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added753 : List (List Vertex) := [[2, 7, 3, 6, 0, 4, 5], [2, 0, 5]]
theorem accepted753 : SyntheticAccepted (decode 753) 1 2
    connector753 added753 := by decide

def connector755 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added755 : List (List Vertex) := [[2, 7, 3, 6, 0, 4], [2, 0, 7, 4]]
theorem accepted755 : SyntheticAccepted (decode 755) 1 0
    connector755 added755 := by decide

def connector756 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added756 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 4, 0], [2, 0]]
theorem accepted756 : SyntheticAccepted (decode 756) 1 2
    connector756 added756 := by decide

def connector757 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added757 : List (List Vertex) := [[2, 7, 3, 6, 1, 0, 4, 5], [2, 6, 0, 5]]
theorem accepted757 : SyntheticAccepted (decode 757) 0 2
    connector757 added757 := by decide

def connector758 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added758 : List (List Vertex) := [[3, 6, 2, 7, 4, 0, 1, 5], [3, 7, 0, 5]]
theorem accepted758 : SyntheticAccepted (decode 758) 0 1
    connector758 added758 := by decide

def connector761 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added761 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 4], [1, 0, 3, 7, 4]]
theorem accepted761 : SyntheticAccepted (decode 761) 0 1
    connector761 added761 := by decide

def connector764 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added764 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [1, 7, 3]]
theorem accepted764 : SyntheticAccepted (decode 764) 1 0
    connector764 added764 := by decide

def connector788 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added788 : List (List Vertex) := [[4, 6, 2, 5, 1, 0], [4, 0]]
theorem accepted788 : SyntheticAccepted (decode 788) 1 2
    connector788 added788 := by decide

def connector789 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added789 : List (List Vertex) := [[4, 6, 1, 0, 5, 2], [4, 0, 6, 2]]
theorem accepted789 : SyntheticAccepted (decode 789) 0 2
    connector789 added789 := by decide

def connector790 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added790 : List (List Vertex) := [[4, 7, 0, 1, 6, 2, 5], [4, 0, 5]]
theorem accepted790 : SyntheticAccepted (decode 790) 0 1
    connector790 added790 := by decide

def connector793 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added793 : List (List Vertex) := [[4, 7, 1, 0, 6, 2, 5], [4, 0, 5]]
theorem accepted793 : SyntheticAccepted (decode 793) 1 0
    connector793 added793 := by decide

def connector794 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added794 : List (List Vertex) := [[4, 6, 2, 0, 7, 1, 5], [4, 0, 5]]
theorem accepted794 : SyntheticAccepted (decode 794) 2 0
    connector794 added794 := by decide

def connector795 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added795 : List (List Vertex) := [[4, 6, 0, 2, 5, 1, 7], [4, 0, 7]]
theorem accepted795 : SyntheticAccepted (decode 795) 2 1
    connector795 added795 := by decide

def connector796 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added796 : List (List Vertex) := [[4, 7, 1, 6, 2, 0], [4, 0]]
theorem accepted796 : SyntheticAccepted (decode 796) 1 0
    connector796 added796 := by decide

def connector798 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added798 : List (List Vertex) := [[4, 6, 1, 7, 0, 2, 5], [4, 0, 5]]
theorem accepted798 : SyntheticAccepted (decode 798) 2 1
    connector798 added798 := by decide

def connector799 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added799 : List (List Vertex) := [[4, 6, 1, 7, 0, 2], [4, 0, 6, 2]]
theorem accepted799 : SyntheticAccepted (decode 799) 2 0
    connector799 added799 := by decide

def connector805 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added805 : List (List Vertex) := [[4, 7, 2, 0, 6, 1, 5], [4, 0, 5]]
theorem accepted805 : SyntheticAccepted (decode 805) 1 0
    connector805 added805 := by decide

def connector806 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added806 : List (List Vertex) := [[4, 6, 1, 0, 7, 2, 5], [4, 0, 5]]
theorem accepted806 : SyntheticAccepted (decode 806) 2 0
    connector806 added806 := by decide

def connector807 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added807 : List (List Vertex) := [[4, 7, 0, 2, 5, 1, 6], [4, 0, 6]]
theorem accepted807 : SyntheticAccepted (decode 807) 1 2
    connector807 added807 := by decide

def connector808 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added808 : List (List Vertex) := [[4, 7, 2, 5, 1, 0], [4, 0]]
theorem accepted808 : SyntheticAccepted (decode 808) 2 1
    connector808 added808 := by decide

def connector809 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added809 : List (List Vertex) := [[4, 6, 0, 1, 7, 2, 5], [4, 0, 5]]
theorem accepted809 : SyntheticAccepted (decode 809) 0 2
    connector809 added809 := by decide

def connector810 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added810 : List (List Vertex) := [[4, 7, 1, 0, 5, 2], [4, 0, 7, 2]]
theorem accepted810 : SyntheticAccepted (decode 810) 0 1
    connector810 added810 := by decide

def connector812 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added812 : List (List Vertex) := [[4, 6, 1, 7, 2, 0], [4, 0]]
theorem accepted812 : SyntheticAccepted (decode 812) 2 0
    connector812 added812 := by decide

def connector813 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added813 : List (List Vertex) := [[4, 7, 1, 6, 0, 2, 5], [4, 0, 5]]
theorem accepted813 : SyntheticAccepted (decode 813) 1 2
    connector813 added813 := by decide

def connector815 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added815 : List (List Vertex) := [[4, 7, 1, 6, 0, 2], [4, 0, 7, 2]]
theorem accepted815 : SyntheticAccepted (decode 815) 1 0
    connector815 added815 := by decide

def connector820 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added820 : List (List Vertex) := [[4, 7, 2, 6, 1, 0], [4, 0]]
theorem accepted820 : SyntheticAccepted (decode 820) 1 0
    connector820 added820 := by decide

def connector822 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added822 : List (List Vertex) := [[4, 6, 2, 7, 0, 1, 5], [4, 0, 5]]
theorem accepted822 : SyntheticAccepted (decode 822) 2 1
    connector822 added822 := by decide

def connector823 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added823 : List (List Vertex) := [[4, 6, 2, 7, 0, 1], [4, 0, 6, 1]]
theorem accepted823 : SyntheticAccepted (decode 823) 2 0
    connector823 added823 := by decide

def connector824 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added824 : List (List Vertex) := [[4, 6, 2, 7, 1, 0], [4, 0]]
theorem accepted824 : SyntheticAccepted (decode 824) 2 0
    connector824 added824 := by decide

def connector825 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added825 : List (List Vertex) := [[4, 7, 2, 6, 0, 1, 5], [4, 0, 5]]
theorem accepted825 : SyntheticAccepted (decode 825) 1 2
    connector825 added825 := by decide

def connector827 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added827 : List (List Vertex) := [[4, 7, 2, 6, 0, 1], [4, 0, 7, 1]]
theorem accepted827 : SyntheticAccepted (decode 827) 1 0
    connector827 added827 := by decide

def connector828 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added828 : List (List Vertex) := [[4, 7, 1, 6, 2, 0], [4, 0]]
theorem accepted828 : SyntheticAccepted (decode 828) 1 2
    connector828 added828 := by decide

def connector829 : List Vertex := [5, 0, 3, 4, 7]
def added829 : List (List Vertex) := [[4, 6, 1, 0, 2, 7], [4, 0, 6, 2, 1, 7]]
theorem accepted829 : SyntheticAccepted (decode 829) 0 2
    connector829 added829 := by decide

def connector830 : List Vertex := [5, 0, 3, 4, 6]
def added830 : List (List Vertex) := [[4, 7, 1, 0, 2, 6], [4, 0, 7, 2, 1, 6]]
theorem accepted830 : SyntheticAccepted (decode 830) 0 1
    connector830 added830 := by decide

def connector836 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added836 : List (List Vertex) := [[1, 5, 3, 6, 4, 0], [1, 0]]
theorem accepted836 : SyntheticAccepted (decode 836) 1 2
    connector836 added836 := by decide

def connector837 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added837 : List (List Vertex) := [[1, 6, 3, 5, 0, 4], [1, 0, 6, 4]]
theorem accepted837 : SyntheticAccepted (decode 837) 0 2
    connector837 added837 := by decide

def connector838 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added838 : List (List Vertex) := [[1, 6, 3, 5, 0, 4, 7], [1, 0, 7]]
theorem accepted838 : SyntheticAccepted (decode 838) 0 1
    connector838 added838 := by decide

def connector841 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added841 : List (List Vertex) := [[1, 7, 4, 0, 5, 3, 6], [1, 0, 6]]
theorem accepted841 : SyntheticAccepted (decode 841) 0 1
    connector841 added841 := by decide

def connector842 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added842 : List (List Vertex) := [[1, 7, 0, 4, 6, 3, 5], [1, 0, 5]]
theorem accepted842 : SyntheticAccepted (decode 842) 0 2
    connector842 added842 := by decide

def connector843 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added843 : List (List Vertex) := [[1, 5, 3, 0, 7, 4, 6], [1, 0, 6]]
theorem accepted843 : SyntheticAccepted (decode 843) 2 1
    connector843 added843 := by decide

def connector844 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added844 : List (List Vertex) := [[1, 7, 4, 6, 3, 0], [1, 0]]
theorem accepted844 : SyntheticAccepted (decode 844) 1 0
    connector844 added844 := by decide

def connector846 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added846 : List (List Vertex) := [[1, 6, 4, 7, 0, 3, 5], [1, 0, 5]]
theorem accepted846 : SyntheticAccepted (decode 846) 2 1
    connector846 added846 := by decide

def connector847 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added847 : List (List Vertex) := [[1, 6, 4, 7, 0, 3], [1, 0, 6, 3]]
theorem accepted847 : SyntheticAccepted (decode 847) 2 0
    connector847 added847 := by decide

def connector848 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added848 : List (List Vertex) := [[2, 5, 3, 6, 4, 0], [2, 0]]
theorem accepted848 : SyntheticAccepted (decode 848) 1 2
    connector848 added848 := by decide

def connector849 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added849 : List (List Vertex) := [[2, 6, 3, 5, 0, 4], [2, 0, 6, 4]]
theorem accepted849 : SyntheticAccepted (decode 849) 0 2
    connector849 added849 := by decide

def connector850 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added850 : List (List Vertex) := [[2, 6, 3, 5, 0, 4, 7], [2, 0, 7]]
theorem accepted850 : SyntheticAccepted (decode 850) 0 1
    connector850 added850 := by decide

def connector852 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added852 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [1, 6, 3]]
theorem accepted852 : SyntheticAccepted (decode 852) 0 2
    connector852 added852 := by decide

def connector856 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added856 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 4, 0], [2, 0]]
theorem accepted856 : SyntheticAccepted (decode 856) 0 1
    connector856 added856 := by decide

def connector858 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added858 : List (List Vertex) := [[2, 6, 3, 5, 1, 0, 4, 7], [2, 5, 0, 7]]
theorem accepted858 : SyntheticAccepted (decode 858) 2 1
    connector858 added858 := by decide

def connector859 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added859 : List (List Vertex) := [[3, 5, 2, 6, 4, 0, 1, 7], [3, 6, 0, 7]]
theorem accepted859 : SyntheticAccepted (decode 859) 2 0
    connector859 added859 := by decide

def connector862 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added862 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 4], [1, 0, 3, 6, 4]]
theorem accepted862 : SyntheticAccepted (decode 862) 2 0
    connector862 added862 := by decide

def connector865 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added865 : List (List Vertex) := [[2, 7, 4, 0, 5, 3, 6], [2, 0, 6]]
theorem accepted865 : SyntheticAccepted (decode 865) 0 1
    connector865 added865 := by decide

def connector866 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added866 : List (List Vertex) := [[2, 7, 0, 4, 6, 3, 5], [2, 0, 5]]
theorem accepted866 : SyntheticAccepted (decode 866) 0 2
    connector866 added866 := by decide

def connector867 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added867 : List (List Vertex) := [[2, 5, 3, 0, 7, 4, 6], [2, 0, 6]]
theorem accepted867 : SyntheticAccepted (decode 867) 2 1
    connector867 added867 := by decide

def connector868 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added868 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 4, 0], [1, 0]]
theorem accepted868 : SyntheticAccepted (decode 868) 0 1
    connector868 added868 := by decide

def connector870 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added870 : List (List Vertex) := [[1, 6, 3, 5, 2, 0, 4, 7], [1, 5, 0, 7]]
theorem accepted870 : SyntheticAccepted (decode 870) 2 1
    connector870 added870 := by decide

def connector871 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added871 : List (List Vertex) := [[3, 5, 1, 6, 4, 0, 2, 7], [3, 6, 0, 7]]
theorem accepted871 : SyntheticAccepted (decode 871) 2 0
    connector871 added871 := by decide

def connector872 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added872 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 4, 0], [1, 0]]
theorem accepted872 : SyntheticAccepted (decode 872) 0 2
    connector872 added872 := by decide

def connector873 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added873 : List (List Vertex) := [[3, 5, 1, 7, 4, 6, 0, 2], [3, 0, 5, 2]]
theorem accepted873 : SyntheticAccepted (decode 873) 1 2
    connector873 added873 := by decide

def connector875 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added875 : List (List Vertex) := [[4, 7, 1, 5, 3, 6, 0, 2], [4, 0, 7, 2]]
theorem accepted875 : SyntheticAccepted (decode 875) 1 0
    connector875 added875 := by decide

def connector876 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added876 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 3, 0], [1, 0]]
theorem accepted876 : SyntheticAccepted (decode 876) 2 1
    connector876 added876 := by decide

def connector877 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added877 : List (List Vertex) := [[4, 7, 1, 6, 3, 0, 2, 5], [4, 6, 0, 5]]
theorem accepted877 : SyntheticAccepted (decode 877) 0 2
    connector877 added877 := by decide

def connector878 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added878 : List (List Vertex) := [[1, 6, 4, 7, 2, 0, 3, 5], [1, 7, 0, 5]]
theorem accepted878 : SyntheticAccepted (decode 878) 0 1
    connector878 added878 := by decide

def connector880 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added880 : List (List Vertex) := [[2, 7, 4, 6, 3, 0], [2, 0]]
theorem accepted880 : SyntheticAccepted (decode 880) 1 0
    connector880 added880 := by decide

def connector882 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added882 : List (List Vertex) := [[2, 6, 4, 7, 0, 3, 5], [2, 0, 5]]
theorem accepted882 : SyntheticAccepted (decode 882) 2 1
    connector882 added882 := by decide

def connector883 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added883 : List (List Vertex) := [[2, 6, 4, 7, 0, 3], [2, 0, 6, 3]]
theorem accepted883 : SyntheticAccepted (decode 883) 2 0
    connector883 added883 := by decide

def connector886 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added886 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 3], [1, 0, 4, 6, 3]]
theorem accepted886 : SyntheticAccepted (decode 886) 0 2
    connector886 added886 := by decide

def connector888 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added888 : List (List Vertex) := [[2, 6, 4, 7, 1, 5, 3, 0], [2, 0]]
theorem accepted888 : SyntheticAccepted (decode 888) 2 1
    connector888 added888 := by decide

def connector889 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added889 : List (List Vertex) := [[4, 7, 2, 6, 3, 0, 1, 5], [4, 6, 0, 5]]
theorem accepted889 : SyntheticAccepted (decode 889) 0 2
    connector889 added889 := by decide

def connector890 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added890 : List (List Vertex) := [[2, 6, 4, 7, 1, 0, 3, 5], [2, 7, 0, 5]]
theorem accepted890 : SyntheticAccepted (decode 890) 0 1
    connector890 added890 := by decide

def connector892 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added892 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 4], [1, 6, 4]]
theorem accepted892 : SyntheticAccepted (decode 892) 2 0
    connector892 added892 := by decide

def connector901 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added901 : List (List Vertex) := [[1, 6, 0, 4, 7, 3, 5], [1, 0, 5]]
theorem accepted901 : SyntheticAccepted (decode 901) 0 1
    connector901 added901 := by decide

def connector902 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added902 : List (List Vertex) := [[1, 6, 4, 0, 5, 3, 7], [1, 0, 7]]
theorem accepted902 : SyntheticAccepted (decode 902) 0 2
    connector902 added902 := by decide

def connector903 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added903 : List (List Vertex) := [[1, 5, 3, 0, 6, 4, 7], [1, 0, 7]]
theorem accepted903 : SyntheticAccepted (decode 903) 1 2
    connector903 added903 := by decide

def connector904 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added904 : List (List Vertex) := [[1, 5, 3, 7, 4, 0], [1, 0]]
theorem accepted904 : SyntheticAccepted (decode 904) 2 1
    connector904 added904 := by decide

def connector905 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added905 : List (List Vertex) := [[1, 7, 3, 5, 0, 4, 6], [1, 0, 6]]
theorem accepted905 : SyntheticAccepted (decode 905) 0 2
    connector905 added905 := by decide

def connector906 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added906 : List (List Vertex) := [[1, 7, 3, 5, 0, 4], [1, 0, 7, 4]]
theorem accepted906 : SyntheticAccepted (decode 906) 0 1
    connector906 added906 := by decide

def connector908 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added908 : List (List Vertex) := [[1, 6, 4, 7, 3, 0], [1, 0]]
theorem accepted908 : SyntheticAccepted (decode 908) 2 0
    connector908 added908 := by decide

def connector909 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added909 : List (List Vertex) := [[1, 7, 4, 6, 0, 3, 5], [1, 0, 5]]
theorem accepted909 : SyntheticAccepted (decode 909) 1 2
    connector909 added909 := by decide

def connector911 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added911 : List (List Vertex) := [[1, 7, 4, 6, 0, 3], [1, 0, 7, 3]]
theorem accepted911 : SyntheticAccepted (decode 911) 1 0
    connector911 added911 := by decide

def connector913 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added913 : List (List Vertex) := [[2, 6, 0, 4, 7, 3, 5], [2, 0, 5]]
theorem accepted913 : SyntheticAccepted (decode 913) 0 1
    connector913 added913 := by decide

def connector914 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added914 : List (List Vertex) := [[2, 6, 4, 0, 5, 3, 7], [2, 0, 7]]
theorem accepted914 : SyntheticAccepted (decode 914) 0 2
    connector914 added914 := by decide

def connector915 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added915 : List (List Vertex) := [[2, 5, 3, 0, 6, 4, 7], [2, 0, 7]]
theorem accepted915 : SyntheticAccepted (decode 915) 1 2
    connector915 added915 := by decide

def connector916 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added916 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 4, 0], [1, 0]]
theorem accepted916 : SyntheticAccepted (decode 916) 0 1
    connector916 added916 := by decide

def connector918 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added918 : List (List Vertex) := [[3, 5, 1, 6, 4, 7, 0, 2], [3, 0, 5, 2]]
theorem accepted918 : SyntheticAccepted (decode 918) 2 1
    connector918 added918 := by decide

def connector919 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added919 : List (List Vertex) := [[4, 6, 1, 5, 3, 7, 0, 2], [4, 0, 6, 2]]
theorem accepted919 : SyntheticAccepted (decode 919) 2 0
    connector919 added919 := by decide

def connector920 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added920 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 4, 0], [1, 0]]
theorem accepted920 : SyntheticAccepted (decode 920) 0 2
    connector920 added920 := by decide

def connector921 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added921 : List (List Vertex) := [[1, 7, 3, 5, 2, 0, 4, 6], [1, 5, 0, 6]]
theorem accepted921 : SyntheticAccepted (decode 921) 1 2
    connector921 added921 := by decide

def connector923 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added923 : List (List Vertex) := [[3, 5, 1, 7, 4, 0, 2, 6], [3, 7, 0, 6]]
theorem accepted923 : SyntheticAccepted (decode 923) 1 0
    connector923 added923 := by decide

def connector924 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added924 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 3, 0], [1, 0]]
theorem accepted924 : SyntheticAccepted (decode 924) 1 2
    connector924 added924 := by decide

def connector925 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added925 : List (List Vertex) := [[1, 7, 4, 6, 2, 0, 3, 5], [1, 6, 0, 5]]
theorem accepted925 : SyntheticAccepted (decode 925) 0 2
    connector925 added925 := by decide

def connector926 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added926 : List (List Vertex) := [[4, 6, 1, 7, 3, 0, 2, 5], [4, 7, 0, 5]]
theorem accepted926 : SyntheticAccepted (decode 926) 0 1
    connector926 added926 := by decide

def connector928 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added928 : List (List Vertex) := [[2, 5, 3, 7, 4, 0], [2, 0]]
theorem accepted928 : SyntheticAccepted (decode 928) 2 1
    connector928 added928 := by decide

def connector929 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added929 : List (List Vertex) := [[2, 7, 3, 5, 0, 4, 6], [2, 0, 6]]
theorem accepted929 : SyntheticAccepted (decode 929) 0 2
    connector929 added929 := by decide

def connector930 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added930 : List (List Vertex) := [[2, 7, 3, 5, 0, 4], [2, 0, 7, 4]]
theorem accepted930 : SyntheticAccepted (decode 930) 0 1
    connector930 added930 := by decide

def connector932 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added932 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 4, 0], [2, 0]]
theorem accepted932 : SyntheticAccepted (decode 932) 0 2
    connector932 added932 := by decide

def connector933 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added933 : List (List Vertex) := [[2, 7, 3, 5, 1, 0, 4, 6], [2, 5, 0, 6]]
theorem accepted933 : SyntheticAccepted (decode 933) 1 2
    connector933 added933 := by decide

def connector935 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added935 : List (List Vertex) := [[3, 5, 2, 7, 4, 0, 1, 6], [3, 7, 0, 6]]
theorem accepted935 : SyntheticAccepted (decode 935) 1 0
    connector935 added935 := by decide

def connector936 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added936 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [1, 7, 3]]
theorem accepted936 : SyntheticAccepted (decode 936) 0 1
    connector936 added936 := by decide

def connector941 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added941 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 4], [1, 0, 3, 7, 4]]
theorem accepted941 : SyntheticAccepted (decode 941) 1 0
    connector941 added941 := by decide

def connector944 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added944 : List (List Vertex) := [[2, 6, 4, 7, 3, 0], [2, 0]]
theorem accepted944 : SyntheticAccepted (decode 944) 2 0
    connector944 added944 := by decide

def connector945 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added945 : List (List Vertex) := [[2, 7, 4, 6, 0, 3, 5], [2, 0, 5]]
theorem accepted945 : SyntheticAccepted (decode 945) 1 2
    connector945 added945 := by decide

def connector947 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added947 : List (List Vertex) := [[2, 7, 4, 6, 0, 3], [2, 0, 7, 3]]
theorem accepted947 : SyntheticAccepted (decode 947) 1 0
    connector947 added947 := by decide

def connector948 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added948 : List (List Vertex) := [[2, 7, 4, 6, 1, 5, 3, 0], [2, 0]]
theorem accepted948 : SyntheticAccepted (decode 948) 1 2
    connector948 added948 := by decide

def connector949 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added949 : List (List Vertex) := [[2, 7, 4, 6, 1, 0, 3, 5], [2, 6, 0, 5]]
theorem accepted949 : SyntheticAccepted (decode 949) 0 2
    connector949 added949 := by decide

def connector950 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added950 : List (List Vertex) := [[4, 6, 2, 7, 3, 0, 1, 5], [4, 7, 0, 5]]
theorem accepted950 : SyntheticAccepted (decode 950) 0 1
    connector950 added950 := by decide

def connector953 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added953 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 3], [1, 0, 4, 7, 3]]
theorem accepted953 : SyntheticAccepted (decode 953) 0 1
    connector953 added953 := by decide

def connector956 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added956 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 4], [1, 7, 4]]
theorem accepted956 : SyntheticAccepted (decode 956) 1 0
    connector956 added956 := by decide

def connector964 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added964 : List (List Vertex) := [[1, 6, 4, 7, 3, 0], [1, 0]]
theorem accepted964 : SyntheticAccepted (decode 964) 1 0
    connector964 added964 := by decide

def connector966 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added966 : List (List Vertex) := [[1, 5, 0, 3, 6, 4, 7], [1, 0, 7]]
theorem accepted966 : SyntheticAccepted (decode 966) 2 1
    connector966 added966 := by decide

def connector967 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added967 : List (List Vertex) := [[1, 6, 3, 0, 7, 4], [1, 0, 6, 4]]
theorem accepted967 : SyntheticAccepted (decode 967) 2 0
    connector967 added967 := by decide

def connector968 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added968 : List (List Vertex) := [[1, 7, 4, 6, 3, 0], [1, 0]]
theorem accepted968 : SyntheticAccepted (decode 968) 2 0
    connector968 added968 := by decide

def connector969 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added969 : List (List Vertex) := [[1, 5, 0, 3, 7, 4, 6], [1, 0, 6]]
theorem accepted969 : SyntheticAccepted (decode 969) 1 2
    connector969 added969 := by decide

def connector971 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added971 : List (List Vertex) := [[1, 7, 3, 0, 6, 4], [1, 0, 7, 4]]
theorem accepted971 : SyntheticAccepted (decode 971) 1 0
    connector971 added971 := by decide

def connector972 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added972 : List (List Vertex) := [[1, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted972 : SyntheticAccepted (decode 972) 1 2
    connector972 added972 := by decide

def connector973 : List Vertex := [5, 0, 2, 1, 7]
def added973 : List (List Vertex) := [[1, 6, 3, 0, 4, 7], [1, 0, 6, 4, 3, 7]]
theorem accepted973 : SyntheticAccepted (decode 973) 0 2
    connector973 added973 := by decide

def connector974 : List Vertex := [5, 0, 2, 1, 6]
def added974 : List (List Vertex) := [[1, 7, 3, 0, 4, 6], [1, 0, 7, 4, 3, 6]]
theorem accepted974 : SyntheticAccepted (decode 974) 0 1
    connector974 added974 := by decide

def connector976 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added976 : List (List Vertex) := [[2, 6, 4, 7, 3, 0], [2, 0]]
theorem accepted976 : SyntheticAccepted (decode 976) 1 0
    connector976 added976 := by decide

def connector978 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added978 : List (List Vertex) := [[2, 5, 0, 3, 6, 4, 7], [2, 0, 7]]
theorem accepted978 : SyntheticAccepted (decode 978) 2 1
    connector978 added978 := by decide

def connector979 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added979 : List (List Vertex) := [[2, 6, 3, 0, 7, 4], [2, 0, 6, 4]]
theorem accepted979 : SyntheticAccepted (decode 979) 2 0
    connector979 added979 := by decide

def connector982 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added982 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 3], [1, 0, 4, 6, 3]]
theorem accepted982 : SyntheticAccepted (decode 982) 0 2
    connector982 added982 := by decide

def connector984 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added984 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 2, 0], [3, 0]]
theorem accepted984 : SyntheticAccepted (decode 984) 2 1
    connector984 added984 := by decide

def connector985 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added985 : List (List Vertex) := [[2, 6, 3, 7, 1, 5, 0, 4], [2, 0, 6, 4]]
theorem accepted985 : SyntheticAccepted (decode 985) 0 2
    connector985 added985 := by decide

def connector986 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added986 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 0, 4], [1, 0, 7, 4]]
theorem accepted986 : SyntheticAccepted (decode 986) 0 1
    connector986 added986 := by decide

def connector988 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added988 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [3, 6, 1]]
theorem accepted988 : SyntheticAccepted (decode 988) 2 0
    connector988 added988 := by decide

def connector992 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added992 : List (List Vertex) := [[2, 7, 4, 6, 3, 0], [2, 0]]
theorem accepted992 : SyntheticAccepted (decode 992) 2 0
    connector992 added992 := by decide

def connector993 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added993 : List (List Vertex) := [[2, 5, 0, 3, 7, 4, 6], [2, 0, 6]]
theorem accepted993 : SyntheticAccepted (decode 993) 1 2
    connector993 added993 := by decide

def connector995 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added995 : List (List Vertex) := [[2, 7, 3, 0, 6, 4], [2, 0, 7, 4]]
theorem accepted995 : SyntheticAccepted (decode 995) 1 0
    connector995 added995 := by decide

def connector996 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added996 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted996 : SyntheticAccepted (decode 996) 1 2
    connector996 added996 := by decide

def connector997 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added997 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 0, 4], [1, 0, 6, 4]]
theorem accepted997 : SyntheticAccepted (decode 997) 0 2
    connector997 added997 := by decide

def connector998 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added998 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 0, 4], [2, 0, 7, 4]]
theorem accepted998 : SyntheticAccepted (decode 998) 0 1
    connector998 added998 := by decide

def connector1001 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added1001 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 3], [1, 0, 4, 7, 3]]
theorem accepted1001 : SyntheticAccepted (decode 1001) 0 1
    connector1001 added1001 := by decide

def connector1004 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added1004 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [3, 7, 1]]
theorem accepted1004 : SyntheticAccepted (decode 1004) 1 0
    connector1004 added1004 := by decide

def connector1008 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added1008 : List (List Vertex) := [[2, 7, 3, 6, 4, 0], [2, 0]]
theorem accepted1008 : SyntheticAccepted (decode 1008) 1 2
    connector1008 added1008 := by decide

def connector1009 : List Vertex := [5, 0, 1, 2, 7]
def added1009 : List (List Vertex) := [[2, 6, 3, 0, 4, 7], [2, 0, 6, 4, 3, 7]]
theorem accepted1009 : SyntheticAccepted (decode 1009) 0 2
    connector1009 added1009 := by decide

def connector1010 : List Vertex := [5, 0, 1, 2, 6]
def added1010 : List (List Vertex) := [[2, 7, 3, 0, 4, 6], [2, 0, 7, 4, 3, 6]]
theorem accepted1010 : SyntheticAccepted (decode 1010) 0 1
    connector1010 added1010 := by decide

def connector1012 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added1012 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 2], [3, 6, 2]]
theorem accepted1012 : SyntheticAccepted (decode 1012) 2 0
    connector1012 added1012 := by decide

def connector1016 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added1016 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 2], [3, 7, 2]]
theorem accepted1016 : SyntheticAccepted (decode 1016) 1 0
    connector1016 added1016 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
