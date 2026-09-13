/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def tail84 : List Vertex := [5, 2, 1, 0, 3, 4]
def added84 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 5]]
theorem accepted84 : OriginalAccepted (decode 84) 0 1 0
    tail84 added84 := by decide

def tail86 : List Vertex := [5, 2, 1, 0, 3, 4]
def added86 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 7, 0, 5]]
theorem accepted86 : OriginalAccepted (decode 86) 2 1 0
    tail86 added86 := by decide

def tail87 : List Vertex := [6, 2, 1, 0, 3, 4]
def added87 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 1], [1, 5, 7, 0, 6]]
theorem accepted87 : OriginalAccepted (decode 87) 2 0 1
    tail87 added87 := by decide

def tail88 : List Vertex := [5, 1, 2, 0, 3, 4]
def added88 : List (List Vertex) := [[4, 0, 1, 7, 5, 3, 6, 2], [2, 5]]
theorem accepted88 : OriginalAccepted (decode 88) 0 2 0
    tail88 added88 := by decide

def tail89 : List Vertex := [5, 1, 2, 0, 3, 4]
def added89 : List (List Vertex) := [[4, 0, 1, 7, 6, 3, 5, 2], [2, 6, 0, 5]]
theorem accepted89 : OriginalAccepted (decode 89) 1 2 0
    tail89 added89 := by decide

def tail91 : List Vertex := [7, 1, 2, 0, 3, 4]
def added91 : List (List Vertex) := [[4, 0, 1, 5, 3, 6, 2], [2, 5, 6, 0, 7]]
theorem accepted91 : OriginalAccepted (decode 91) 1 0 2
    tail91 added91 := by decide

def tail92 : List Vertex := [6, 1, 2, 0, 3, 4]
def added92 : List (List Vertex) := [[4, 0, 1, 7, 6, 3, 5, 2], [2, 6]]
theorem accepted92 : OriginalAccepted (decode 92) 1 2 1
    tail92 added92 := by decide

def tail93 : List Vertex := [6, 1, 2, 0, 3, 4]
def added93 : List (List Vertex) := [[4, 0, 1, 7, 5, 3, 6, 2], [2, 5, 0, 6]]
theorem accepted93 : OriginalAccepted (decode 93) 0 2 1
    tail93 added93 := by decide

def tail94 : List Vertex := [7, 1, 2, 0, 3, 4]
def added94 : List (List Vertex) := [[4, 0, 1, 6, 3, 5, 2], [2, 6, 5, 0, 7]]
theorem accepted94 : OriginalAccepted (decode 94) 0 1 2
    tail94 added94 := by decide

def tail100 : List Vertex := [5, 2, 1, 0, 3, 4]
def added100 : List (List Vertex) := [[4, 0, 2, 7, 5, 3, 6, 1], [1, 5]]
theorem accepted100 : OriginalAccepted (decode 100) 0 2 0
    tail100 added100 := by decide

def tail101 : List Vertex := [5, 2, 1, 0, 3, 4]
def added101 : List (List Vertex) := [[4, 0, 2, 7, 6, 3, 5, 1], [1, 6, 0, 5]]
theorem accepted101 : OriginalAccepted (decode 101) 1 2 0
    tail101 added101 := by decide

def tail103 : List Vertex := [7, 2, 1, 0, 3, 4]
def added103 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 1], [1, 5, 6, 0, 7]]
theorem accepted103 : OriginalAccepted (decode 103) 1 0 2
    tail103 added103 := by decide

def tail104 : List Vertex := [5, 2, 1, 0, 3, 4]
def added104 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 3, 6], [5, 6]]
theorem accepted104 : OriginalAccepted (decode 104) 0 1 0
    tail104 added104 := by decide

def tail106 : List Vertex := [5, 2, 1, 0, 3, 4]
def added106 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 3, 6], [5, 0, 7, 6]]
theorem accepted106 : OriginalAccepted (decode 106) 2 1 0
    tail106 added106 := by decide

def tail107 : List Vertex := [7, 2, 1, 0, 3, 4]
def added107 : List (List Vertex) := [[4, 0, 6, 3, 5, 7, 1], [1, 5, 2, 0, 7]]
theorem accepted107 : OriginalAccepted (decode 107) 2 0 2
    tail107 added107 := by decide

def tail109 : List Vertex := [5, 2, 1, 0, 3, 4]
def added109 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted109 : OriginalAccepted (decode 109) 1 0 0
    tail109 added109 := by decide

def tail110 : List Vertex := [7, 1, 2, 0, 3, 4]
def added110 : List (List Vertex) := [[4, 0, 1, 6, 3, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted110 : OriginalAccepted (decode 110) 0 2 2
    tail110 added110 := by decide

def tail111 : List Vertex := [7, 2, 1, 0, 3, 4]
def added111 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted111 : OriginalAccepted (decode 111) 1 2 2
    tail111 added111 := by decide

def tail116 : List Vertex := [6, 2, 1, 0, 3, 4]
def added116 : List (List Vertex) := [[4, 0, 2, 7, 6, 3, 5, 1], [1, 6]]
theorem accepted116 : OriginalAccepted (decode 116) 1 2 1
    tail116 added116 := by decide

def tail117 : List Vertex := [6, 2, 1, 0, 3, 4]
def added117 : List (List Vertex) := [[4, 0, 2, 7, 5, 3, 6, 1], [1, 5, 0, 6]]
theorem accepted117 : OriginalAccepted (decode 117) 0 2 1
    tail117 added117 := by decide

def tail118 : List Vertex := [7, 2, 1, 0, 3, 4]
def added118 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 5, 0, 7]]
theorem accepted118 : OriginalAccepted (decode 118) 0 1 2
    tail118 added118 := by decide

def tail121 : List Vertex := [6, 2, 1, 0, 3, 4]
def added121 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted121 : OriginalAccepted (decode 121) 0 1 1
    tail121 added121 := by decide

def tail122 : List Vertex := [7, 2, 1, 0, 3, 4]
def added122 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted122 : OriginalAccepted (decode 122) 0 2 2
    tail122 added122 := by decide

def tail123 : List Vertex := [7, 1, 2, 0, 3, 4]
def added123 : List (List Vertex) := [[4, 0, 1, 5, 3, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted123 : OriginalAccepted (decode 123) 1 2 2
    tail123 added123 := by decide

def tail124 : List Vertex := [6, 2, 1, 0, 3, 4]
def added124 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 3, 5], [6, 5]]
theorem accepted124 : OriginalAccepted (decode 124) 1 0 1
    tail124 added124 := by decide

def tail126 : List Vertex := [7, 2, 1, 0, 3, 4]
def added126 : List (List Vertex) := [[4, 0, 5, 3, 6, 7, 1], [1, 6, 2, 0, 7]]
theorem accepted126 : OriginalAccepted (decode 126) 2 1 2
    tail126 added126 := by decide

def tail127 : List Vertex := [6, 2, 1, 0, 3, 4]
def added127 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 3, 5], [6, 0, 7, 5]]
theorem accepted127 : OriginalAccepted (decode 127) 2 0 1
    tail127 added127 := by decide

def tail148 : List Vertex := [5, 2, 1, 0, 3, 4]
def added148 : List (List Vertex) := [[4, 0, 2, 6, 1, 5, 3, 7], [5, 7]]
theorem accepted148 : OriginalAccepted (decode 148) 0 2 0
    tail148 added148 := by decide

def tail149 : List Vertex := [5, 2, 1, 0, 3, 4]
def added149 : List (List Vertex) := [[4, 0, 2, 6, 1, 5, 3, 7], [5, 0, 6, 7]]
theorem accepted149 : OriginalAccepted (decode 149) 1 2 0
    tail149 added149 := by decide

def tail151 : List Vertex := [6, 2, 1, 0, 3, 4]
def added151 : List (List Vertex) := [[4, 0, 7, 3, 5, 6, 1], [1, 5, 2, 0, 6]]
theorem accepted151 : OriginalAccepted (decode 151) 1 0 1
    tail151 added151 := by decide

def tail152 : List Vertex := [5, 2, 1, 0, 3, 4]
def added152 : List (List Vertex) := [[4, 0, 2, 6, 5, 3, 7, 1], [1, 5]]
theorem accepted152 : OriginalAccepted (decode 152) 0 1 0
    tail152 added152 := by decide

def tail154 : List Vertex := [5, 2, 1, 0, 3, 4]
def added154 : List (List Vertex) := [[4, 0, 2, 6, 7, 3, 5, 1], [1, 7, 0, 5]]
theorem accepted154 : OriginalAccepted (decode 154) 2 1 0
    tail154 added154 := by decide

def tail155 : List Vertex := [6, 2, 1, 0, 3, 4]
def added155 : List (List Vertex) := [[4, 0, 2, 5, 3, 7, 1], [1, 5, 7, 0, 6]]
theorem accepted155 : OriginalAccepted (decode 155) 2 0 1
    tail155 added155 := by decide

def tail157 : List Vertex := [6, 1, 2, 0, 3, 4]
def added157 : List (List Vertex) := [[4, 0, 1, 7, 3, 5, 6, 2], [2, 5, 0, 6]]
theorem accepted157 : OriginalAccepted (decode 157) 0 1 1
    tail157 added157 := by decide

def tail158 : List Vertex := [5, 2, 1, 0, 3, 4]
def added158 : List (List Vertex) := [[4, 0, 2, 6, 1, 7, 5, 3], [3, 7, 0, 5]]
theorem accepted158 : OriginalAccepted (decode 158) 2 0 0
    tail158 added158 := by decide

def tail159 : List Vertex := [6, 2, 1, 0, 3, 4]
def added159 : List (List Vertex) := [[4, 0, 2, 5, 3, 7, 6, 1], [1, 7, 0, 6]]
theorem accepted159 : OriginalAccepted (decode 159) 2 1 1
    tail159 added159 := by decide

def tail164 : List Vertex := [5, 1, 2, 0, 3, 4]
def added164 : List (List Vertex) := [[4, 0, 1, 6, 5, 3, 7, 2], [2, 5]]
theorem accepted164 : OriginalAccepted (decode 164) 0 1 0
    tail164 added164 := by decide

def tail166 : List Vertex := [5, 1, 2, 0, 3, 4]
def added166 : List (List Vertex) := [[4, 0, 1, 6, 7, 3, 5, 2], [2, 7, 0, 5]]
theorem accepted166 : OriginalAccepted (decode 166) 2 1 0
    tail166 added166 := by decide

def tail167 : List Vertex := [6, 1, 2, 0, 3, 4]
def added167 : List (List Vertex) := [[4, 0, 1, 5, 3, 7, 2], [2, 5, 7, 0, 6]]
theorem accepted167 : OriginalAccepted (decode 167) 2 0 1
    tail167 added167 := by decide

def tail168 : List Vertex := [5, 2, 1, 0, 3, 4]
def added168 : List (List Vertex) := [[4, 0, 2, 7, 3, 5, 1], [1, 7, 5]]
theorem accepted168 : OriginalAccepted (decode 168) 0 2 0
    tail168 added168 := by decide

def tail169 : List Vertex := [5, 2, 1, 0, 3, 4]
def added169 : List (List Vertex) := [[4, 0, 2, 7, 3, 5, 1], [1, 7, 6, 0, 5]]
theorem accepted169 : OriginalAccepted (decode 169) 1 2 0
    tail169 added169 := by decide

def tail171 : List Vertex := [7, 2, 1, 0, 3, 4]
def added171 : List (List Vertex) := [[4, 0, 2, 5, 3, 7, 1], [1, 5, 6, 0, 7]]
theorem accepted171 : OriginalAccepted (decode 171) 1 0 2
    tail171 added171 := by decide

def tail172 : List Vertex := [7, 1, 2, 0, 3, 4]
def added172 : List (List Vertex) := [[4, 0, 1, 6, 7, 3, 5, 2], [2, 7]]
theorem accepted172 : OriginalAccepted (decode 172) 2 1 2
    tail172 added172 := by decide

def tail173 : List Vertex := [6, 1, 2, 0, 3, 4]
def added173 : List (List Vertex) := [[4, 0, 1, 7, 3, 5, 2], [2, 7, 5, 0, 6]]
theorem accepted173 : OriginalAccepted (decode 173) 0 2 1
    tail173 added173 := by decide

def tail174 : List Vertex := [7, 1, 2, 0, 3, 4]
def added174 : List (List Vertex) := [[4, 0, 1, 6, 5, 3, 7, 2], [2, 5, 0, 7]]
theorem accepted174 : OriginalAccepted (decode 174) 0 1 2
    tail174 added174 := by decide

def tail181 : List Vertex := [6, 2, 1, 0, 3, 4]
def added181 : List (List Vertex) := [[4, 0, 2, 7, 3, 5, 6, 1], [1, 5, 0, 6]]
theorem accepted181 : OriginalAccepted (decode 181) 0 1 1
    tail181 added181 := by decide

def tail182 : List Vertex := [7, 2, 1, 0, 3, 4]
def added182 : List (List Vertex) := [[4, 0, 2, 6, 1, 5, 7, 3], [3, 5, 0, 7]]
theorem accepted182 : OriginalAccepted (decode 182) 0 2 2
    tail182 added182 := by decide

def tail183 : List Vertex := [6, 1, 2, 0, 3, 4]
def added183 : List (List Vertex) := [[4, 0, 1, 5, 3, 7, 6, 2], [2, 7, 0, 6]]
theorem accepted183 : OriginalAccepted (decode 183) 2 1 1
    tail183 added183 := by decide

def tail184 : List Vertex := [7, 2, 1, 0, 3, 4]
def added184 : List (List Vertex) := [[4, 0, 2, 6, 7, 3, 5, 1], [1, 7]]
theorem accepted184 : OriginalAccepted (decode 184) 2 1 2
    tail184 added184 := by decide

def tail185 : List Vertex := [6, 2, 1, 0, 3, 4]
def added185 : List (List Vertex) := [[4, 0, 2, 7, 3, 5, 1], [1, 7, 5, 0, 6]]
theorem accepted185 : OriginalAccepted (decode 185) 0 2 1
    tail185 added185 := by decide

def tail186 : List Vertex := [7, 2, 1, 0, 3, 4]
def added186 : List (List Vertex) := [[4, 0, 2, 6, 5, 3, 7, 1], [1, 5, 0, 7]]
theorem accepted186 : OriginalAccepted (decode 186) 0 1 2
    tail186 added186 := by decide

def tail188 : List Vertex := [7, 2, 1, 0, 3, 4]
def added188 : List (List Vertex) := [[4, 0, 2, 6, 1, 7, 3, 5], [7, 5]]
theorem accepted188 : OriginalAccepted (decode 188) 2 0 2
    tail188 added188 := by decide

def tail189 : List Vertex := [6, 2, 1, 0, 3, 4]
def added189 : List (List Vertex) := [[4, 0, 5, 3, 7, 6, 1], [1, 7, 2, 0, 6]]
theorem accepted189 : OriginalAccepted (decode 189) 1 2 1
    tail189 added189 := by decide

def tail191 : List Vertex := [7, 2, 1, 0, 3, 4]
def added191 : List (List Vertex) := [[4, 0, 2, 6, 1, 7, 3, 5], [7, 0, 6, 5]]
theorem accepted191 : OriginalAccepted (decode 191) 1 0 2
    tail191 added191 := by decide

def tail212 : List Vertex := [6, 2, 1, 0, 3, 4]
def added212 : List (List Vertex) := [[4, 0, 2, 5, 1, 6, 3, 7], [6, 7]]
theorem accepted212 : OriginalAccepted (decode 212) 1 2 1
    tail212 added212 := by decide

def tail213 : List Vertex := [6, 2, 1, 0, 3, 4]
def added213 : List (List Vertex) := [[4, 0, 2, 5, 1, 6, 3, 7], [6, 0, 5, 7]]
theorem accepted213 : OriginalAccepted (decode 213) 0 2 1
    tail213 added213 := by decide

def tail214 : List Vertex := [5, 2, 1, 0, 3, 4]
def added214 : List (List Vertex) := [[4, 0, 7, 3, 6, 5, 1], [1, 6, 2, 0, 5]]
theorem accepted214 : OriginalAccepted (decode 214) 0 1 0
    tail214 added214 := by decide

def tail217 : List Vertex := [5, 1, 2, 0, 3, 4]
def added217 : List (List Vertex) := [[4, 0, 1, 7, 3, 6, 5, 2], [2, 6, 0, 5]]
theorem accepted217 : OriginalAccepted (decode 217) 1 0 0
    tail217 added217 := by decide

def tail218 : List Vertex := [5, 2, 1, 0, 3, 4]
def added218 : List (List Vertex) := [[4, 0, 2, 6, 3, 7, 5, 1], [1, 7, 0, 5]]
theorem accepted218 : OriginalAccepted (decode 218) 2 0 0
    tail218 added218 := by decide

def tail219 : List Vertex := [6, 2, 1, 0, 3, 4]
def added219 : List (List Vertex) := [[4, 0, 2, 5, 1, 7, 6, 3], [3, 7, 0, 6]]
theorem accepted219 : OriginalAccepted (decode 219) 2 1 1
    tail219 added219 := by decide

def tail220 : List Vertex := [6, 2, 1, 0, 3, 4]
def added220 : List (List Vertex) := [[4, 0, 2, 5, 6, 3, 7, 1], [1, 6]]
theorem accepted220 : OriginalAccepted (decode 220) 1 0 1
    tail220 added220 := by decide

def tail222 : List Vertex := [5, 2, 1, 0, 3, 4]
def added222 : List (List Vertex) := [[4, 0, 2, 6, 3, 7, 1], [1, 6, 7, 0, 5]]
theorem accepted222 : OriginalAccepted (decode 222) 2 1 0
    tail222 added222 := by decide

def tail223 : List Vertex := [6, 2, 1, 0, 3, 4]
def added223 : List (List Vertex) := [[4, 0, 2, 5, 7, 3, 6, 1], [1, 7, 0, 6]]
theorem accepted223 : OriginalAccepted (decode 223) 2 0 1
    tail223 added223 := by decide

def tail229 : List Vertex := [5, 2, 1, 0, 3, 4]
def added229 : List (List Vertex) := [[4, 0, 2, 7, 3, 6, 5, 1], [1, 6, 0, 5]]
theorem accepted229 : OriginalAccepted (decode 229) 1 0 0
    tail229 added229 := by decide

def tail230 : List Vertex := [5, 1, 2, 0, 3, 4]
def added230 : List (List Vertex) := [[4, 0, 1, 6, 3, 7, 5, 2], [2, 7, 0, 5]]
theorem accepted230 : OriginalAccepted (decode 230) 2 0 0
    tail230 added230 := by decide

def tail231 : List Vertex := [7, 2, 1, 0, 3, 4]
def added231 : List (List Vertex) := [[4, 0, 2, 5, 1, 6, 7, 3], [3, 6, 0, 7]]
theorem accepted231 : OriginalAccepted (decode 231) 1 2 2
    tail231 added231 := by decide

def tail232 : List Vertex := [7, 2, 1, 0, 3, 4]
def added232 : List (List Vertex) := [[4, 0, 2, 5, 1, 7, 3, 6], [7, 6]]
theorem accepted232 : OriginalAccepted (decode 232) 2 1 2
    tail232 added232 := by decide

def tail233 : List Vertex := [5, 2, 1, 0, 3, 4]
def added233 : List (List Vertex) := [[4, 0, 6, 3, 7, 5, 1], [1, 7, 2, 0, 5]]
theorem accepted233 : OriginalAccepted (decode 233) 0 2 0
    tail233 added233 := by decide

def tail234 : List Vertex := [7, 2, 1, 0, 3, 4]
def added234 : List (List Vertex) := [[4, 0, 2, 5, 1, 7, 3, 6], [7, 0, 5, 6]]
theorem accepted234 : OriginalAccepted (decode 234) 0 1 2
    tail234 added234 := by decide

def tail236 : List Vertex := [7, 2, 1, 0, 3, 4]
def added236 : List (List Vertex) := [[4, 0, 2, 5, 7, 3, 6, 1], [1, 7]]
theorem accepted236 : OriginalAccepted (decode 236) 2 0 2
    tail236 added236 := by decide

def tail237 : List Vertex := [5, 2, 1, 0, 3, 4]
def added237 : List (List Vertex) := [[4, 0, 2, 7, 3, 6, 1], [1, 7, 6, 0, 5]]
theorem accepted237 : OriginalAccepted (decode 237) 1 2 0
    tail237 added237 := by decide

def tail239 : List Vertex := [7, 2, 1, 0, 3, 4]
def added239 : List (List Vertex) := [[4, 0, 2, 5, 6, 3, 7, 1], [1, 6, 0, 7]]
theorem accepted239 : OriginalAccepted (decode 239) 1 0 2
    tail239 added239 := by decide

def tail244 : List Vertex := [6, 1, 2, 0, 3, 4]
def added244 : List (List Vertex) := [[4, 0, 1, 5, 6, 3, 7, 2], [2, 6]]
theorem accepted244 : OriginalAccepted (decode 244) 1 0 1
    tail244 added244 := by decide

def tail246 : List Vertex := [5, 1, 2, 0, 3, 4]
def added246 : List (List Vertex) := [[4, 0, 1, 6, 3, 7, 2], [2, 6, 7, 0, 5]]
theorem accepted246 : OriginalAccepted (decode 246) 2 1 0
    tail246 added246 := by decide

def tail247 : List Vertex := [6, 1, 2, 0, 3, 4]
def added247 : List (List Vertex) := [[4, 0, 1, 5, 7, 3, 6, 2], [2, 7, 0, 6]]
theorem accepted247 : OriginalAccepted (decode 247) 2 0 1
    tail247 added247 := by decide

def tail248 : List Vertex := [7, 1, 2, 0, 3, 4]
def added248 : List (List Vertex) := [[4, 0, 1, 5, 7, 3, 6, 2], [2, 7]]
theorem accepted248 : OriginalAccepted (decode 248) 2 0 2
    tail248 added248 := by decide

def tail249 : List Vertex := [5, 1, 2, 0, 3, 4]
def added249 : List (List Vertex) := [[4, 0, 1, 7, 3, 6, 2], [2, 7, 6, 0, 5]]
theorem accepted249 : OriginalAccepted (decode 249) 1 2 0
    tail249 added249 := by decide

def tail251 : List Vertex := [7, 1, 2, 0, 3, 4]
def added251 : List (List Vertex) := [[4, 0, 1, 5, 6, 3, 7, 2], [2, 6, 0, 7]]
theorem accepted251 : OriginalAccepted (decode 251) 1 0 2
    tail251 added251 := by decide

def tail252 : List Vertex := [6, 2, 1, 0, 3, 4]
def added252 : List (List Vertex) := [[4, 0, 2, 7, 3, 6, 1], [1, 7, 6]]
theorem accepted252 : OriginalAccepted (decode 252) 1 2 1
    tail252 added252 := by decide

def tail253 : List Vertex := [6, 2, 1, 0, 3, 4]
def added253 : List (List Vertex) := [[4, 0, 2, 7, 3, 6, 1], [1, 7, 5, 0, 6]]
theorem accepted253 : OriginalAccepted (decode 253) 0 2 1
    tail253 added253 := by decide

def tail254 : List Vertex := [7, 2, 1, 0, 3, 4]
def added254 : List (List Vertex) := [[4, 0, 2, 6, 3, 7, 1], [1, 6, 5, 0, 7]]
theorem accepted254 : OriginalAccepted (decode 254) 0 1 2
    tail254 added254 := by decide

def tail276 : List Vertex := [5, 2, 1, 0, 4, 3]
def added276 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [1, 6, 5]]
theorem accepted276 : OriginalAccepted (decode 276) 0 1 0
    tail276 added276 := by decide

def tail278 : List Vertex := [5, 2, 1, 0, 4, 3]
def added278 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [1, 6, 7, 0, 5]]
theorem accepted278 : OriginalAccepted (decode 278) 2 1 0
    tail278 added278 := by decide

def tail279 : List Vertex := [6, 2, 1, 0, 4, 3]
def added279 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 1], [1, 5, 7, 0, 6]]
theorem accepted279 : OriginalAccepted (decode 279) 2 0 1
    tail279 added279 := by decide

def tail280 : List Vertex := [5, 1, 2, 0, 4, 3]
def added280 : List (List Vertex) := [[3, 0, 1, 7, 5, 4, 6, 2], [2, 5]]
theorem accepted280 : OriginalAccepted (decode 280) 0 2 0
    tail280 added280 := by decide

def tail281 : List Vertex := [5, 1, 2, 0, 4, 3]
def added281 : List (List Vertex) := [[3, 0, 1, 7, 6, 4, 5, 2], [2, 6, 0, 5]]
theorem accepted281 : OriginalAccepted (decode 281) 1 2 0
    tail281 added281 := by decide

def tail283 : List Vertex := [7, 1, 2, 0, 4, 3]
def added283 : List (List Vertex) := [[3, 0, 1, 5, 4, 6, 2], [2, 5, 6, 0, 7]]
theorem accepted283 : OriginalAccepted (decode 283) 1 0 2
    tail283 added283 := by decide

def tail284 : List Vertex := [6, 1, 2, 0, 4, 3]
def added284 : List (List Vertex) := [[3, 0, 1, 7, 6, 4, 5, 2], [2, 6]]
theorem accepted284 : OriginalAccepted (decode 284) 1 2 1
    tail284 added284 := by decide

def tail285 : List Vertex := [6, 1, 2, 0, 4, 3]
def added285 : List (List Vertex) := [[3, 0, 1, 7, 5, 4, 6, 2], [2, 5, 0, 6]]
theorem accepted285 : OriginalAccepted (decode 285) 0 2 1
    tail285 added285 := by decide

def tail286 : List Vertex := [7, 1, 2, 0, 4, 3]
def added286 : List (List Vertex) := [[3, 0, 1, 6, 4, 5, 2], [2, 6, 5, 0, 7]]
theorem accepted286 : OriginalAccepted (decode 286) 0 1 2
    tail286 added286 := by decide

def tail292 : List Vertex := [5, 2, 1, 0, 4, 3]
def added292 : List (List Vertex) := [[3, 0, 2, 7, 5, 4, 6, 1], [1, 5]]
theorem accepted292 : OriginalAccepted (decode 292) 0 2 0
    tail292 added292 := by decide

def tail293 : List Vertex := [5, 2, 1, 0, 4, 3]
def added293 : List (List Vertex) := [[3, 0, 2, 7, 6, 4, 5, 1], [1, 6, 0, 5]]
theorem accepted293 : OriginalAccepted (decode 293) 1 2 0
    tail293 added293 := by decide

def tail295 : List Vertex := [7, 2, 1, 0, 4, 3]
def added295 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 1], [1, 5, 6, 0, 7]]
theorem accepted295 : OriginalAccepted (decode 295) 1 0 2
    tail295 added295 := by decide

def tail296 : List Vertex := [5, 2, 1, 0, 4, 3]
def added296 : List (List Vertex) := [[3, 0, 2, 7, 1, 5, 4, 6], [5, 6]]
theorem accepted296 : OriginalAccepted (decode 296) 0 1 0
    tail296 added296 := by decide

def tail298 : List Vertex := [5, 2, 1, 0, 4, 3]
def added298 : List (List Vertex) := [[3, 0, 2, 7, 1, 5, 4, 6], [5, 0, 7, 6]]
theorem accepted298 : OriginalAccepted (decode 298) 2 1 0
    tail298 added298 := by decide

def tail299 : List Vertex := [7, 2, 1, 0, 4, 3]
def added299 : List (List Vertex) := [[3, 0, 6, 4, 5, 7, 1], [1, 5, 2, 0, 7]]
theorem accepted299 : OriginalAccepted (decode 299) 2 0 2
    tail299 added299 := by decide

def tail301 : List Vertex := [5, 2, 1, 0, 4, 3]
def added301 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted301 : OriginalAccepted (decode 301) 1 0 0
    tail301 added301 := by decide

def tail302 : List Vertex := [7, 1, 2, 0, 4, 3]
def added302 : List (List Vertex) := [[3, 0, 1, 6, 4, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted302 : OriginalAccepted (decode 302) 0 2 2
    tail302 added302 := by decide

def tail303 : List Vertex := [7, 2, 1, 0, 4, 3]
def added303 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted303 : OriginalAccepted (decode 303) 1 2 2
    tail303 added303 := by decide

def tail308 : List Vertex := [6, 2, 1, 0, 4, 3]
def added308 : List (List Vertex) := [[3, 0, 2, 7, 6, 4, 5, 1], [1, 6]]
theorem accepted308 : OriginalAccepted (decode 308) 1 2 1
    tail308 added308 := by decide

def tail309 : List Vertex := [6, 2, 1, 0, 4, 3]
def added309 : List (List Vertex) := [[3, 0, 2, 7, 5, 4, 6, 1], [1, 5, 0, 6]]
theorem accepted309 : OriginalAccepted (decode 309) 0 2 1
    tail309 added309 := by decide

def tail310 : List Vertex := [7, 2, 1, 0, 4, 3]
def added310 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [1, 6, 5, 0, 7]]
theorem accepted310 : OriginalAccepted (decode 310) 0 1 2
    tail310 added310 := by decide

def tail313 : List Vertex := [6, 2, 1, 0, 4, 3]
def added313 : List (List Vertex) := [[3, 0, 2, 7, 1, 5, 6, 4], [4, 5, 0, 6]]
theorem accepted313 : OriginalAccepted (decode 313) 0 1 1
    tail313 added313 := by decide

def tail314 : List Vertex := [7, 2, 1, 0, 4, 3]
def added314 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted314 : OriginalAccepted (decode 314) 0 2 2
    tail314 added314 := by decide

def tail315 : List Vertex := [7, 1, 2, 0, 4, 3]
def added315 : List (List Vertex) := [[3, 0, 1, 5, 4, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted315 : OriginalAccepted (decode 315) 1 2 2
    tail315 added315 := by decide

def tail316 : List Vertex := [6, 2, 1, 0, 4, 3]
def added316 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 4, 5], [6, 5]]
theorem accepted316 : OriginalAccepted (decode 316) 1 0 1
    tail316 added316 := by decide

def tail318 : List Vertex := [7, 2, 1, 0, 4, 3]
def added318 : List (List Vertex) := [[3, 0, 5, 4, 6, 7, 1], [1, 6, 2, 0, 7]]
theorem accepted318 : OriginalAccepted (decode 318) 2 1 2
    tail318 added318 := by decide

def tail319 : List Vertex := [6, 2, 1, 0, 4, 3]
def added319 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 4, 5], [6, 0, 7, 5]]
theorem accepted319 : OriginalAccepted (decode 319) 2 0 1
    tail319 added319 := by decide

def tail324 : List Vertex := [5, 4, 3, 0, 1, 2]
def added324 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 5]]
theorem accepted324 : OriginalAccepted (decode 324) 0 1 0
    tail324 added324 := by decide

def tail326 : List Vertex := [5, 4, 3, 0, 1, 2]
def added326 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 7, 0, 5]]
theorem accepted326 : OriginalAccepted (decode 326) 2 1 0
    tail326 added326 := by decide

def tail327 : List Vertex := [6, 4, 3, 0, 1, 2]
def added327 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 3], [3, 5, 7, 0, 6]]
theorem accepted327 : OriginalAccepted (decode 327) 2 0 1
    tail327 added327 := by decide

def tail328 : List Vertex := [5, 4, 3, 0, 1, 2]
def added328 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 1, 7], [5, 7]]
theorem accepted328 : OriginalAccepted (decode 328) 0 2 0
    tail328 added328 := by decide

def tail329 : List Vertex := [5, 4, 3, 0, 1, 2]
def added329 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 1, 7], [5, 0, 6, 7]]
theorem accepted329 : OriginalAccepted (decode 329) 1 2 0
    tail329 added329 := by decide

def tail331 : List Vertex := [6, 4, 3, 0, 1, 2]
def added331 : List (List Vertex) := [[2, 0, 7, 1, 5, 6, 3], [3, 5, 4, 0, 6]]
theorem accepted331 : OriginalAccepted (decode 331) 1 0 1
    tail331 added331 := by decide

def tail332 : List Vertex := [6, 4, 3, 0, 1, 2]
def added332 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 1, 7], [6, 7]]
theorem accepted332 : OriginalAccepted (decode 332) 1 2 1
    tail332 added332 := by decide

def tail333 : List Vertex := [6, 4, 3, 0, 1, 2]
def added333 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 1, 7], [6, 0, 5, 7]]
theorem accepted333 : OriginalAccepted (decode 333) 0 2 1
    tail333 added333 := by decide

def tail334 : List Vertex := [5, 4, 3, 0, 1, 2]
def added334 : List (List Vertex) := [[2, 0, 7, 1, 6, 5, 3], [3, 6, 4, 0, 5]]
theorem accepted334 : OriginalAccepted (decode 334) 0 1 0
    tail334 added334 := by decide

def tail336 : List Vertex := [5, 4, 3, 0, 2, 1]
def added336 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 5]]
theorem accepted336 : OriginalAccepted (decode 336) 0 1 0
    tail336 added336 := by decide

def tail338 : List Vertex := [5, 4, 3, 0, 2, 1]
def added338 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 7, 0, 5]]
theorem accepted338 : OriginalAccepted (decode 338) 2 1 0
    tail338 added338 := by decide

def tail339 : List Vertex := [6, 4, 3, 0, 2, 1]
def added339 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [3, 5, 7, 0, 6]]
theorem accepted339 : OriginalAccepted (decode 339) 2 0 1
    tail339 added339 := by decide

def tail344 : List Vertex := [5, 1, 2, 0, 4, 3]
def added344 : List (List Vertex) := [[3, 0, 1, 7, 6, 4, 5, 2], [2, 6, 3, 5]]
theorem accepted344 : OriginalAccepted (decode 344) 1 2 0
    tail344 added344 := by decide

def tail348 : List Vertex := [6, 1, 2, 0, 4, 3]
def added348 : List (List Vertex) := [[3, 0, 1, 7, 5, 4, 6, 2], [2, 5, 3, 6]]
theorem accepted348 : OriginalAccepted (decode 348) 0 2 1
    tail348 added348 := by decide

def tail352 : List Vertex := [5, 4, 3, 0, 2, 1]
def added352 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 2, 7], [5, 7]]
theorem accepted352 : OriginalAccepted (decode 352) 0 2 0
    tail352 added352 := by decide

def tail353 : List Vertex := [5, 4, 3, 0, 2, 1]
def added353 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 2, 7], [5, 0, 6, 7]]
theorem accepted353 : OriginalAccepted (decode 353) 1 2 0
    tail353 added353 := by decide

def tail355 : List Vertex := [6, 4, 3, 0, 2, 1]
def added355 : List (List Vertex) := [[1, 0, 7, 2, 5, 6, 3], [3, 5, 4, 0, 6]]
theorem accepted355 : OriginalAccepted (decode 355) 1 0 1
    tail355 added355 := by decide

def tail356 : List Vertex := [5, 2, 1, 0, 4, 3]
def added356 : List (List Vertex) := [[3, 0, 2, 7, 6, 4, 5, 1], [1, 6, 3, 5]]
theorem accepted356 : OriginalAccepted (decode 356) 1 2 0
    tail356 added356 := by decide

def tail363 : List Vertex := [6, 4, 3, 0, 2, 1]
def added363 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 0, 4], [4, 5, 1, 0, 7, 6]]
theorem accepted363 : OriginalAccepted (decode 363) 2 1 1
    tail363 added363 := by decide

def tail364 : List Vertex := [5, 2, 1, 0, 4, 3]
def added364 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 2, 0], [5, 6, 3, 0]]
theorem accepted364 : OriginalAccepted (decode 364) 1 0 0
    tail364 added364 := by decide

def tail366 : List Vertex := [5, 4, 3, 0, 1, 2]
def added366 : List (List Vertex) := [[2, 7, 1, 6, 3, 5, 0, 4], [4, 6, 7, 0, 2, 5]]
theorem accepted366 : OriginalAccepted (decode 366) 2 1 0
    tail366 added366 := by decide

def tail367 : List Vertex := [6, 4, 3, 0, 2, 1]
def added367 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 0, 4], [4, 5, 7, 0, 1, 6]]
theorem accepted367 : OriginalAccepted (decode 367) 2 0 1
    tail367 added367 := by decide

def tail368 : List Vertex := [6, 4, 3, 0, 2, 1]
def added368 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 2, 7], [6, 7]]
theorem accepted368 : OriginalAccepted (decode 368) 1 2 1
    tail368 added368 := by decide

def tail369 : List Vertex := [6, 4, 3, 0, 2, 1]
def added369 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 2, 7], [6, 0, 5, 7]]
theorem accepted369 : OriginalAccepted (decode 369) 0 2 1
    tail369 added369 := by decide

def tail370 : List Vertex := [5, 4, 3, 0, 2, 1]
def added370 : List (List Vertex) := [[1, 0, 7, 2, 6, 5, 3], [3, 6, 4, 0, 5]]
theorem accepted370 : OriginalAccepted (decode 370) 0 1 0
    tail370 added370 := by decide

def tail372 : List Vertex := [6, 2, 1, 0, 4, 3]
def added372 : List (List Vertex) := [[3, 0, 2, 7, 5, 4, 6, 1], [1, 5, 3, 6]]
theorem accepted372 : OriginalAccepted (decode 372) 0 2 1
    tail372 added372 := by decide

def tail376 : List Vertex := [6, 2, 1, 0, 4, 3]
def added376 : List (List Vertex) := [[3, 6, 4, 5, 1, 7, 2, 0], [6, 5, 3, 0]]
theorem accepted376 : OriginalAccepted (decode 376) 0 1 1
    tail376 added376 := by decide

def tail378 : List Vertex := [5, 4, 3, 0, 2, 1]
def added378 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 0, 4], [4, 6, 7, 0, 1, 5]]
theorem accepted378 : OriginalAccepted (decode 378) 2 1 0
    tail378 added378 := by decide

def tail379 : List Vertex := [6, 4, 3, 0, 1, 2]
def added379 : List (List Vertex) := [[2, 7, 1, 5, 3, 6, 0, 4], [4, 5, 7, 0, 2, 6]]
theorem accepted379 : OriginalAccepted (decode 379) 2 0 1
    tail379 added379 := by decide

def tail382 : List Vertex := [5, 4, 3, 0, 2, 1]
def added382 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 0, 4], [4, 6, 1, 0, 7, 5]]
theorem accepted382 : OriginalAccepted (decode 382) 2 0 0
    tail382 added382 := by decide

def tail388 : List Vertex := [5, 3, 4, 0, 1, 2]
def added388 : List (List Vertex) := [[2, 0, 3, 7, 5, 1, 6, 4], [4, 5]]
theorem accepted388 : OriginalAccepted (decode 388) 0 2 0
    tail388 added388 := by decide

def tail389 : List Vertex := [5, 3, 4, 0, 1, 2]
def added389 : List (List Vertex) := [[2, 0, 3, 7, 6, 1, 5, 4], [4, 6, 0, 5]]
theorem accepted389 : OriginalAccepted (decode 389) 1 2 0
    tail389 added389 := by decide

def tail391 : List Vertex := [7, 3, 4, 0, 1, 2]
def added391 : List (List Vertex) := [[2, 0, 3, 5, 1, 6, 4], [4, 5, 6, 0, 7]]
theorem accepted391 : OriginalAccepted (decode 391) 1 0 2
    tail391 added391 := by decide

def tail392 : List Vertex := [5, 4, 3, 0, 1, 2]
def added392 : List (List Vertex) := [[2, 0, 4, 6, 5, 1, 7, 3], [3, 5]]
theorem accepted392 : OriginalAccepted (decode 392) 0 1 0
    tail392 added392 := by decide

def tail394 : List Vertex := [5, 4, 3, 0, 1, 2]
def added394 : List (List Vertex) := [[2, 0, 4, 6, 7, 1, 5, 3], [3, 7, 0, 5]]
theorem accepted394 : OriginalAccepted (decode 394) 2 1 0
    tail394 added394 := by decide

def tail395 : List Vertex := [6, 4, 3, 0, 1, 2]
def added395 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 3], [3, 5, 7, 0, 6]]
theorem accepted395 : OriginalAccepted (decode 395) 2 0 1
    tail395 added395 := by decide

def tail397 : List Vertex := [5, 3, 4, 0, 1, 2]
def added397 : List (List Vertex) := [[2, 0, 3, 7, 1, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted397 : OriginalAccepted (decode 397) 1 0 0
    tail397 added397 := by decide

def tail398 : List Vertex := [5, 4, 3, 0, 1, 2]
def added398 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 5, 3], [3, 7, 0, 5]]
theorem accepted398 : OriginalAccepted (decode 398) 2 0 0
    tail398 added398 := by decide

def tail399 : List Vertex := [6, 4, 3, 0, 1, 2]
def added399 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 6, 1], [1, 7, 0, 6]]
theorem accepted399 : OriginalAccepted (decode 399) 2 1 1
    tail399 added399 := by decide

def tail400 : List Vertex := [5, 3, 4, 0, 2, 1]
def added400 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5]]
theorem accepted400 : OriginalAccepted (decode 400) 0 2 0
    tail400 added400 := by decide

def tail401 : List Vertex := [5, 3, 4, 0, 2, 1]
def added401 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6, 0, 5]]
theorem accepted401 : OriginalAccepted (decode 401) 1 2 0
    tail401 added401 := by decide

def tail403 : List Vertex := [7, 3, 4, 0, 2, 1]
def added403 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 4], [4, 5, 6, 0, 7]]
theorem accepted403 : OriginalAccepted (decode 403) 1 0 2
    tail403 added403 := by decide

def tail404 : List Vertex := [5, 3, 4, 0, 2, 1]
def added404 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6, 1, 5]]
theorem accepted404 : OriginalAccepted (decode 404) 1 2 0
    tail404 added404 := by decide

def tail411 : List Vertex := [6, 4, 3, 0, 2, 1]
def added411 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 0, 4], [4, 5, 1, 0, 7, 6]]
theorem accepted411 : OriginalAccepted (decode 411) 2 1 1
    tail411 added411 := by decide

def tail412 : List Vertex := [5, 3, 4, 0, 1, 2]
def added412 : List (List Vertex) := [[2, 5, 4, 6, 1, 7, 3, 0], [5, 6, 2, 0]]
theorem accepted412 : OriginalAccepted (decode 412) 1 0 0
    tail412 added412 := by decide

def tail414 : List Vertex := [7, 1, 2, 0, 4, 3]
def added414 : List (List Vertex) := [[4, 5, 2, 6, 1, 0, 3, 7], [3, 5, 0, 7, 6, 4]]
theorem accepted414 : OriginalAccepted (decode 414) 2 1 2
    tail414 added414 := by decide

def tail415 : List Vertex := [7, 3, 4, 0, 2, 1]
def added415 : List (List Vertex) := [[2, 6, 4, 5, 3, 0, 1, 7], [1, 6, 0, 7, 5, 2]]
theorem accepted415 : OriginalAccepted (decode 415) 2 0 2
    tail415 added415 := by decide

def tail416 : List Vertex := [5, 4, 3, 0, 2, 1]
def added416 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5]]
theorem accepted416 : OriginalAccepted (decode 416) 0 1 0
    tail416 added416 := by decide

def tail418 : List Vertex := [5, 4, 3, 0, 2, 1]
def added418 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7, 0, 5]]
theorem accepted418 : OriginalAccepted (decode 418) 2 1 0
    tail418 added418 := by decide

def tail419 : List Vertex := [6, 4, 3, 0, 2, 1]
def added419 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [3, 5, 7, 0, 6]]
theorem accepted419 : OriginalAccepted (decode 419) 2 0 1
    tail419 added419 := by decide

def tail423 : List Vertex := [7, 3, 4, 0, 2, 1]
def added423 : List (List Vertex) := [[1, 6, 4, 5, 2, 7, 0, 3], [3, 5, 1, 0, 6, 7]]
theorem accepted423 : OriginalAccepted (decode 423) 1 2 2
    tail423 added423 := by decide

def tail424 : List Vertex := [5, 4, 3, 0, 2, 1]
def added424 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7, 1, 5]]
theorem accepted424 : OriginalAccepted (decode 424) 2 1 0
    tail424 added424 := by decide

def tail428 : List Vertex := [5, 4, 3, 0, 1, 2]
def added428 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 4, 0], [5, 7, 2, 0]]
theorem accepted428 : OriginalAccepted (decode 428) 2 0 0
    tail428 added428 := by decide

def tail429 : List Vertex := [6, 1, 2, 0, 3, 4]
def added429 : List (List Vertex) := [[3, 5, 2, 7, 1, 0, 4, 6], [4, 5, 0, 6, 7, 3]]
theorem accepted429 : OriginalAccepted (decode 429) 1 2 1
    tail429 added429 := by decide

def tail431 : List Vertex := [6, 4, 3, 0, 2, 1]
def added431 : List (List Vertex) := [[2, 7, 3, 5, 4, 0, 1, 6], [1, 7, 0, 6, 5, 2]]
theorem accepted431 : OriginalAccepted (decode 431) 1 0 1
    tail431 added431 := by decide

def tail433 : List Vertex := [5, 3, 4, 0, 2, 1]
def added433 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted433 : OriginalAccepted (decode 433) 1 0 0
    tail433 added433 := by decide

def tail434 : List Vertex := [5, 4, 3, 0, 2, 1]
def added434 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 5, 3], [3, 7, 0, 5]]
theorem accepted434 : OriginalAccepted (decode 434) 2 0 0
    tail434 added434 := by decide

def tail435 : List Vertex := [6, 4, 3, 0, 2, 1]
def added435 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 6, 2], [2, 7, 0, 6]]
theorem accepted435 : OriginalAccepted (decode 435) 2 1 1
    tail435 added435 := by decide

def tail436 : List Vertex := [5, 3, 4, 0, 2, 1]
def added436 : List (List Vertex) := [[1, 5, 4, 6, 2, 7, 3, 0], [5, 6, 1, 0]]
theorem accepted436 : OriginalAccepted (decode 436) 1 0 0
    tail436 added436 := by decide

def tail438 : List Vertex := [7, 2, 1, 0, 4, 3]
def added438 : List (List Vertex) := [[4, 5, 1, 6, 2, 0, 3, 7], [3, 5, 0, 7, 6, 4]]
theorem accepted438 : OriginalAccepted (decode 438) 2 1 2
    tail438 added438 := by decide

def tail439 : List Vertex := [7, 3, 4, 0, 1, 2]
def added439 : List (List Vertex) := [[1, 6, 4, 5, 3, 0, 2, 7], [2, 6, 0, 7, 5, 1]]
theorem accepted439 : OriginalAccepted (decode 439) 2 0 2
    tail439 added439 := by decide

def tail440 : List Vertex := [5, 4, 3, 0, 2, 1]
def added440 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 4, 0], [5, 7, 1, 0]]
theorem accepted440 : OriginalAccepted (decode 440) 2 0 0
    tail440 added440 := by decide

def tail441 : List Vertex := [6, 2, 1, 0, 3, 4]
def added441 : List (List Vertex) := [[3, 5, 1, 7, 2, 0, 4, 6], [4, 5, 0, 6, 7, 3]]
theorem accepted441 : OriginalAccepted (decode 441) 1 2 1
    tail441 added441 := by decide

def tail443 : List Vertex := [6, 4, 3, 0, 1, 2]
def added443 : List (List Vertex) := [[1, 7, 3, 5, 4, 0, 2, 6], [2, 7, 0, 6, 5, 1]]
theorem accepted443 : OriginalAccepted (decode 443) 1 0 1
    tail443 added443 := by decide

def tail444 : List Vertex := [6, 4, 3, 0, 2, 1]
def added444 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 4, 0], [6, 7, 1, 0]]
theorem accepted444 : OriginalAccepted (decode 444) 2 1 1
    tail444 added444 := by decide

def tail445 : List Vertex := [6, 2, 1, 0, 3, 4]
def added445 : List (List Vertex) := [[4, 5, 3, 7, 1, 6, 0, 2], [2, 7, 5, 0, 4, 6]]
theorem accepted445 : OriginalAccepted (decode 445) 0 2 1
    tail445 added445 := by decide

def tail446 : List Vertex := [7, 2, 1, 0, 4, 3]
def added446 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 0, 2], [2, 6, 5, 0, 3, 7]]
theorem accepted446 : OriginalAccepted (decode 446) 0 1 2
    tail446 added446 := by decide

def tail452 : List Vertex := [6, 3, 4, 0, 1, 2]
def added452 : List (List Vertex) := [[2, 0, 3, 7, 6, 1, 5, 4], [4, 6]]
theorem accepted452 : OriginalAccepted (decode 452) 1 2 1
    tail452 added452 := by decide

def tail453 : List Vertex := [6, 3, 4, 0, 1, 2]
def added453 : List (List Vertex) := [[2, 0, 3, 7, 5, 1, 6, 4], [4, 5, 0, 6]]
theorem accepted453 : OriginalAccepted (decode 453) 0 2 1
    tail453 added453 := by decide

def tail454 : List Vertex := [7, 3, 4, 0, 1, 2]
def added454 : List (List Vertex) := [[2, 0, 3, 6, 1, 5, 4], [4, 6, 5, 0, 7]]
theorem accepted454 : OriginalAccepted (decode 454) 0 1 2
    tail454 added454 := by decide

def tail457 : List Vertex := [6, 3, 4, 0, 1, 2]
def added457 : List (List Vertex) := [[2, 0, 3, 7, 1, 5, 6, 4], [4, 5, 0, 6]]
theorem accepted457 : OriginalAccepted (decode 457) 0 1 1
    tail457 added457 := by decide

def tail458 : List Vertex := [5, 4, 3, 0, 1, 2]
def added458 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 5, 1], [1, 7, 0, 5]]
theorem accepted458 : OriginalAccepted (decode 458) 2 0 0
    tail458 added458 := by decide

def tail459 : List Vertex := [6, 4, 3, 0, 1, 2]
def added459 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 6, 3], [3, 7, 0, 6]]
theorem accepted459 : OriginalAccepted (decode 459) 2 1 1
    tail459 added459 := by decide

def tail460 : List Vertex := [6, 4, 3, 0, 1, 2]
def added460 : List (List Vertex) := [[2, 0, 4, 5, 6, 1, 7, 3], [3, 6]]
theorem accepted460 : OriginalAccepted (decode 460) 1 0 1
    tail460 added460 := by decide

def tail462 : List Vertex := [5, 4, 3, 0, 1, 2]
def added462 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 3], [3, 6, 7, 0, 5]]
theorem accepted462 : OriginalAccepted (decode 462) 2 1 0
    tail462 added462 := by decide

def tail463 : List Vertex := [6, 4, 3, 0, 1, 2]
def added463 : List (List Vertex) := [[2, 0, 4, 5, 7, 1, 6, 3], [3, 7, 0, 6]]
theorem accepted463 : OriginalAccepted (decode 463) 2 0 1
    tail463 added463 := by decide

def tail464 : List Vertex := [6, 3, 4, 0, 2, 1]
def added464 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6]]
theorem accepted464 : OriginalAccepted (decode 464) 1 2 1
    tail464 added464 := by decide

def tail465 : List Vertex := [6, 3, 4, 0, 2, 1]
def added465 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5, 0, 6]]
theorem accepted465 : OriginalAccepted (decode 465) 0 2 1
    tail465 added465 := by decide

def tail466 : List Vertex := [7, 3, 4, 0, 2, 1]
def added466 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 4], [4, 6, 5, 0, 7]]
theorem accepted466 : OriginalAccepted (decode 466) 0 1 2
    tail466 added466 := by decide

def tail468 : List Vertex := [6, 3, 4, 0, 2, 1]
def added468 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5, 1, 6]]
theorem accepted468 : OriginalAccepted (decode 468) 0 2 1
    tail468 added468 := by decide

def tail472 : List Vertex := [6, 3, 4, 0, 1, 2]
def added472 : List (List Vertex) := [[2, 6, 4, 5, 1, 7, 3, 0], [6, 5, 2, 0]]
theorem accepted472 : OriginalAccepted (decode 472) 0 1 1
    tail472 added472 := by decide

def tail474 : List Vertex := [7, 3, 4, 0, 2, 1]
def added474 : List (List Vertex) := [[2, 5, 4, 6, 3, 0, 1, 7], [1, 5, 0, 7, 6, 2]]
theorem accepted474 : OriginalAccepted (decode 474) 2 1 2
    tail474 added474 := by decide

def tail475 : List Vertex := [7, 1, 2, 0, 4, 3]
def added475 : List (List Vertex) := [[4, 6, 2, 5, 1, 0, 3, 7], [3, 6, 0, 7, 5, 4]]
theorem accepted475 : OriginalAccepted (decode 475) 2 0 2
    tail475 added475 := by decide

def tail478 : List Vertex := [5, 4, 3, 0, 2, 1]
def added478 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 0, 4], [4, 6, 1, 0, 7, 5]]
theorem accepted478 : OriginalAccepted (decode 478) 2 0 0
    tail478 added478 := by decide

def tail481 : List Vertex := [6, 3, 4, 0, 2, 1]
def added481 : List (List Vertex) := [[1, 0, 3, 7, 2, 5, 6, 4], [4, 5, 0, 6]]
theorem accepted481 : OriginalAccepted (decode 481) 0 1 1
    tail481 added481 := by decide

def tail482 : List Vertex := [5, 4, 3, 0, 2, 1]
def added482 : List (List Vertex) := [[1, 0, 4, 6, 3, 7, 5, 2], [2, 7, 0, 5]]
theorem accepted482 : OriginalAccepted (decode 482) 2 0 0
    tail482 added482 := by decide

def tail483 : List Vertex := [6, 4, 3, 0, 2, 1]
def added483 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 6, 3], [3, 7, 0, 6]]
theorem accepted483 : OriginalAccepted (decode 483) 2 1 1
    tail483 added483 := by decide

def tail484 : List Vertex := [6, 3, 4, 0, 2, 1]
def added484 : List (List Vertex) := [[1, 6, 4, 5, 2, 7, 3, 0], [6, 5, 1, 0]]
theorem accepted484 : OriginalAccepted (decode 484) 0 1 1
    tail484 added484 := by decide

def tail486 : List Vertex := [7, 3, 4, 0, 1, 2]
def added486 : List (List Vertex) := [[1, 5, 4, 6, 3, 0, 2, 7], [2, 5, 0, 7, 6, 1]]
theorem accepted486 : OriginalAccepted (decode 486) 2 1 2
    tail486 added486 := by decide

def tail487 : List Vertex := [7, 2, 1, 0, 4, 3]
def added487 : List (List Vertex) := [[4, 6, 1, 5, 2, 0, 3, 7], [3, 6, 0, 7, 5, 4]]
theorem accepted487 : OriginalAccepted (decode 487) 2 0 2
    tail487 added487 := by decide

def tail488 : List Vertex := [5, 4, 3, 0, 2, 1]
def added488 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 4, 0], [5, 7, 1, 0]]
theorem accepted488 : OriginalAccepted (decode 488) 2 0 0
    tail488 added488 := by decide

def tail489 : List Vertex := [5, 2, 1, 0, 3, 4]
def added489 : List (List Vertex) := [[4, 6, 3, 7, 1, 5, 0, 2], [2, 7, 6, 0, 4, 5]]
theorem accepted489 : OriginalAccepted (decode 489) 1 2 0
    tail489 added489 := by decide

def tail491 : List Vertex := [7, 2, 1, 0, 4, 3]
def added491 : List (List Vertex) := [[3, 6, 4, 5, 1, 7, 0, 2], [2, 5, 6, 0, 3, 7]]
theorem accepted491 : OriginalAccepted (decode 491) 1 0 2
    tail491 added491 := by decide

def tail492 : List Vertex := [6, 4, 3, 0, 2, 1]
def added492 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 4, 0], [6, 7, 1, 0]]
theorem accepted492 : OriginalAccepted (decode 492) 2 1 1
    tail492 added492 := by decide

def tail493 : List Vertex := [5, 2, 1, 0, 3, 4]
def added493 : List (List Vertex) := [[3, 6, 1, 7, 2, 0, 4, 5], [4, 6, 0, 5, 7, 3]]
theorem accepted493 : OriginalAccepted (decode 493) 0 2 0
    tail493 added493 := by decide

def tail494 : List Vertex := [5, 4, 3, 0, 1, 2]
def added494 : List (List Vertex) := [[1, 7, 3, 6, 4, 0, 2, 5], [2, 7, 0, 5, 6, 1]]
theorem accepted494 : OriginalAccepted (decode 494) 0 1 0
    tail494 added494 := by decide

def tail496 : List Vertex := [6, 4, 3, 0, 2, 1]
def added496 : List (List Vertex) := [[1, 0, 4, 5, 6, 2, 7, 3], [3, 6]]
theorem accepted496 : OriginalAccepted (decode 496) 1 0 1
    tail496 added496 := by decide

def tail498 : List Vertex := [5, 4, 3, 0, 2, 1]
def added498 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 3], [3, 6, 7, 0, 5]]
theorem accepted498 : OriginalAccepted (decode 498) 2 1 0
    tail498 added498 := by decide

def tail499 : List Vertex := [6, 4, 3, 0, 2, 1]
def added499 : List (List Vertex) := [[1, 0, 4, 5, 7, 2, 6, 3], [3, 7, 0, 6]]
theorem accepted499 : OriginalAccepted (decode 499) 2 0 1
    tail499 added499 := by decide

def tail502 : List Vertex := [7, 3, 4, 0, 2, 1]
def added502 : List (List Vertex) := [[1, 5, 4, 6, 2, 7, 0, 3], [3, 6, 1, 0, 5, 7]]
theorem accepted502 : OriginalAccepted (decode 502) 0 2 2
    tail502 added502 := by decide

def tail504 : List Vertex := [6, 4, 3, 0, 1, 2]
def added504 : List (List Vertex) := [[2, 6, 3, 7, 1, 5, 4, 0], [6, 7, 2, 0]]
theorem accepted504 : OriginalAccepted (decode 504) 2 1 1
    tail504 added504 := by decide

def tail505 : List Vertex := [5, 1, 2, 0, 3, 4]
def added505 : List (List Vertex) := [[3, 6, 2, 7, 1, 0, 4, 5], [4, 6, 0, 5, 7, 3]]
theorem accepted505 : OriginalAccepted (decode 505) 0 2 0
    tail505 added505 := by decide

def tail506 : List Vertex := [5, 4, 3, 0, 2, 1]
def added506 : List (List Vertex) := [[2, 7, 3, 6, 4, 0, 1, 5], [1, 7, 0, 5, 6, 2]]
theorem accepted506 : OriginalAccepted (decode 506) 0 1 0
    tail506 added506 := by decide

def tail508 : List Vertex := [6, 4, 3, 0, 2, 1]
def added508 : List (List Vertex) := [[1, 0, 4, 5, 7, 2, 6, 3], [3, 7, 1, 6]]
theorem accepted508 : OriginalAccepted (decode 508) 2 0 1
    tail508 added508 := by decide

def tail532 : List Vertex := [5, 2, 1, 0, 4, 3]
def added532 : List (List Vertex) := [[3, 0, 2, 6, 1, 5, 4, 7], [5, 7]]
theorem accepted532 : OriginalAccepted (decode 532) 0 2 0
    tail532 added532 := by decide

def tail533 : List Vertex := [5, 2, 1, 0, 4, 3]
def added533 : List (List Vertex) := [[3, 0, 2, 6, 1, 5, 4, 7], [5, 0, 6, 7]]
theorem accepted533 : OriginalAccepted (decode 533) 1 2 0
    tail533 added533 := by decide

def tail535 : List Vertex := [6, 2, 1, 0, 4, 3]
def added535 : List (List Vertex) := [[3, 0, 7, 4, 5, 6, 1], [1, 5, 2, 0, 6]]
theorem accepted535 : OriginalAccepted (decode 535) 1 0 1
    tail535 added535 := by decide

def tail536 : List Vertex := [5, 2, 1, 0, 4, 3]
def added536 : List (List Vertex) := [[3, 0, 2, 6, 5, 4, 7, 1], [1, 5]]
theorem accepted536 : OriginalAccepted (decode 536) 0 1 0
    tail536 added536 := by decide

def tail538 : List Vertex := [5, 2, 1, 0, 4, 3]
def added538 : List (List Vertex) := [[3, 0, 2, 6, 7, 4, 5, 1], [1, 7, 0, 5]]
theorem accepted538 : OriginalAccepted (decode 538) 2 1 0
    tail538 added538 := by decide

def tail539 : List Vertex := [6, 2, 1, 0, 4, 3]
def added539 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 1], [1, 5, 7, 0, 6]]
theorem accepted539 : OriginalAccepted (decode 539) 2 0 1
    tail539 added539 := by decide

def tail541 : List Vertex := [6, 1, 2, 0, 4, 3]
def added541 : List (List Vertex) := [[3, 0, 1, 7, 4, 5, 6, 2], [2, 5, 0, 6]]
theorem accepted541 : OriginalAccepted (decode 541) 0 1 1
    tail541 added541 := by decide

def tail542 : List Vertex := [5, 2, 1, 0, 4, 3]
def added542 : List (List Vertex) := [[3, 0, 2, 6, 1, 7, 5, 4], [4, 7, 0, 5]]
theorem accepted542 : OriginalAccepted (decode 542) 2 0 0
    tail542 added542 := by decide

def tail543 : List Vertex := [6, 2, 1, 0, 4, 3]
def added543 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 6, 1], [1, 7, 0, 6]]
theorem accepted543 : OriginalAccepted (decode 543) 2 1 1
    tail543 added543 := by decide

def tail548 : List Vertex := [5, 1, 2, 0, 4, 3]
def added548 : List (List Vertex) := [[3, 0, 1, 6, 5, 4, 7, 2], [2, 5]]
theorem accepted548 : OriginalAccepted (decode 548) 0 1 0
    tail548 added548 := by decide

def tail550 : List Vertex := [5, 1, 2, 0, 4, 3]
def added550 : List (List Vertex) := [[3, 0, 1, 6, 7, 4, 5, 2], [2, 7, 0, 5]]
theorem accepted550 : OriginalAccepted (decode 550) 2 1 0
    tail550 added550 := by decide

def tail551 : List Vertex := [6, 1, 2, 0, 4, 3]
def added551 : List (List Vertex) := [[3, 0, 1, 5, 4, 7, 2], [2, 5, 7, 0, 6]]
theorem accepted551 : OriginalAccepted (decode 551) 2 0 1
    tail551 added551 := by decide

def tail552 : List Vertex := [5, 2, 1, 0, 4, 3]
def added552 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 5]]
theorem accepted552 : OriginalAccepted (decode 552) 0 2 0
    tail552 added552 := by decide

def tail553 : List Vertex := [5, 2, 1, 0, 4, 3]
def added553 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 6, 0, 5]]
theorem accepted553 : OriginalAccepted (decode 553) 1 2 0
    tail553 added553 := by decide

def tail555 : List Vertex := [7, 2, 1, 0, 4, 3]
def added555 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 1], [1, 5, 6, 0, 7]]
theorem accepted555 : OriginalAccepted (decode 555) 1 0 2
    tail555 added555 := by decide

def tail556 : List Vertex := [7, 1, 2, 0, 4, 3]
def added556 : List (List Vertex) := [[3, 0, 1, 6, 7, 4, 5, 2], [2, 7]]
theorem accepted556 : OriginalAccepted (decode 556) 2 1 2
    tail556 added556 := by decide

def tail557 : List Vertex := [6, 1, 2, 0, 4, 3]
def added557 : List (List Vertex) := [[3, 0, 1, 7, 4, 5, 2], [2, 7, 5, 0, 6]]
theorem accepted557 : OriginalAccepted (decode 557) 0 2 1
    tail557 added557 := by decide

def tail558 : List Vertex := [7, 1, 2, 0, 4, 3]
def added558 : List (List Vertex) := [[3, 0, 1, 6, 5, 4, 7, 2], [2, 5, 0, 7]]
theorem accepted558 : OriginalAccepted (decode 558) 0 1 2
    tail558 added558 := by decide

def tail565 : List Vertex := [6, 2, 1, 0, 4, 3]
def added565 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 6, 1], [1, 5, 0, 6]]
theorem accepted565 : OriginalAccepted (decode 565) 0 1 1
    tail565 added565 := by decide

def tail566 : List Vertex := [7, 2, 1, 0, 4, 3]
def added566 : List (List Vertex) := [[3, 0, 2, 6, 1, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted566 : OriginalAccepted (decode 566) 0 2 2
    tail566 added566 := by decide

def tail567 : List Vertex := [6, 1, 2, 0, 4, 3]
def added567 : List (List Vertex) := [[3, 0, 1, 5, 4, 7, 6, 2], [2, 7, 0, 6]]
theorem accepted567 : OriginalAccepted (decode 567) 2 1 1
    tail567 added567 := by decide

def tail568 : List Vertex := [7, 2, 1, 0, 4, 3]
def added568 : List (List Vertex) := [[3, 0, 2, 6, 7, 4, 5, 1], [1, 7]]
theorem accepted568 : OriginalAccepted (decode 568) 2 1 2
    tail568 added568 := by decide

def tail569 : List Vertex := [6, 2, 1, 0, 4, 3]
def added569 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 5, 0, 6]]
theorem accepted569 : OriginalAccepted (decode 569) 0 2 1
    tail569 added569 := by decide

def tail570 : List Vertex := [7, 2, 1, 0, 4, 3]
def added570 : List (List Vertex) := [[3, 0, 2, 6, 5, 4, 7, 1], [1, 5, 0, 7]]
theorem accepted570 : OriginalAccepted (decode 570) 0 1 2
    tail570 added570 := by decide

def tail572 : List Vertex := [7, 2, 1, 0, 4, 3]
def added572 : List (List Vertex) := [[3, 0, 2, 6, 1, 7, 4, 5], [7, 5]]
theorem accepted572 : OriginalAccepted (decode 572) 2 0 2
    tail572 added572 := by decide

def tail573 : List Vertex := [6, 2, 1, 0, 4, 3]
def added573 : List (List Vertex) := [[3, 0, 5, 4, 7, 6, 1], [1, 7, 2, 0, 6]]
theorem accepted573 : OriginalAccepted (decode 573) 1 2 1
    tail573 added573 := by decide

def tail575 : List Vertex := [7, 2, 1, 0, 4, 3]
def added575 : List (List Vertex) := [[3, 0, 2, 6, 1, 7, 4, 5], [7, 0, 6, 5]]
theorem accepted575 : OriginalAccepted (decode 575) 1 0 2
    tail575 added575 := by decide

def tail580 : List Vertex := [5, 4, 3, 0, 1, 2]
def added580 : List (List Vertex) := [[2, 0, 4, 7, 5, 1, 6, 3], [3, 5]]
theorem accepted580 : OriginalAccepted (decode 580) 0 2 0
    tail580 added580 := by decide

def tail581 : List Vertex := [5, 4, 3, 0, 1, 2]
def added581 : List (List Vertex) := [[2, 0, 4, 7, 6, 1, 5, 3], [3, 6, 0, 5]]
theorem accepted581 : OriginalAccepted (decode 581) 1 2 0
    tail581 added581 := by decide

def tail583 : List Vertex := [7, 4, 3, 0, 1, 2]
def added583 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 3], [3, 5, 6, 0, 7]]
theorem accepted583 : OriginalAccepted (decode 583) 1 0 2
    tail583 added583 := by decide

def tail584 : List Vertex := [5, 3, 4, 0, 1, 2]
def added584 : List (List Vertex) := [[2, 0, 3, 6, 5, 1, 7, 4], [4, 5]]
theorem accepted584 : OriginalAccepted (decode 584) 0 1 0
    tail584 added584 := by decide

def tail586 : List Vertex := [5, 3, 4, 0, 1, 2]
def added586 : List (List Vertex) := [[2, 0, 3, 6, 7, 1, 5, 4], [4, 7, 0, 5]]
theorem accepted586 : OriginalAccepted (decode 586) 2 1 0
    tail586 added586 := by decide

def tail587 : List Vertex := [6, 3, 4, 0, 1, 2]
def added587 : List (List Vertex) := [[2, 0, 3, 5, 1, 7, 4], [4, 5, 7, 0, 6]]
theorem accepted587 : OriginalAccepted (decode 587) 2 0 1
    tail587 added587 := by decide

def tail589 : List Vertex := [5, 4, 3, 0, 1, 2]
def added589 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted589 : OriginalAccepted (decode 589) 1 0 0
    tail589 added589 := by decide

def tail590 : List Vertex := [5, 3, 4, 0, 1, 2]
def added590 : List (List Vertex) := [[2, 0, 3, 6, 1, 7, 5, 4], [4, 7, 0, 5]]
theorem accepted590 : OriginalAccepted (decode 590) 2 0 0
    tail590 added590 := by decide

def tail591 : List Vertex := [7, 4, 3, 0, 1, 2]
def added591 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted591 : OriginalAccepted (decode 591) 1 2 2
    tail591 added591 := by decide

def tail592 : List Vertex := [5, 4, 3, 0, 2, 1]
def added592 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5]]
theorem accepted592 : OriginalAccepted (decode 592) 0 2 0
    tail592 added592 := by decide

def tail593 : List Vertex := [5, 4, 3, 0, 2, 1]
def added593 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6, 0, 5]]
theorem accepted593 : OriginalAccepted (decode 593) 1 2 0
    tail593 added593 := by decide

def tail595 : List Vertex := [7, 4, 3, 0, 2, 1]
def added595 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [3, 5, 6, 0, 7]]
theorem accepted595 : OriginalAccepted (decode 595) 1 0 2
    tail595 added595 := by decide

def tail596 : List Vertex := [5, 4, 3, 0, 2, 1]
def added596 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6, 1, 5]]
theorem accepted596 : OriginalAccepted (decode 596) 1 2 0
    tail596 added596 := by decide

def tail603 : List Vertex := [6, 3, 4, 0, 2, 1]
def added603 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 0, 3], [3, 5, 1, 0, 7, 6]]
theorem accepted603 : OriginalAccepted (decode 603) 2 1 1
    tail603 added603 := by decide

def tail604 : List Vertex := [5, 4, 3, 0, 1, 2]
def added604 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 4, 0], [5, 6, 2, 0]]
theorem accepted604 : OriginalAccepted (decode 604) 1 0 0
    tail604 added604 := by decide

def tail606 : List Vertex := [7, 1, 2, 0, 3, 4]
def added606 : List (List Vertex) := [[3, 5, 2, 6, 1, 0, 4, 7], [4, 5, 0, 7, 6, 3]]
theorem accepted606 : OriginalAccepted (decode 606) 2 1 2
    tail606 added606 := by decide

def tail607 : List Vertex := [7, 4, 3, 0, 2, 1]
def added607 : List (List Vertex) := [[2, 6, 3, 5, 4, 0, 1, 7], [1, 6, 0, 7, 5, 2]]
theorem accepted607 : OriginalAccepted (decode 607) 2 0 2
    tail607 added607 := by decide

def tail608 : List Vertex := [5, 3, 4, 0, 2, 1]
def added608 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5]]
theorem accepted608 : OriginalAccepted (decode 608) 0 1 0
    tail608 added608 := by decide

def tail610 : List Vertex := [5, 3, 4, 0, 2, 1]
def added610 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7, 0, 5]]
theorem accepted610 : OriginalAccepted (decode 610) 2 1 0
    tail610 added610 := by decide

def tail611 : List Vertex := [6, 3, 4, 0, 2, 1]
def added611 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 4], [4, 5, 7, 0, 6]]
theorem accepted611 : OriginalAccepted (decode 611) 2 0 1
    tail611 added611 := by decide

def tail615 : List Vertex := [7, 4, 3, 0, 2, 1]
def added615 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 0, 4], [4, 5, 1, 0, 6, 7]]
theorem accepted615 : OriginalAccepted (decode 615) 1 2 2
    tail615 added615 := by decide

def tail616 : List Vertex := [5, 3, 4, 0, 2, 1]
def added616 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7, 1, 5]]
theorem accepted616 : OriginalAccepted (decode 616) 2 1 0
    tail616 added616 := by decide

def tail620 : List Vertex := [5, 3, 4, 0, 1, 2]
def added620 : List (List Vertex) := [[2, 5, 4, 7, 1, 6, 3, 0], [5, 7, 2, 0]]
theorem accepted620 : OriginalAccepted (decode 620) 2 0 0
    tail620 added620 := by decide

def tail621 : List Vertex := [6, 1, 2, 0, 4, 3]
def added621 : List (List Vertex) := [[4, 5, 2, 7, 1, 0, 3, 6], [3, 5, 0, 6, 7, 4]]
theorem accepted621 : OriginalAccepted (decode 621) 1 2 1
    tail621 added621 := by decide

def tail623 : List Vertex := [6, 3, 4, 0, 2, 1]
def added623 : List (List Vertex) := [[2, 7, 4, 5, 3, 0, 1, 6], [1, 7, 0, 6, 5, 2]]
theorem accepted623 : OriginalAccepted (decode 623) 1 0 1
    tail623 added623 := by decide

def tail625 : List Vertex := [5, 4, 3, 0, 2, 1]
def added625 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted625 : OriginalAccepted (decode 625) 1 0 0
    tail625 added625 := by decide

def tail626 : List Vertex := [5, 3, 4, 0, 2, 1]
def added626 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 5, 4], [4, 7, 0, 5]]
theorem accepted626 : OriginalAccepted (decode 626) 2 0 0
    tail626 added626 := by decide

def tail627 : List Vertex := [7, 4, 3, 0, 2, 1]
def added627 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted627 : OriginalAccepted (decode 627) 1 2 2
    tail627 added627 := by decide

def tail628 : List Vertex := [5, 4, 3, 0, 2, 1]
def added628 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 4, 0], [5, 6, 1, 0]]
theorem accepted628 : OriginalAccepted (decode 628) 1 0 0
    tail628 added628 := by decide

def tail630 : List Vertex := [7, 2, 1, 0, 3, 4]
def added630 : List (List Vertex) := [[3, 5, 1, 6, 2, 0, 4, 7], [4, 5, 0, 7, 6, 3]]
theorem accepted630 : OriginalAccepted (decode 630) 2 1 2
    tail630 added630 := by decide

def tail631 : List Vertex := [7, 4, 3, 0, 1, 2]
def added631 : List (List Vertex) := [[1, 6, 3, 5, 4, 0, 2, 7], [2, 6, 0, 7, 5, 1]]
theorem accepted631 : OriginalAccepted (decode 631) 2 0 2
    tail631 added631 := by decide

def tail632 : List Vertex := [5, 3, 4, 0, 2, 1]
def added632 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 3, 0], [5, 7, 1, 0]]
theorem accepted632 : OriginalAccepted (decode 632) 2 0 0
    tail632 added632 := by decide

def tail633 : List Vertex := [6, 2, 1, 0, 4, 3]
def added633 : List (List Vertex) := [[4, 5, 1, 7, 2, 0, 3, 6], [3, 5, 0, 6, 7, 4]]
theorem accepted633 : OriginalAccepted (decode 633) 1 2 1
    tail633 added633 := by decide

def tail635 : List Vertex := [6, 3, 4, 0, 1, 2]
def added635 : List (List Vertex) := [[1, 7, 4, 5, 3, 0, 2, 6], [2, 7, 0, 6, 5, 1]]
theorem accepted635 : OriginalAccepted (decode 635) 1 0 1
    tail635 added635 := by decide

def tail636 : List Vertex := [7, 4, 3, 0, 2, 1]
def added636 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 4, 0], [7, 6, 1, 0]]
theorem accepted636 : OriginalAccepted (decode 636) 1 2 2
    tail636 added636 := by decide

def tail637 : List Vertex := [6, 2, 1, 0, 4, 3]
def added637 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 0, 2], [2, 7, 5, 0, 3, 6]]
theorem accepted637 : OriginalAccepted (decode 637) 0 2 1
    tail637 added637 := by decide

def tail638 : List Vertex := [7, 2, 1, 0, 3, 4]
def added638 : List (List Vertex) := [[4, 5, 3, 6, 1, 7, 0, 2], [2, 6, 5, 0, 4, 7]]
theorem accepted638 : OriginalAccepted (decode 638) 0 1 2
    tail638 added638 := by decide

def tail644 : List Vertex := [5, 4, 3, 0, 1, 2]
def added644 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 1, 6], [5, 6]]
theorem accepted644 : OriginalAccepted (decode 644) 0 1 0
    tail644 added644 := by decide

def tail646 : List Vertex := [5, 4, 3, 0, 1, 2]
def added646 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 1, 6], [5, 0, 7, 6]]
theorem accepted646 : OriginalAccepted (decode 646) 2 1 0
    tail646 added646 := by decide

def tail647 : List Vertex := [7, 4, 3, 0, 1, 2]
def added647 : List (List Vertex) := [[2, 0, 6, 1, 5, 7, 3], [3, 5, 4, 0, 7]]
theorem accepted647 : OriginalAccepted (decode 647) 2 0 2
    tail647 added647 := by decide

def tail648 : List Vertex := [5, 4, 3, 0, 1, 2]
def added648 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 5]]
theorem accepted648 : OriginalAccepted (decode 648) 0 2 0
    tail648 added648 := by decide

def tail649 : List Vertex := [5, 4, 3, 0, 1, 2]
def added649 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 6, 0, 5]]
theorem accepted649 : OriginalAccepted (decode 649) 1 2 0
    tail649 added649 := by decide

def tail651 : List Vertex := [7, 4, 3, 0, 1, 2]
def added651 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 3], [3, 5, 6, 0, 7]]
theorem accepted651 : OriginalAccepted (decode 651) 1 0 2
    tail651 added651 := by decide

def tail652 : List Vertex := [7, 4, 3, 0, 1, 2]
def added652 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 1, 6], [7, 6]]
theorem accepted652 : OriginalAccepted (decode 652) 2 1 2
    tail652 added652 := by decide

def tail653 : List Vertex := [5, 4, 3, 0, 1, 2]
def added653 : List (List Vertex) := [[2, 0, 6, 1, 7, 5, 3], [3, 7, 4, 0, 5]]
theorem accepted653 : OriginalAccepted (decode 653) 0 2 0
    tail653 added653 := by decide

def tail654 : List Vertex := [7, 4, 3, 0, 1, 2]
def added654 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 1, 6], [7, 0, 5, 6]]
theorem accepted654 : OriginalAccepted (decode 654) 0 1 2
    tail654 added654 := by decide

def tail656 : List Vertex := [5, 4, 3, 0, 2, 1]
def added656 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 2, 6], [5, 6]]
theorem accepted656 : OriginalAccepted (decode 656) 0 1 0
    tail656 added656 := by decide

def tail658 : List Vertex := [5, 4, 3, 0, 2, 1]
def added658 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 2, 6], [5, 0, 7, 6]]
theorem accepted658 : OriginalAccepted (decode 658) 2 1 0
    tail658 added658 := by decide

def tail659 : List Vertex := [7, 4, 3, 0, 2, 1]
def added659 : List (List Vertex) := [[1, 0, 6, 2, 5, 7, 3], [3, 5, 4, 0, 7]]
theorem accepted659 : OriginalAccepted (decode 659) 2 0 2
    tail659 added659 := by decide

def tail663 : List Vertex := [7, 4, 3, 0, 2, 1]
def added663 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 0, 4], [4, 5, 1, 0, 6, 7]]
theorem accepted663 : OriginalAccepted (decode 663) 1 2 2
    tail663 added663 := by decide

def tail664 : List Vertex := [5, 2, 1, 0, 4, 3]
def added664 : List (List Vertex) := [[3, 0, 2, 6, 7, 4, 5, 1], [1, 7, 3, 5]]
theorem accepted664 : OriginalAccepted (decode 664) 2 1 0
    tail664 added664 := by decide

def tail668 : List Vertex := [5, 2, 1, 0, 4, 3]
def added668 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 2, 0], [5, 7, 3, 0]]
theorem accepted668 : OriginalAccepted (decode 668) 2 0 0
    tail668 added668 := by decide

def tail669 : List Vertex := [5, 4, 3, 0, 1, 2]
def added669 : List (List Vertex) := [[2, 6, 1, 7, 3, 5, 0, 4], [4, 7, 6, 0, 2, 5]]
theorem accepted669 : OriginalAccepted (decode 669) 1 2 0
    tail669 added669 := by decide

def tail671 : List Vertex := [7, 4, 3, 0, 2, 1]
def added671 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 0, 4], [4, 5, 6, 0, 1, 7]]
theorem accepted671 : OriginalAccepted (decode 671) 1 0 2
    tail671 added671 := by decide

def tail672 : List Vertex := [5, 4, 3, 0, 2, 1]
def added672 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 5]]
theorem accepted672 : OriginalAccepted (decode 672) 0 2 0
    tail672 added672 := by decide

def tail673 : List Vertex := [5, 4, 3, 0, 2, 1]
def added673 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 6, 0, 5]]
theorem accepted673 : OriginalAccepted (decode 673) 1 2 0
    tail673 added673 := by decide

def tail675 : List Vertex := [7, 4, 3, 0, 2, 1]
def added675 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [3, 5, 6, 0, 7]]
theorem accepted675 : OriginalAccepted (decode 675) 1 0 2
    tail675 added675 := by decide

def tail676 : List Vertex := [5, 1, 2, 0, 4, 3]
def added676 : List (List Vertex) := [[3, 0, 1, 6, 7, 4, 5, 2], [2, 7, 3, 5]]
theorem accepted676 : OriginalAccepted (decode 676) 2 1 0
    tail676 added676 := by decide

def tail684 : List Vertex := [7, 1, 2, 0, 4, 3]
def added684 : List (List Vertex) := [[3, 0, 1, 6, 5, 4, 7, 2], [2, 5, 3, 7]]
theorem accepted684 : OriginalAccepted (decode 684) 0 1 2
    tail684 added684 := by decide

def tail688 : List Vertex := [7, 4, 3, 0, 2, 1]
def added688 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 2, 6], [7, 6]]
theorem accepted688 : OriginalAccepted (decode 688) 2 1 2
    tail688 added688 := by decide

def tail689 : List Vertex := [5, 4, 3, 0, 2, 1]
def added689 : List (List Vertex) := [[1, 0, 6, 2, 7, 5, 3], [3, 7, 4, 0, 5]]
theorem accepted689 : OriginalAccepted (decode 689) 0 2 0
    tail689 added689 := by decide

def tail690 : List Vertex := [7, 4, 3, 0, 2, 1]
def added690 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 2, 6], [7, 0, 5, 6]]
theorem accepted690 : OriginalAccepted (decode 690) 0 1 2
    tail690 added690 := by decide

def tail692 : List Vertex := [7, 2, 1, 0, 4, 3]
def added692 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 2, 0], [7, 5, 3, 0]]
theorem accepted692 : OriginalAccepted (decode 692) 0 2 2
    tail692 added692 := by decide

def tail693 : List Vertex := [5, 4, 3, 0, 2, 1]
def added693 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 0, 4], [4, 7, 6, 0, 1, 5]]
theorem accepted693 : OriginalAccepted (decode 693) 1 2 0
    tail693 added693 := by decide

def tail695 : List Vertex := [7, 4, 3, 0, 1, 2]
def added695 : List (List Vertex) := [[2, 6, 1, 5, 3, 7, 0, 4], [4, 5, 6, 0, 2, 7]]
theorem accepted695 : OriginalAccepted (decode 695) 1 0 2
    tail695 added695 := by decide

def tail696 : List Vertex := [7, 2, 1, 0, 4, 3]
def added696 : List (List Vertex) := [[3, 0, 2, 6, 5, 4, 7, 1], [1, 5, 3, 7]]
theorem accepted696 : OriginalAccepted (decode 696) 0 1 2
    tail696 added696 := by decide

def tail701 : List Vertex := [5, 4, 3, 0, 2, 1]
def added701 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 0, 4], [4, 7, 1, 0, 6, 5]]
theorem accepted701 : OriginalAccepted (decode 701) 1 0 0
    tail701 added701 := by decide

def tail709 : List Vertex := [5, 4, 3, 0, 1, 2]
def added709 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 5, 1], [1, 6, 0, 5]]
theorem accepted709 : OriginalAccepted (decode 709) 1 0 0
    tail709 added709 := by decide

def tail710 : List Vertex := [7, 3, 4, 0, 1, 2]
def added710 : List (List Vertex) := [[2, 0, 3, 6, 1, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted710 : OriginalAccepted (decode 710) 0 2 2
    tail710 added710 := by decide

def tail711 : List Vertex := [7, 4, 3, 0, 1, 2]
def added711 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 7, 3], [3, 6, 0, 7]]
theorem accepted711 : OriginalAccepted (decode 711) 1 2 2
    tail711 added711 := by decide

def tail712 : List Vertex := [7, 3, 4, 0, 1, 2]
def added712 : List (List Vertex) := [[2, 0, 3, 6, 7, 1, 5, 4], [4, 7]]
theorem accepted712 : OriginalAccepted (decode 712) 2 1 2
    tail712 added712 := by decide

def tail713 : List Vertex := [6, 3, 4, 0, 1, 2]
def added713 : List (List Vertex) := [[2, 0, 3, 7, 1, 5, 4], [4, 7, 5, 0, 6]]
theorem accepted713 : OriginalAccepted (decode 713) 0 2 1
    tail713 added713 := by decide

def tail714 : List Vertex := [7, 3, 4, 0, 1, 2]
def added714 : List (List Vertex) := [[2, 0, 3, 6, 5, 1, 7, 4], [4, 5, 0, 7]]
theorem accepted714 : OriginalAccepted (decode 714) 0 1 2
    tail714 added714 := by decide

def tail716 : List Vertex := [7, 4, 3, 0, 1, 2]
def added716 : List (List Vertex) := [[2, 0, 4, 5, 7, 1, 6, 3], [3, 7]]
theorem accepted716 : OriginalAccepted (decode 716) 2 0 2
    tail716 added716 := by decide

def tail717 : List Vertex := [5, 4, 3, 0, 1, 2]
def added717 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 6, 0, 5]]
theorem accepted717 : OriginalAccepted (decode 717) 1 2 0
    tail717 added717 := by decide

def tail719 : List Vertex := [7, 4, 3, 0, 1, 2]
def added719 : List (List Vertex) := [[2, 0, 4, 5, 6, 1, 7, 3], [3, 6, 0, 7]]
theorem accepted719 : OriginalAccepted (decode 719) 1 0 2
    tail719 added719 := by decide

def tail721 : List Vertex := [5, 4, 3, 0, 2, 1]
def added721 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 5, 2], [2, 6, 0, 5]]
theorem accepted721 : OriginalAccepted (decode 721) 1 0 0
    tail721 added721 := by decide

def tail722 : List Vertex := [7, 3, 4, 0, 2, 1]
def added722 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted722 : OriginalAccepted (decode 722) 0 2 2
    tail722 added722 := by decide

def tail723 : List Vertex := [7, 4, 3, 0, 2, 1]
def added723 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 7, 3], [3, 6, 0, 7]]
theorem accepted723 : OriginalAccepted (decode 723) 1 2 2
    tail723 added723 := by decide

def tail724 : List Vertex := [5, 4, 3, 0, 2, 1]
def added724 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 4, 0], [5, 6, 1, 0]]
theorem accepted724 : OriginalAccepted (decode 724) 1 0 0
    tail724 added724 := by decide

def tail726 : List Vertex := [5, 2, 1, 0, 3, 4]
def added726 : List (List Vertex) := [[4, 7, 3, 6, 1, 5, 0, 2], [2, 6, 7, 0, 4, 5]]
theorem accepted726 : OriginalAccepted (decode 726) 2 1 0
    tail726 added726 := by decide

def tail727 : List Vertex := [6, 2, 1, 0, 4, 3]
def added727 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 0, 2], [2, 5, 7, 0, 3, 6]]
theorem accepted727 : OriginalAccepted (decode 727) 2 0 1
    tail727 added727 := by decide

def tail728 : List Vertex := [7, 3, 4, 0, 2, 1]
def added728 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 3, 0], [7, 5, 1, 0]]
theorem accepted728 : OriginalAccepted (decode 728) 0 2 2
    tail728 added728 := by decide

def tail729 : List Vertex := [6, 3, 4, 0, 1, 2]
def added729 : List (List Vertex) := [[1, 5, 4, 7, 3, 0, 2, 6], [2, 5, 0, 6, 7, 1]]
theorem accepted729 : OriginalAccepted (decode 729) 1 2 1
    tail729 added729 := by decide

def tail731 : List Vertex := [6, 2, 1, 0, 4, 3]
def added731 : List (List Vertex) := [[4, 7, 1, 5, 2, 0, 3, 6], [3, 7, 0, 6, 5, 4]]
theorem accepted731 : OriginalAccepted (decode 731) 1 0 1
    tail731 added731 := by decide

def tail732 : List Vertex := [7, 4, 3, 0, 2, 1]
def added732 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 4, 0], [7, 6, 1, 0]]
theorem accepted732 : OriginalAccepted (decode 732) 1 2 2
    tail732 added732 := by decide

def tail733 : List Vertex := [5, 4, 3, 0, 1, 2]
def added733 : List (List Vertex) := [[1, 6, 3, 7, 4, 0, 2, 5], [2, 6, 0, 5, 7, 1]]
theorem accepted733 : OriginalAccepted (decode 733) 0 2 0
    tail733 added733 := by decide

def tail734 : List Vertex := [5, 2, 1, 0, 3, 4]
def added734 : List (List Vertex) := [[3, 7, 1, 6, 2, 0, 4, 5], [4, 7, 0, 5, 6, 3]]
theorem accepted734 : OriginalAccepted (decode 734) 0 1 0
    tail734 added734 := by decide

def tail736 : List Vertex := [7, 3, 4, 0, 2, 1]
def added736 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7]]
theorem accepted736 : OriginalAccepted (decode 736) 2 1 2
    tail736 added736 := by decide

def tail737 : List Vertex := [6, 3, 4, 0, 2, 1]
def added737 : List (List Vertex) := [[1, 0, 3, 7, 2, 5, 4], [4, 7, 5, 0, 6]]
theorem accepted737 : OriginalAccepted (decode 737) 0 2 1
    tail737 added737 := by decide

def tail738 : List Vertex := [7, 3, 4, 0, 2, 1]
def added738 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5, 0, 7]]
theorem accepted738 : OriginalAccepted (decode 738) 0 1 2
    tail738 added738 := by decide

def tail740 : List Vertex := [7, 3, 4, 0, 1, 2]
def added740 : List (List Vertex) := [[2, 7, 4, 5, 1, 6, 3, 0], [7, 5, 2, 0]]
theorem accepted740 : OriginalAccepted (decode 740) 0 2 2
    tail740 added740 := by decide

def tail741 : List Vertex := [6, 3, 4, 0, 2, 1]
def added741 : List (List Vertex) := [[2, 5, 4, 7, 3, 0, 1, 6], [1, 5, 0, 6, 7, 2]]
theorem accepted741 : OriginalAccepted (decode 741) 1 2 1
    tail741 added741 := by decide

def tail743 : List Vertex := [6, 1, 2, 0, 4, 3]
def added743 : List (List Vertex) := [[4, 7, 2, 5, 1, 0, 3, 6], [3, 7, 0, 6, 5, 4]]
theorem accepted743 : OriginalAccepted (decode 743) 1 0 1
    tail743 added743 := by decide

def tail744 : List Vertex := [7, 3, 4, 0, 2, 1]
def added744 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5, 1, 7]]
theorem accepted744 : OriginalAccepted (decode 744) 0 1 2
    tail744 added744 := by decide

def tail749 : List Vertex := [5, 4, 3, 0, 2, 1]
def added749 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 0, 4], [4, 7, 1, 0, 6, 5]]
theorem accepted749 : OriginalAccepted (decode 749) 1 0 0
    tail749 added749 := by decide

def tail752 : List Vertex := [7, 4, 3, 0, 2, 1]
def added752 : List (List Vertex) := [[1, 0, 4, 5, 7, 2, 6, 3], [3, 7]]
theorem accepted752 : OriginalAccepted (decode 752) 2 0 2
    tail752 added752 := by decide

def tail753 : List Vertex := [5, 4, 3, 0, 2, 1]
def added753 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 6, 0, 5]]
theorem accepted753 : OriginalAccepted (decode 753) 1 2 0
    tail753 added753 := by decide

def tail755 : List Vertex := [7, 4, 3, 0, 2, 1]
def added755 : List (List Vertex) := [[1, 0, 4, 5, 6, 2, 7, 3], [3, 6, 0, 7]]
theorem accepted755 : OriginalAccepted (decode 755) 1 0 2
    tail755 added755 := by decide

def tail756 : List Vertex := [7, 4, 3, 0, 1, 2]
def added756 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 4, 0], [7, 6, 2, 0]]
theorem accepted756 : OriginalAccepted (decode 756) 1 2 2
    tail756 added756 := by decide

def tail757 : List Vertex := [5, 4, 3, 0, 2, 1]
def added757 : List (List Vertex) := [[2, 6, 3, 7, 4, 0, 1, 5], [1, 6, 0, 5, 7, 2]]
theorem accepted757 : OriginalAccepted (decode 757) 0 2 0
    tail757 added757 := by decide

def tail758 : List Vertex := [5, 1, 2, 0, 3, 4]
def added758 : List (List Vertex) := [[3, 7, 2, 6, 1, 0, 4, 5], [4, 7, 0, 5, 6, 3]]
theorem accepted758 : OriginalAccepted (decode 758) 0 1 0
    tail758 added758 := by decide

def tail761 : List Vertex := [6, 3, 4, 0, 2, 1]
def added761 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 0, 3], [3, 7, 1, 0, 5, 6]]
theorem accepted761 : OriginalAccepted (decode 761) 0 1 1
    tail761 added761 := by decide

def tail764 : List Vertex := [7, 4, 3, 0, 2, 1]
def added764 : List (List Vertex) := [[1, 0, 4, 5, 6, 2, 7, 3], [3, 6, 1, 7]]
theorem accepted764 : OriginalAccepted (decode 764) 1 0 2
    tail764 added764 := by decide

def tail788 : List Vertex := [6, 2, 1, 0, 4, 3]
def added788 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 4, 7], [6, 7]]
theorem accepted788 : OriginalAccepted (decode 788) 1 2 1
    tail788 added788 := by decide

def tail789 : List Vertex := [6, 2, 1, 0, 4, 3]
def added789 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 4, 7], [6, 0, 5, 7]]
theorem accepted789 : OriginalAccepted (decode 789) 0 2 1
    tail789 added789 := by decide

def tail790 : List Vertex := [5, 2, 1, 0, 4, 3]
def added790 : List (List Vertex) := [[3, 0, 7, 4, 6, 5, 1], [1, 6, 2, 0, 5]]
theorem accepted790 : OriginalAccepted (decode 790) 0 1 0
    tail790 added790 := by decide

def tail793 : List Vertex := [5, 1, 2, 0, 4, 3]
def added793 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 5, 2], [2, 6, 0, 5]]
theorem accepted793 : OriginalAccepted (decode 793) 1 0 0
    tail793 added793 := by decide

def tail794 : List Vertex := [5, 2, 1, 0, 4, 3]
def added794 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 5, 1], [1, 7, 0, 5]]
theorem accepted794 : OriginalAccepted (decode 794) 2 0 0
    tail794 added794 := by decide

def tail795 : List Vertex := [6, 2, 1, 0, 4, 3]
def added795 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted795 : OriginalAccepted (decode 795) 2 1 1
    tail795 added795 := by decide

def tail796 : List Vertex := [6, 2, 1, 0, 4, 3]
def added796 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6]]
theorem accepted796 : OriginalAccepted (decode 796) 1 0 1
    tail796 added796 := by decide

def tail798 : List Vertex := [5, 2, 1, 0, 4, 3]
def added798 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [1, 6, 7, 0, 5]]
theorem accepted798 : OriginalAccepted (decode 798) 2 1 0
    tail798 added798 := by decide

def tail799 : List Vertex := [6, 2, 1, 0, 4, 3]
def added799 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7, 0, 6]]
theorem accepted799 : OriginalAccepted (decode 799) 2 0 1
    tail799 added799 := by decide

def tail805 : List Vertex := [5, 2, 1, 0, 4, 3]
def added805 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 5, 1], [1, 6, 0, 5]]
theorem accepted805 : OriginalAccepted (decode 805) 1 0 0
    tail805 added805 := by decide

def tail806 : List Vertex := [5, 1, 2, 0, 4, 3]
def added806 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 5, 2], [2, 7, 0, 5]]
theorem accepted806 : OriginalAccepted (decode 806) 2 0 0
    tail806 added806 := by decide

def tail807 : List Vertex := [7, 2, 1, 0, 4, 3]
def added807 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted807 : OriginalAccepted (decode 807) 1 2 2
    tail807 added807 := by decide

def tail808 : List Vertex := [7, 2, 1, 0, 4, 3]
def added808 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 4, 6], [7, 6]]
theorem accepted808 : OriginalAccepted (decode 808) 2 1 2
    tail808 added808 := by decide

def tail809 : List Vertex := [5, 2, 1, 0, 4, 3]
def added809 : List (List Vertex) := [[3, 0, 6, 4, 7, 5, 1], [1, 7, 2, 0, 5]]
theorem accepted809 : OriginalAccepted (decode 809) 0 2 0
    tail809 added809 := by decide

def tail810 : List Vertex := [7, 2, 1, 0, 4, 3]
def added810 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 4, 6], [7, 0, 5, 6]]
theorem accepted810 : OriginalAccepted (decode 810) 0 1 2
    tail810 added810 := by decide

def tail812 : List Vertex := [7, 2, 1, 0, 4, 3]
def added812 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7]]
theorem accepted812 : OriginalAccepted (decode 812) 2 0 2
    tail812 added812 := by decide

def tail813 : List Vertex := [5, 2, 1, 0, 4, 3]
def added813 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 6, 0, 5]]
theorem accepted813 : OriginalAccepted (decode 813) 1 2 0
    tail813 added813 := by decide

def tail815 : List Vertex := [7, 2, 1, 0, 4, 3]
def added815 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6, 0, 7]]
theorem accepted815 : OriginalAccepted (decode 815) 1 0 2
    tail815 added815 := by decide

def tail820 : List Vertex := [6, 1, 2, 0, 4, 3]
def added820 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6]]
theorem accepted820 : OriginalAccepted (decode 820) 1 0 1
    tail820 added820 := by decide

def tail822 : List Vertex := [5, 1, 2, 0, 4, 3]
def added822 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 2], [2, 6, 7, 0, 5]]
theorem accepted822 : OriginalAccepted (decode 822) 2 1 0
    tail822 added822 := by decide

def tail823 : List Vertex := [6, 1, 2, 0, 4, 3]
def added823 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7, 0, 6]]
theorem accepted823 : OriginalAccepted (decode 823) 2 0 1
    tail823 added823 := by decide

def tail824 : List Vertex := [7, 1, 2, 0, 4, 3]
def added824 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7]]
theorem accepted824 : OriginalAccepted (decode 824) 2 0 2
    tail824 added824 := by decide

def tail825 : List Vertex := [5, 1, 2, 0, 4, 3]
def added825 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 2], [2, 7, 6, 0, 5]]
theorem accepted825 : OriginalAccepted (decode 825) 1 2 0
    tail825 added825 := by decide

def tail827 : List Vertex := [7, 1, 2, 0, 4, 3]
def added827 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6, 0, 7]]
theorem accepted827 : OriginalAccepted (decode 827) 1 0 2
    tail827 added827 := by decide

def tail828 : List Vertex := [6, 2, 1, 0, 4, 3]
def added828 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 6]]
theorem accepted828 : OriginalAccepted (decode 828) 1 2 1
    tail828 added828 := by decide

def tail829 : List Vertex := [6, 2, 1, 0, 4, 3]
def added829 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 5, 0, 6]]
theorem accepted829 : OriginalAccepted (decode 829) 0 2 1
    tail829 added829 := by decide

def tail830 : List Vertex := [7, 2, 1, 0, 4, 3]
def added830 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [1, 6, 5, 0, 7]]
theorem accepted830 : OriginalAccepted (decode 830) 0 1 2
    tail830 added830 := by decide

def tail836 : List Vertex := [6, 4, 3, 0, 1, 2]
def added836 : List (List Vertex) := [[2, 0, 4, 7, 6, 1, 5, 3], [3, 6]]
theorem accepted836 : OriginalAccepted (decode 836) 1 2 1
    tail836 added836 := by decide

def tail837 : List Vertex := [6, 4, 3, 0, 1, 2]
def added837 : List (List Vertex) := [[2, 0, 4, 7, 5, 1, 6, 3], [3, 5, 0, 6]]
theorem accepted837 : OriginalAccepted (decode 837) 0 2 1
    tail837 added837 := by decide

def tail838 : List Vertex := [7, 4, 3, 0, 1, 2]
def added838 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 5, 0, 7]]
theorem accepted838 : OriginalAccepted (decode 838) 0 1 2
    tail838 added838 := by decide

def tail841 : List Vertex := [6, 4, 3, 0, 1, 2]
def added841 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted841 : OriginalAccepted (decode 841) 0 1 1
    tail841 added841 := by decide

def tail842 : List Vertex := [7, 4, 3, 0, 1, 2]
def added842 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted842 : OriginalAccepted (decode 842) 0 2 2
    tail842 added842 := by decide

def tail843 : List Vertex := [6, 3, 4, 0, 1, 2]
def added843 : List (List Vertex) := [[2, 0, 3, 5, 1, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted843 : OriginalAccepted (decode 843) 2 1 1
    tail843 added843 := by decide

def tail844 : List Vertex := [6, 3, 4, 0, 1, 2]
def added844 : List (List Vertex) := [[2, 0, 3, 5, 6, 1, 7, 4], [4, 6]]
theorem accepted844 : OriginalAccepted (decode 844) 1 0 1
    tail844 added844 := by decide

def tail846 : List Vertex := [5, 3, 4, 0, 1, 2]
def added846 : List (List Vertex) := [[2, 0, 3, 6, 1, 7, 4], [4, 6, 7, 0, 5]]
theorem accepted846 : OriginalAccepted (decode 846) 2 1 0
    tail846 added846 := by decide

def tail847 : List Vertex := [6, 3, 4, 0, 1, 2]
def added847 : List (List Vertex) := [[2, 0, 3, 5, 7, 1, 6, 4], [4, 7, 0, 6]]
theorem accepted847 : OriginalAccepted (decode 847) 2 0 1
    tail847 added847 := by decide

def tail848 : List Vertex := [6, 4, 3, 0, 2, 1]
def added848 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6]]
theorem accepted848 : OriginalAccepted (decode 848) 1 2 1
    tail848 added848 := by decide

def tail849 : List Vertex := [6, 4, 3, 0, 2, 1]
def added849 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5, 0, 6]]
theorem accepted849 : OriginalAccepted (decode 849) 0 2 1
    tail849 added849 := by decide

def tail850 : List Vertex := [7, 4, 3, 0, 2, 1]
def added850 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 5, 0, 7]]
theorem accepted850 : OriginalAccepted (decode 850) 0 1 2
    tail850 added850 := by decide

def tail852 : List Vertex := [6, 4, 3, 0, 2, 1]
def added852 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5, 1, 6]]
theorem accepted852 : OriginalAccepted (decode 852) 0 2 1
    tail852 added852 := by decide

def tail856 : List Vertex := [6, 4, 3, 0, 1, 2]
def added856 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 4, 0], [6, 5, 2, 0]]
theorem accepted856 : OriginalAccepted (decode 856) 0 1 1
    tail856 added856 := by decide

def tail858 : List Vertex := [7, 4, 3, 0, 2, 1]
def added858 : List (List Vertex) := [[2, 5, 3, 6, 4, 0, 1, 7], [1, 5, 0, 7, 6, 2]]
theorem accepted858 : OriginalAccepted (decode 858) 2 1 2
    tail858 added858 := by decide

def tail859 : List Vertex := [7, 1, 2, 0, 3, 4]
def added859 : List (List Vertex) := [[3, 6, 2, 5, 1, 0, 4, 7], [4, 6, 0, 7, 5, 3]]
theorem accepted859 : OriginalAccepted (decode 859) 2 0 2
    tail859 added859 := by decide

def tail862 : List Vertex := [5, 3, 4, 0, 2, 1]
def added862 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 0, 3], [3, 6, 1, 0, 7, 5]]
theorem accepted862 : OriginalAccepted (decode 862) 2 0 0
    tail862 added862 := by decide

def tail865 : List Vertex := [6, 4, 3, 0, 2, 1]
def added865 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted865 : OriginalAccepted (decode 865) 0 1 1
    tail865 added865 := by decide

def tail866 : List Vertex := [7, 4, 3, 0, 2, 1]
def added866 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted866 : OriginalAccepted (decode 866) 0 2 2
    tail866 added866 := by decide

def tail867 : List Vertex := [6, 3, 4, 0, 2, 1]
def added867 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted867 : OriginalAccepted (decode 867) 2 1 1
    tail867 added867 := by decide

def tail868 : List Vertex := [6, 4, 3, 0, 2, 1]
def added868 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 4, 0], [6, 5, 1, 0]]
theorem accepted868 : OriginalAccepted (decode 868) 0 1 1
    tail868 added868 := by decide

def tail870 : List Vertex := [7, 4, 3, 0, 1, 2]
def added870 : List (List Vertex) := [[1, 5, 3, 6, 4, 0, 2, 7], [2, 5, 0, 7, 6, 1]]
theorem accepted870 : OriginalAccepted (decode 870) 2 1 2
    tail870 added870 := by decide

def tail871 : List Vertex := [7, 2, 1, 0, 3, 4]
def added871 : List (List Vertex) := [[3, 6, 1, 5, 2, 0, 4, 7], [4, 6, 0, 7, 5, 3]]
theorem accepted871 : OriginalAccepted (decode 871) 2 0 2
    tail871 added871 := by decide

def tail872 : List Vertex := [7, 4, 3, 0, 2, 1]
def added872 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 4, 0], [7, 5, 1, 0]]
theorem accepted872 : OriginalAccepted (decode 872) 0 2 2
    tail872 added872 := by decide

def tail873 : List Vertex := [5, 2, 1, 0, 4, 3]
def added873 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 0, 2], [2, 7, 6, 0, 3, 5]]
theorem accepted873 : OriginalAccepted (decode 873) 1 2 0
    tail873 added873 := by decide

def tail875 : List Vertex := [7, 2, 1, 0, 3, 4]
def added875 : List (List Vertex) := [[4, 6, 3, 5, 1, 7, 0, 2], [2, 5, 6, 0, 4, 7]]
theorem accepted875 : OriginalAccepted (decode 875) 1 0 2
    tail875 added875 := by decide

def tail876 : List Vertex := [6, 3, 4, 0, 2, 1]
def added876 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 3, 0], [6, 7, 1, 0]]
theorem accepted876 : OriginalAccepted (decode 876) 2 1 1
    tail876 added876 := by decide

def tail877 : List Vertex := [5, 2, 1, 0, 4, 3]
def added877 : List (List Vertex) := [[4, 6, 1, 7, 2, 0, 3, 5], [3, 6, 0, 5, 7, 4]]
theorem accepted877 : OriginalAccepted (decode 877) 0 2 0
    tail877 added877 := by decide

def tail878 : List Vertex := [5, 3, 4, 0, 1, 2]
def added878 : List (List Vertex) := [[1, 7, 4, 6, 3, 0, 2, 5], [2, 7, 0, 5, 6, 1]]
theorem accepted878 : OriginalAccepted (decode 878) 0 1 0
    tail878 added878 := by decide

def tail880 : List Vertex := [6, 3, 4, 0, 2, 1]
def added880 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6]]
theorem accepted880 : OriginalAccepted (decode 880) 1 0 1
    tail880 added880 := by decide

def tail882 : List Vertex := [5, 3, 4, 0, 2, 1]
def added882 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 4], [4, 6, 7, 0, 5]]
theorem accepted882 : OriginalAccepted (decode 882) 2 1 0
    tail882 added882 := by decide

def tail883 : List Vertex := [6, 3, 4, 0, 2, 1]
def added883 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7, 0, 6]]
theorem accepted883 : OriginalAccepted (decode 883) 2 0 1
    tail883 added883 := by decide

def tail886 : List Vertex := [7, 4, 3, 0, 2, 1]
def added886 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 0, 4], [4, 6, 1, 0, 5, 7]]
theorem accepted886 : OriginalAccepted (decode 886) 0 2 2
    tail886 added886 := by decide

def tail888 : List Vertex := [6, 3, 4, 0, 1, 2]
def added888 : List (List Vertex) := [[2, 6, 4, 7, 1, 5, 3, 0], [6, 7, 2, 0]]
theorem accepted888 : OriginalAccepted (decode 888) 2 1 1
    tail888 added888 := by decide

def tail889 : List Vertex := [5, 1, 2, 0, 4, 3]
def added889 : List (List Vertex) := [[4, 6, 2, 7, 1, 0, 3, 5], [3, 6, 0, 5, 7, 4]]
theorem accepted889 : OriginalAccepted (decode 889) 0 2 0
    tail889 added889 := by decide

def tail890 : List Vertex := [5, 3, 4, 0, 2, 1]
def added890 : List (List Vertex) := [[2, 7, 4, 6, 3, 0, 1, 5], [1, 7, 0, 5, 6, 2]]
theorem accepted890 : OriginalAccepted (decode 890) 0 1 0
    tail890 added890 := by decide

def tail892 : List Vertex := [6, 3, 4, 0, 2, 1]
def added892 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7, 1, 6]]
theorem accepted892 : OriginalAccepted (decode 892) 2 0 1
    tail892 added892 := by decide

def tail901 : List Vertex := [6, 4, 3, 0, 1, 2]
def added901 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 6, 1], [1, 5, 0, 6]]
theorem accepted901 : OriginalAccepted (decode 901) 0 1 1
    tail901 added901 := by decide

def tail902 : List Vertex := [7, 4, 3, 0, 1, 2]
def added902 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 7, 3], [3, 5, 0, 7]]
theorem accepted902 : OriginalAccepted (decode 902) 0 2 2
    tail902 added902 := by decide

def tail903 : List Vertex := [7, 3, 4, 0, 1, 2]
def added903 : List (List Vertex) := [[2, 0, 3, 5, 1, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted903 : OriginalAccepted (decode 903) 1 2 2
    tail903 added903 := by decide

def tail904 : List Vertex := [7, 4, 3, 0, 1, 2]
def added904 : List (List Vertex) := [[2, 0, 4, 6, 7, 1, 5, 3], [3, 7]]
theorem accepted904 : OriginalAccepted (decode 904) 2 1 2
    tail904 added904 := by decide

def tail905 : List Vertex := [6, 4, 3, 0, 1, 2]
def added905 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 5, 0, 6]]
theorem accepted905 : OriginalAccepted (decode 905) 0 2 1
    tail905 added905 := by decide

def tail906 : List Vertex := [7, 4, 3, 0, 1, 2]
def added906 : List (List Vertex) := [[2, 0, 4, 6, 5, 1, 7, 3], [3, 5, 0, 7]]
theorem accepted906 : OriginalAccepted (decode 906) 0 1 2
    tail906 added906 := by decide

def tail908 : List Vertex := [7, 3, 4, 0, 1, 2]
def added908 : List (List Vertex) := [[2, 0, 3, 5, 7, 1, 6, 4], [4, 7]]
theorem accepted908 : OriginalAccepted (decode 908) 2 0 2
    tail908 added908 := by decide

def tail909 : List Vertex := [5, 3, 4, 0, 1, 2]
def added909 : List (List Vertex) := [[2, 0, 3, 7, 1, 6, 4], [4, 7, 6, 0, 5]]
theorem accepted909 : OriginalAccepted (decode 909) 1 2 0
    tail909 added909 := by decide

def tail911 : List Vertex := [7, 3, 4, 0, 1, 2]
def added911 : List (List Vertex) := [[2, 0, 3, 5, 6, 1, 7, 4], [4, 6, 0, 7]]
theorem accepted911 : OriginalAccepted (decode 911) 1 0 2
    tail911 added911 := by decide

def tail913 : List Vertex := [6, 4, 3, 0, 2, 1]
def added913 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 6, 2], [2, 5, 0, 6]]
theorem accepted913 : OriginalAccepted (decode 913) 0 1 1
    tail913 added913 := by decide

def tail914 : List Vertex := [7, 4, 3, 0, 2, 1]
def added914 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 7, 3], [3, 5, 0, 7]]
theorem accepted914 : OriginalAccepted (decode 914) 0 2 2
    tail914 added914 := by decide

def tail915 : List Vertex := [7, 3, 4, 0, 2, 1]
def added915 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted915 : OriginalAccepted (decode 915) 1 2 2
    tail915 added915 := by decide

def tail916 : List Vertex := [6, 4, 3, 0, 2, 1]
def added916 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 4, 0], [6, 5, 1, 0]]
theorem accepted916 : OriginalAccepted (decode 916) 0 1 1
    tail916 added916 := by decide

def tail918 : List Vertex := [5, 2, 1, 0, 4, 3]
def added918 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 0, 2], [2, 6, 7, 0, 3, 5]]
theorem accepted918 : OriginalAccepted (decode 918) 2 1 0
    tail918 added918 := by decide

def tail919 : List Vertex := [6, 2, 1, 0, 3, 4]
def added919 : List (List Vertex) := [[4, 7, 3, 5, 1, 6, 0, 2], [2, 5, 7, 0, 4, 6]]
theorem accepted919 : OriginalAccepted (decode 919) 2 0 1
    tail919 added919 := by decide

def tail920 : List Vertex := [7, 4, 3, 0, 2, 1]
def added920 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 4, 0], [7, 5, 1, 0]]
theorem accepted920 : OriginalAccepted (decode 920) 0 2 2
    tail920 added920 := by decide

def tail921 : List Vertex := [6, 4, 3, 0, 1, 2]
def added921 : List (List Vertex) := [[1, 5, 3, 7, 4, 0, 2, 6], [2, 5, 0, 6, 7, 1]]
theorem accepted921 : OriginalAccepted (decode 921) 1 2 1
    tail921 added921 := by decide

def tail923 : List Vertex := [6, 2, 1, 0, 3, 4]
def added923 : List (List Vertex) := [[3, 7, 1, 5, 2, 0, 4, 6], [4, 7, 0, 6, 5, 3]]
theorem accepted923 : OriginalAccepted (decode 923) 1 0 1
    tail923 added923 := by decide

def tail924 : List Vertex := [7, 3, 4, 0, 2, 1]
def added924 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 3, 0], [7, 6, 1, 0]]
theorem accepted924 : OriginalAccepted (decode 924) 1 2 2
    tail924 added924 := by decide

def tail925 : List Vertex := [5, 3, 4, 0, 1, 2]
def added925 : List (List Vertex) := [[1, 6, 4, 7, 3, 0, 2, 5], [2, 6, 0, 5, 7, 1]]
theorem accepted925 : OriginalAccepted (decode 925) 0 2 0
    tail925 added925 := by decide

def tail926 : List Vertex := [5, 2, 1, 0, 4, 3]
def added926 : List (List Vertex) := [[4, 7, 1, 6, 2, 0, 3, 5], [3, 7, 0, 5, 6, 4]]
theorem accepted926 : OriginalAccepted (decode 926) 0 1 0
    tail926 added926 := by decide

def tail928 : List Vertex := [7, 4, 3, 0, 2, 1]
def added928 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7]]
theorem accepted928 : OriginalAccepted (decode 928) 2 1 2
    tail928 added928 := by decide

def tail929 : List Vertex := [6, 4, 3, 0, 2, 1]
def added929 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 5, 0, 6]]
theorem accepted929 : OriginalAccepted (decode 929) 0 2 1
    tail929 added929 := by decide

def tail930 : List Vertex := [7, 4, 3, 0, 2, 1]
def added930 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5, 0, 7]]
theorem accepted930 : OriginalAccepted (decode 930) 0 1 2
    tail930 added930 := by decide

def tail932 : List Vertex := [7, 4, 3, 0, 1, 2]
def added932 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 4, 0], [7, 5, 2, 0]]
theorem accepted932 : OriginalAccepted (decode 932) 0 2 2
    tail932 added932 := by decide

def tail933 : List Vertex := [6, 4, 3, 0, 2, 1]
def added933 : List (List Vertex) := [[2, 5, 3, 7, 4, 0, 1, 6], [1, 5, 0, 6, 7, 2]]
theorem accepted933 : OriginalAccepted (decode 933) 1 2 1
    tail933 added933 := by decide

def tail935 : List Vertex := [6, 1, 2, 0, 3, 4]
def added935 : List (List Vertex) := [[3, 7, 2, 5, 1, 0, 4, 6], [4, 7, 0, 6, 5, 3]]
theorem accepted935 : OriginalAccepted (decode 935) 1 0 1
    tail935 added935 := by decide

def tail936 : List Vertex := [7, 4, 3, 0, 2, 1]
def added936 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5, 1, 7]]
theorem accepted936 : OriginalAccepted (decode 936) 0 1 2
    tail936 added936 := by decide

def tail941 : List Vertex := [5, 3, 4, 0, 2, 1]
def added941 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 0, 3], [3, 7, 1, 0, 6, 5]]
theorem accepted941 : OriginalAccepted (decode 941) 1 0 0
    tail941 added941 := by decide

def tail944 : List Vertex := [7, 3, 4, 0, 2, 1]
def added944 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7]]
theorem accepted944 : OriginalAccepted (decode 944) 2 0 2
    tail944 added944 := by decide

def tail945 : List Vertex := [5, 3, 4, 0, 2, 1]
def added945 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 4], [4, 7, 6, 0, 5]]
theorem accepted945 : OriginalAccepted (decode 945) 1 2 0
    tail945 added945 := by decide

def tail947 : List Vertex := [7, 3, 4, 0, 2, 1]
def added947 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6, 0, 7]]
theorem accepted947 : OriginalAccepted (decode 947) 1 0 2
    tail947 added947 := by decide

def tail948 : List Vertex := [7, 3, 4, 0, 1, 2]
def added948 : List (List Vertex) := [[2, 7, 4, 6, 1, 5, 3, 0], [7, 6, 2, 0]]
theorem accepted948 : OriginalAccepted (decode 948) 1 2 2
    tail948 added948 := by decide

def tail949 : List Vertex := [5, 3, 4, 0, 2, 1]
def added949 : List (List Vertex) := [[2, 6, 4, 7, 3, 0, 1, 5], [1, 6, 0, 5, 7, 2]]
theorem accepted949 : OriginalAccepted (decode 949) 0 2 0
    tail949 added949 := by decide

def tail950 : List Vertex := [5, 1, 2, 0, 4, 3]
def added950 : List (List Vertex) := [[4, 7, 2, 6, 1, 0, 3, 5], [3, 7, 0, 5, 6, 4]]
theorem accepted950 : OriginalAccepted (decode 950) 0 1 0
    tail950 added950 := by decide

def tail953 : List Vertex := [6, 4, 3, 0, 2, 1]
def added953 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 0, 4], [4, 7, 1, 0, 5, 6]]
theorem accepted953 : OriginalAccepted (decode 953) 0 1 1
    tail953 added953 := by decide

def tail956 : List Vertex := [7, 3, 4, 0, 2, 1]
def added956 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6, 1, 7]]
theorem accepted956 : OriginalAccepted (decode 956) 1 0 2
    tail956 added956 := by decide

def tail964 : List Vertex := [6, 4, 3, 0, 1, 2]
def added964 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 1, 5], [6, 5]]
theorem accepted964 : OriginalAccepted (decode 964) 1 0 1
    tail964 added964 := by decide

def tail966 : List Vertex := [7, 4, 3, 0, 1, 2]
def added966 : List (List Vertex) := [[2, 0, 5, 1, 6, 7, 3], [3, 6, 4, 0, 7]]
theorem accepted966 : OriginalAccepted (decode 966) 2 1 2
    tail966 added966 := by decide

def tail967 : List Vertex := [6, 4, 3, 0, 1, 2]
def added967 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 1, 5], [6, 0, 7, 5]]
theorem accepted967 : OriginalAccepted (decode 967) 2 0 1
    tail967 added967 := by decide

def tail968 : List Vertex := [7, 4, 3, 0, 1, 2]
def added968 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 1, 5], [7, 5]]
theorem accepted968 : OriginalAccepted (decode 968) 2 0 2
    tail968 added968 := by decide

def tail969 : List Vertex := [6, 4, 3, 0, 1, 2]
def added969 : List (List Vertex) := [[2, 0, 5, 1, 7, 6, 3], [3, 7, 4, 0, 6]]
theorem accepted969 : OriginalAccepted (decode 969) 1 2 1
    tail969 added969 := by decide

def tail971 : List Vertex := [7, 4, 3, 0, 1, 2]
def added971 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 1, 5], [7, 0, 6, 5]]
theorem accepted971 : OriginalAccepted (decode 971) 1 0 2
    tail971 added971 := by decide

def tail972 : List Vertex := [6, 4, 3, 0, 1, 2]
def added972 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 6]]
theorem accepted972 : OriginalAccepted (decode 972) 1 2 1
    tail972 added972 := by decide

def tail973 : List Vertex := [6, 4, 3, 0, 1, 2]
def added973 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 5, 0, 6]]
theorem accepted973 : OriginalAccepted (decode 973) 0 2 1
    tail973 added973 := by decide

def tail974 : List Vertex := [7, 4, 3, 0, 1, 2]
def added974 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 3], [3, 6, 5, 0, 7]]
theorem accepted974 : OriginalAccepted (decode 974) 0 1 2
    tail974 added974 := by decide

def tail976 : List Vertex := [6, 4, 3, 0, 2, 1]
def added976 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 2, 5], [6, 5]]
theorem accepted976 : OriginalAccepted (decode 976) 1 0 1
    tail976 added976 := by decide

def tail978 : List Vertex := [7, 4, 3, 0, 2, 1]
def added978 : List (List Vertex) := [[1, 0, 5, 2, 6, 7, 3], [3, 6, 4, 0, 7]]
theorem accepted978 : OriginalAccepted (decode 978) 2 1 2
    tail978 added978 := by decide

def tail979 : List Vertex := [6, 4, 3, 0, 2, 1]
def added979 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 2, 5], [6, 0, 7, 5]]
theorem accepted979 : OriginalAccepted (decode 979) 2 0 1
    tail979 added979 := by decide

def tail982 : List Vertex := [7, 4, 3, 0, 2, 1]
def added982 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 0, 4], [4, 6, 1, 0, 5, 7]]
theorem accepted982 : OriginalAccepted (decode 982) 0 2 2
    tail982 added982 := by decide

def tail984 : List Vertex := [6, 2, 1, 0, 4, 3]
def added984 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 2, 0], [6, 7, 3, 0]]
theorem accepted984 : OriginalAccepted (decode 984) 2 1 1
    tail984 added984 := by decide

def tail985 : List Vertex := [6, 4, 3, 0, 1, 2]
def added985 : List (List Vertex) := [[2, 5, 1, 7, 3, 6, 0, 4], [4, 7, 5, 0, 2, 6]]
theorem accepted985 : OriginalAccepted (decode 985) 0 2 1
    tail985 added985 := by decide

def tail986 : List Vertex := [7, 4, 3, 0, 2, 1]
def added986 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 0, 4], [4, 6, 5, 0, 1, 7]]
theorem accepted986 : OriginalAccepted (decode 986) 0 1 2
    tail986 added986 := by decide

def tail988 : List Vertex := [6, 2, 1, 0, 4, 3]
def added988 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7, 3, 6]]
theorem accepted988 : OriginalAccepted (decode 988) 2 0 1
    tail988 added988 := by decide

def tail992 : List Vertex := [7, 4, 3, 0, 2, 1]
def added992 : List (List Vertex) := [[1, 0, 4, 6, 3, 7, 2, 5], [7, 5]]
theorem accepted992 : OriginalAccepted (decode 992) 2 0 2
    tail992 added992 := by decide

def tail993 : List Vertex := [6, 4, 3, 0, 2, 1]
def added993 : List (List Vertex) := [[1, 0, 5, 2, 7, 6, 3], [3, 7, 4, 0, 6]]
theorem accepted993 : OriginalAccepted (decode 993) 1 2 1
    tail993 added993 := by decide

def tail995 : List Vertex := [7, 4, 3, 0, 2, 1]
def added995 : List (List Vertex) := [[1, 0, 4, 6, 3, 7, 2, 5], [7, 0, 6, 5]]
theorem accepted995 : OriginalAccepted (decode 995) 1 0 2
    tail995 added995 := by decide

def tail996 : List Vertex := [7, 2, 1, 0, 4, 3]
def added996 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 2, 0], [7, 6, 3, 0]]
theorem accepted996 : OriginalAccepted (decode 996) 1 2 2
    tail996 added996 := by decide

def tail997 : List Vertex := [6, 4, 3, 0, 2, 1]
def added997 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 0, 4], [4, 7, 5, 0, 1, 6]]
theorem accepted997 : OriginalAccepted (decode 997) 0 2 1
    tail997 added997 := by decide

def tail998 : List Vertex := [7, 4, 3, 0, 1, 2]
def added998 : List (List Vertex) := [[2, 5, 1, 6, 3, 7, 0, 4], [4, 6, 5, 0, 2, 7]]
theorem accepted998 : OriginalAccepted (decode 998) 0 1 2
    tail998 added998 := by decide

def tail1001 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1001 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 0, 4], [4, 7, 1, 0, 5, 6]]
theorem accepted1001 : OriginalAccepted (decode 1001) 0 1 1
    tail1001 added1001 := by decide

def tail1004 : List Vertex := [7, 2, 1, 0, 4, 3]
def added1004 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6, 3, 7]]
theorem accepted1004 : OriginalAccepted (decode 1004) 1 0 2
    tail1004 added1004 := by decide

def tail1008 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1008 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 6]]
theorem accepted1008 : OriginalAccepted (decode 1008) 1 2 1
    tail1008 added1008 := by decide

def tail1009 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1009 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 5, 0, 6]]
theorem accepted1009 : OriginalAccepted (decode 1009) 0 2 1
    tail1009 added1009 := by decide

def tail1010 : List Vertex := [7, 4, 3, 0, 2, 1]
def added1010 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 3], [3, 6, 5, 0, 7]]
theorem accepted1010 : OriginalAccepted (decode 1010) 0 1 2
    tail1010 added1010 := by decide

def tail1012 : List Vertex := [6, 1, 2, 0, 4, 3]
def added1012 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7, 3, 6]]
theorem accepted1012 : OriginalAccepted (decode 1012) 2 0 1
    tail1012 added1012 := by decide

def tail1016 : List Vertex := [7, 1, 2, 0, 4, 3]
def added1016 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6, 3, 7]]
theorem accepted1016 : OriginalAccepted (decode 1016) 1 0 2
    tail1016 added1016 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
