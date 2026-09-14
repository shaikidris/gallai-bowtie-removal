/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
