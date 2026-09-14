/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.Orbits
