/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.CheapOrbits
