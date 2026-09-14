/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.Orbits
