/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
