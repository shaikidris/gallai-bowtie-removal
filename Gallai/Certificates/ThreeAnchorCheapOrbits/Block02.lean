/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.CheapOrbits
