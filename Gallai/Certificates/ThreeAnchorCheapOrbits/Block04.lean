/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.CheapOrbits
