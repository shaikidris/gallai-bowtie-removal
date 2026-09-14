/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.CheapOrbits
