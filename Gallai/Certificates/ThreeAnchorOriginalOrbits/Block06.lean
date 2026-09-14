/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

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

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
