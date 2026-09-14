/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector481 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added481 : List (List Vertex) := [[2, 7, 3, 0, 5, 4, 6], [2, 0, 6]]
theorem accepted481 : SyntheticAccepted (decode 481) 0 1
    connector481 added481 := by decide

def connector482 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added482 : List (List Vertex) := [[2, 5, 0, 4, 6, 3, 7], [2, 0, 7]]
theorem accepted482 : SyntheticAccepted (decode 482) 2 0
    connector482 added482 := by decide

def connector483 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added483 : List (List Vertex) := [[2, 5, 4, 0, 7, 3, 6], [2, 0, 6]]
theorem accepted483 : SyntheticAccepted (decode 483) 2 1
    connector483 added483 := by decide

def connector484 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added484 : List (List Vertex) := [[1, 6, 4, 5, 2, 7, 3, 0], [1, 0]]
theorem accepted484 : SyntheticAccepted (decode 484) 0 1
    connector484 added484 := by decide

def connector486 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added486 : List (List Vertex) := [[1, 6, 4, 5, 2, 0, 3, 7], [1, 5, 0, 7]]
theorem accepted486 : SyntheticAccepted (decode 486) 2 1
    connector486 added486 := by decide

def connector487 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added487 : List (List Vertex) := [[4, 5, 1, 6, 3, 0, 2, 7], [4, 6, 0, 7]]
theorem accepted487 : SyntheticAccepted (decode 487) 2 0
    connector487 added487 := by decide

def connector488 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added488 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted488 : SyntheticAccepted (decode 488) 2 0
    connector488 added488 := by decide

def connector489 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added489 : List (List Vertex) := [[4, 5, 1, 7, 3, 6, 0, 2], [4, 0, 5, 2]]
theorem accepted489 : SyntheticAccepted (decode 489) 1 2
    connector489 added489 := by decide

def connector491 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added491 : List (List Vertex) := [[3, 7, 1, 5, 4, 6, 0, 2], [3, 0, 7, 2]]
theorem accepted491 : SyntheticAccepted (decode 491) 1 0
    connector491 added491 := by decide

def connector492 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added492 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 4, 0], [1, 0]]
theorem accepted492 : SyntheticAccepted (decode 492) 2 1
    connector492 added492 := by decide

def connector493 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added493 : List (List Vertex) := [[3, 7, 1, 6, 4, 0, 2, 5], [3, 6, 0, 5]]
theorem accepted493 : SyntheticAccepted (decode 493) 0 2
    connector493 added493 := by decide

def connector494 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added494 : List (List Vertex) := [[1, 6, 3, 7, 2, 0, 4, 5], [1, 7, 0, 5]]
theorem accepted494 : SyntheticAccepted (decode 494) 0 1
    connector494 added494 := by decide

def connector496 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added496 : List (List Vertex) := [[2, 7, 3, 6, 4, 0], [2, 0]]
theorem accepted496 : SyntheticAccepted (decode 496) 1 0
    connector496 added496 := by decide

def connector498 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added498 : List (List Vertex) := [[2, 6, 3, 7, 0, 4, 5], [2, 0, 5]]
theorem accepted498 : SyntheticAccepted (decode 498) 2 1
    connector498 added498 := by decide

def connector499 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added499 : List (List Vertex) := [[2, 6, 3, 7, 0, 4], [2, 0, 6, 4]]
theorem accepted499 : SyntheticAccepted (decode 499) 2 0
    connector499 added499 := by decide

def connector502 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added502 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 4], [1, 0, 3, 6, 4]]
theorem accepted502 : SyntheticAccepted (decode 502) 0 2
    connector502 added502 := by decide

def connector504 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added504 : List (List Vertex) := [[2, 6, 3, 7, 1, 5, 4, 0], [2, 0]]
theorem accepted504 : SyntheticAccepted (decode 504) 2 1
    connector504 added504 := by decide

def connector505 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added505 : List (List Vertex) := [[3, 7, 2, 6, 4, 0, 1, 5], [3, 6, 0, 5]]
theorem accepted505 : SyntheticAccepted (decode 505) 0 2
    connector505 added505 := by decide

def connector506 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added506 : List (List Vertex) := [[2, 6, 3, 7, 1, 0, 4, 5], [2, 7, 0, 5]]
theorem accepted506 : SyntheticAccepted (decode 506) 0 1
    connector506 added506 := by decide

def connector508 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added508 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 3], [1, 6, 3]]
theorem accepted508 : SyntheticAccepted (decode 508) 2 0
    connector508 added508 := by decide

def connector532 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added532 : List (List Vertex) := [[4, 5, 2, 6, 1, 0], [4, 0]]
theorem accepted532 : SyntheticAccepted (decode 532) 0 2
    connector532 added532 := by decide

def connector533 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added533 : List (List Vertex) := [[4, 5, 1, 0, 6, 2], [4, 0, 5, 2]]
theorem accepted533 : SyntheticAccepted (decode 533) 1 2
    connector533 added533 := by decide

def connector535 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added535 : List (List Vertex) := [[4, 7, 0, 1, 5, 2, 6], [4, 0, 6]]
theorem accepted535 : SyntheticAccepted (decode 535) 1 0
    connector535 added535 := by decide

def connector536 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added536 : List (List Vertex) := [[4, 7, 1, 5, 2, 0], [4, 0]]
theorem accepted536 : SyntheticAccepted (decode 536) 0 1
    connector536 added536 := by decide

def connector538 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added538 : List (List Vertex) := [[4, 5, 1, 7, 0, 2], [4, 0, 5, 2]]
theorem accepted538 : SyntheticAccepted (decode 538) 2 1
    connector538 added538 := by decide

def connector539 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added539 : List (List Vertex) := [[4, 5, 1, 7, 0, 2, 6], [4, 0, 6]]
theorem accepted539 : SyntheticAccepted (decode 539) 2 0
    connector539 added539 := by decide

def connector541 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added541 : List (List Vertex) := [[4, 7, 1, 0, 5, 2, 6], [4, 0, 6]]
theorem accepted541 : SyntheticAccepted (decode 541) 0 1
    connector541 added541 := by decide

def connector542 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added542 : List (List Vertex) := [[4, 5, 0, 2, 6, 1, 7], [4, 0, 7]]
theorem accepted542 : SyntheticAccepted (decode 542) 2 0
    connector542 added542 := by decide

def connector543 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added543 : List (List Vertex) := [[4, 5, 2, 0, 7, 1, 6], [4, 0, 6]]
theorem accepted543 : SyntheticAccepted (decode 543) 2 1
    connector543 added543 := by decide

def connector548 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added548 : List (List Vertex) := [[4, 7, 2, 5, 1, 0], [4, 0]]
theorem accepted548 : SyntheticAccepted (decode 548) 0 1
    connector548 added548 := by decide

def connector550 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added550 : List (List Vertex) := [[4, 5, 2, 7, 0, 1], [4, 0, 5, 1]]
theorem accepted550 : SyntheticAccepted (decode 550) 2 1
    connector550 added550 := by decide

def connector551 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added551 : List (List Vertex) := [[4, 5, 2, 7, 0, 1, 6], [4, 0, 6]]
theorem accepted551 : SyntheticAccepted (decode 551) 2 0
    connector551 added551 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
