/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail552 : List Vertex := [5, 2, 1, 0, 4, 3]
def added552 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 5]]
theorem accepted552 : OriginalAccepted (decode 552) 0 2 0
    tail552 added552 := by decide

def tail553 : List Vertex := [5, 2, 1, 0, 4, 3]
def added553 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 6, 0, 5]]
theorem accepted553 : OriginalAccepted (decode 553) 1 2 0
    tail553 added553 := by decide

def tail555 : List Vertex := [7, 2, 1, 0, 4, 3]
def added555 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 1], [1, 5, 6, 0, 7]]
theorem accepted555 : OriginalAccepted (decode 555) 1 0 2
    tail555 added555 := by decide

def tail556 : List Vertex := [7, 1, 2, 0, 4, 3]
def added556 : List (List Vertex) := [[3, 0, 1, 6, 7, 4, 5, 2], [2, 7]]
theorem accepted556 : OriginalAccepted (decode 556) 2 1 2
    tail556 added556 := by decide

def tail557 : List Vertex := [6, 1, 2, 0, 4, 3]
def added557 : List (List Vertex) := [[3, 0, 1, 7, 4, 5, 2], [2, 7, 5, 0, 6]]
theorem accepted557 : OriginalAccepted (decode 557) 0 2 1
    tail557 added557 := by decide

def tail558 : List Vertex := [7, 1, 2, 0, 4, 3]
def added558 : List (List Vertex) := [[3, 0, 1, 6, 5, 4, 7, 2], [2, 5, 0, 7]]
theorem accepted558 : OriginalAccepted (decode 558) 0 1 2
    tail558 added558 := by decide

def tail565 : List Vertex := [6, 2, 1, 0, 4, 3]
def added565 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 6, 1], [1, 5, 0, 6]]
theorem accepted565 : OriginalAccepted (decode 565) 0 1 1
    tail565 added565 := by decide

def tail566 : List Vertex := [7, 2, 1, 0, 4, 3]
def added566 : List (List Vertex) := [[3, 0, 2, 6, 1, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted566 : OriginalAccepted (decode 566) 0 2 2
    tail566 added566 := by decide

def tail567 : List Vertex := [6, 1, 2, 0, 4, 3]
def added567 : List (List Vertex) := [[3, 0, 1, 5, 4, 7, 6, 2], [2, 7, 0, 6]]
theorem accepted567 : OriginalAccepted (decode 567) 2 1 1
    tail567 added567 := by decide

def tail568 : List Vertex := [7, 2, 1, 0, 4, 3]
def added568 : List (List Vertex) := [[3, 0, 2, 6, 7, 4, 5, 1], [1, 7]]
theorem accepted568 : OriginalAccepted (decode 568) 2 1 2
    tail568 added568 := by decide

def tail569 : List Vertex := [6, 2, 1, 0, 4, 3]
def added569 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [1, 7, 5, 0, 6]]
theorem accepted569 : OriginalAccepted (decode 569) 0 2 1
    tail569 added569 := by decide

def tail570 : List Vertex := [7, 2, 1, 0, 4, 3]
def added570 : List (List Vertex) := [[3, 0, 2, 6, 5, 4, 7, 1], [1, 5, 0, 7]]
theorem accepted570 : OriginalAccepted (decode 570) 0 1 2
    tail570 added570 := by decide

def tail572 : List Vertex := [7, 2, 1, 0, 4, 3]
def added572 : List (List Vertex) := [[3, 0, 2, 6, 1, 7, 4, 5], [7, 5]]
theorem accepted572 : OriginalAccepted (decode 572) 2 0 2
    tail572 added572 := by decide

def tail573 : List Vertex := [6, 2, 1, 0, 4, 3]
def added573 : List (List Vertex) := [[3, 0, 5, 4, 7, 6, 1], [1, 7, 2, 0, 6]]
theorem accepted573 : OriginalAccepted (decode 573) 1 2 1
    tail573 added573 := by decide

def tail575 : List Vertex := [7, 2, 1, 0, 4, 3]
def added575 : List (List Vertex) := [[3, 0, 2, 6, 1, 7, 4, 5], [7, 0, 6, 5]]
theorem accepted575 : OriginalAccepted (decode 575) 1 0 2
    tail575 added575 := by decide

def tail580 : List Vertex := [5, 4, 3, 0, 1, 2]
def added580 : List (List Vertex) := [[2, 0, 4, 7, 5, 1, 6, 3], [3, 5]]
theorem accepted580 : OriginalAccepted (decode 580) 0 2 0
    tail580 added580 := by decide

def tail581 : List Vertex := [5, 4, 3, 0, 1, 2]
def added581 : List (List Vertex) := [[2, 0, 4, 7, 6, 1, 5, 3], [3, 6, 0, 5]]
theorem accepted581 : OriginalAccepted (decode 581) 1 2 0
    tail581 added581 := by decide

def tail583 : List Vertex := [7, 4, 3, 0, 1, 2]
def added583 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 3], [3, 5, 6, 0, 7]]
theorem accepted583 : OriginalAccepted (decode 583) 1 0 2
    tail583 added583 := by decide

def tail584 : List Vertex := [5, 3, 4, 0, 1, 2]
def added584 : List (List Vertex) := [[2, 0, 3, 6, 5, 1, 7, 4], [4, 5]]
theorem accepted584 : OriginalAccepted (decode 584) 0 1 0
    tail584 added584 := by decide

def tail586 : List Vertex := [5, 3, 4, 0, 1, 2]
def added586 : List (List Vertex) := [[2, 0, 3, 6, 7, 1, 5, 4], [4, 7, 0, 5]]
theorem accepted586 : OriginalAccepted (decode 586) 2 1 0
    tail586 added586 := by decide

def tail587 : List Vertex := [6, 3, 4, 0, 1, 2]
def added587 : List (List Vertex) := [[2, 0, 3, 5, 1, 7, 4], [4, 5, 7, 0, 6]]
theorem accepted587 : OriginalAccepted (decode 587) 2 0 1
    tail587 added587 := by decide

def tail589 : List Vertex := [5, 4, 3, 0, 1, 2]
def added589 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted589 : OriginalAccepted (decode 589) 1 0 0
    tail589 added589 := by decide

def tail590 : List Vertex := [5, 3, 4, 0, 1, 2]
def added590 : List (List Vertex) := [[2, 0, 3, 6, 1, 7, 5, 4], [4, 7, 0, 5]]
theorem accepted590 : OriginalAccepted (decode 590) 2 0 0
    tail590 added590 := by decide

def tail591 : List Vertex := [7, 4, 3, 0, 1, 2]
def added591 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted591 : OriginalAccepted (decode 591) 1 2 2
    tail591 added591 := by decide

def tail592 : List Vertex := [5, 4, 3, 0, 2, 1]
def added592 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5]]
theorem accepted592 : OriginalAccepted (decode 592) 0 2 0
    tail592 added592 := by decide

def tail593 : List Vertex := [5, 4, 3, 0, 2, 1]
def added593 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6, 0, 5]]
theorem accepted593 : OriginalAccepted (decode 593) 1 2 0
    tail593 added593 := by decide

def tail595 : List Vertex := [7, 4, 3, 0, 2, 1]
def added595 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [3, 5, 6, 0, 7]]
theorem accepted595 : OriginalAccepted (decode 595) 1 0 2
    tail595 added595 := by decide

def tail596 : List Vertex := [5, 4, 3, 0, 2, 1]
def added596 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6, 1, 5]]
theorem accepted596 : OriginalAccepted (decode 596) 1 2 0
    tail596 added596 := by decide

def tail603 : List Vertex := [6, 3, 4, 0, 2, 1]
def added603 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 0, 3], [3, 5, 1, 0, 7, 6]]
theorem accepted603 : OriginalAccepted (decode 603) 2 1 1
    tail603 added603 := by decide

def tail604 : List Vertex := [5, 4, 3, 0, 1, 2]
def added604 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 4, 0], [5, 6, 2, 0]]
theorem accepted604 : OriginalAccepted (decode 604) 1 0 0
    tail604 added604 := by decide

def tail606 : List Vertex := [7, 1, 2, 0, 3, 4]
def added606 : List (List Vertex) := [[3, 5, 2, 6, 1, 0, 4, 7], [4, 5, 0, 7, 6, 3]]
theorem accepted606 : OriginalAccepted (decode 606) 2 1 2
    tail606 added606 := by decide

def tail607 : List Vertex := [7, 4, 3, 0, 2, 1]
def added607 : List (List Vertex) := [[2, 6, 3, 5, 4, 0, 1, 7], [1, 6, 0, 7, 5, 2]]
theorem accepted607 : OriginalAccepted (decode 607) 2 0 2
    tail607 added607 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
