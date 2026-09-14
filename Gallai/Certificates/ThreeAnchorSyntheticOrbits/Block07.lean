/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector552 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added552 : List (List Vertex) := [[4, 7, 1, 5, 2, 0], [4, 0]]
theorem accepted552 : SyntheticAccepted (decode 552) 0 2
    connector552 added552 := by decide

def connector553 : List Vertex := [6, 0, 3, 4, 7]
def added553 : List (List Vertex) := [[4, 5, 1, 0, 2, 7], [4, 0, 5, 2, 1, 7]]
theorem accepted553 : SyntheticAccepted (decode 553) 1 2
    connector553 added553 := by decide

def connector555 : List Vertex := [6, 0, 3, 4, 5]
def added555 : List (List Vertex) := [[4, 7, 1, 0, 2, 5], [4, 0, 7, 2, 1, 5]]
theorem accepted555 : SyntheticAccepted (decode 555) 1 0
    connector555 added555 := by decide

def connector556 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added556 : List (List Vertex) := [[4, 5, 2, 7, 1, 0], [4, 0]]
theorem accepted556 : SyntheticAccepted (decode 556) 2 1
    connector556 added556 := by decide

def connector557 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added557 : List (List Vertex) := [[4, 7, 2, 5, 0, 1, 6], [4, 0, 6]]
theorem accepted557 : SyntheticAccepted (decode 557) 0 2
    connector557 added557 := by decide

def connector558 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added558 : List (List Vertex) := [[4, 7, 2, 5, 0, 1], [4, 0, 7, 1]]
theorem accepted558 : SyntheticAccepted (decode 558) 0 1
    connector558 added558 := by decide

def connector565 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added565 : List (List Vertex) := [[4, 7, 2, 0, 5, 1, 6], [4, 0, 6]]
theorem accepted565 : SyntheticAccepted (decode 565) 0 1
    connector565 added565 := by decide

def connector566 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added566 : List (List Vertex) := [[4, 7, 0, 2, 6, 1, 5], [4, 0, 5]]
theorem accepted566 : SyntheticAccepted (decode 566) 0 2
    connector566 added566 := by decide

def connector567 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added567 : List (List Vertex) := [[4, 5, 1, 0, 7, 2, 6], [4, 0, 6]]
theorem accepted567 : SyntheticAccepted (decode 567) 2 1
    connector567 added567 := by decide

def connector568 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added568 : List (List Vertex) := [[4, 5, 1, 7, 2, 0], [4, 0]]
theorem accepted568 : SyntheticAccepted (decode 568) 2 1
    connector568 added568 := by decide

def connector569 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added569 : List (List Vertex) := [[4, 7, 1, 5, 0, 2, 6], [4, 0, 6]]
theorem accepted569 : SyntheticAccepted (decode 569) 0 2
    connector569 added569 := by decide

def connector570 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added570 : List (List Vertex) := [[4, 7, 1, 5, 0, 2], [4, 0, 7, 2]]
theorem accepted570 : SyntheticAccepted (decode 570) 0 1
    connector570 added570 := by decide

def connector572 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added572 : List (List Vertex) := [[4, 7, 2, 6, 1, 0], [4, 0]]
theorem accepted572 : SyntheticAccepted (decode 572) 2 0
    connector572 added572 := by decide

def connector573 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added573 : List (List Vertex) := [[4, 5, 0, 1, 7, 2, 6], [4, 0, 6]]
theorem accepted573 : SyntheticAccepted (decode 573) 1 2
    connector573 added573 := by decide

def connector575 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added575 : List (List Vertex) := [[4, 7, 1, 0, 6, 2], [4, 0, 7, 2]]
theorem accepted575 : SyntheticAccepted (decode 575) 1 0
    connector575 added575 := by decide

def connector580 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added580 : List (List Vertex) := [[1, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted580 : SyntheticAccepted (decode 580) 0 2
    connector580 added580 := by decide

def connector581 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added581 : List (List Vertex) := [[1, 5, 3, 6, 0, 4], [1, 0, 5, 4]]
theorem accepted581 : SyntheticAccepted (decode 581) 1 2
    connector581 added581 := by decide

def connector583 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added583 : List (List Vertex) := [[1, 5, 3, 6, 0, 4, 7], [1, 0, 7]]
theorem accepted583 : SyntheticAccepted (decode 583) 1 0
    connector583 added583 := by decide

def connector584 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added584 : List (List Vertex) := [[1, 7, 4, 5, 3, 0], [1, 0]]
theorem accepted584 : SyntheticAccepted (decode 584) 0 1
    connector584 added584 := by decide

def connector586 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added586 : List (List Vertex) := [[1, 5, 4, 7, 0, 3], [1, 0, 5, 3]]
theorem accepted586 : SyntheticAccepted (decode 586) 2 1
    connector586 added586 := by decide

def connector587 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added587 : List (List Vertex) := [[1, 5, 4, 7, 0, 3, 6], [1, 0, 6]]
theorem accepted587 : SyntheticAccepted (decode 587) 2 0
    connector587 added587 := by decide

def connector589 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added589 : List (List Vertex) := [[1, 7, 4, 0, 6, 3, 5], [1, 0, 5]]
theorem accepted589 : SyntheticAccepted (decode 589) 1 0
    connector589 added589 := by decide

def connector590 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added590 : List (List Vertex) := [[1, 6, 3, 0, 7, 4, 5], [1, 0, 5]]
theorem accepted590 : SyntheticAccepted (decode 590) 2 0
    connector590 added590 := by decide

def connector591 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added591 : List (List Vertex) := [[1, 7, 0, 4, 5, 3, 6], [1, 0, 6]]
theorem accepted591 : SyntheticAccepted (decode 591) 1 2
    connector591 added591 := by decide

def connector592 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added592 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted592 : SyntheticAccepted (decode 592) 0 2
    connector592 added592 := by decide

def connector593 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added593 : List (List Vertex) := [[2, 5, 3, 6, 0, 4], [2, 0, 5, 4]]
theorem accepted593 : SyntheticAccepted (decode 593) 1 2
    connector593 added593 := by decide

def connector595 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added595 : List (List Vertex) := [[2, 5, 3, 6, 0, 4, 7], [2, 0, 7]]
theorem accepted595 : SyntheticAccepted (decode 595) 1 0
    connector595 added595 := by decide

def connector596 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added596 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [1, 5, 3]]
theorem accepted596 : SyntheticAccepted (decode 596) 1 2
    connector596 added596 := by decide

def connector603 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added603 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 4], [1, 0, 3, 5, 4]]
theorem accepted603 : SyntheticAccepted (decode 603) 2 1
    connector603 added603 := by decide

def connector604 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added604 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 4, 0], [2, 0]]
theorem accepted604 : SyntheticAccepted (decode 604) 1 0
    connector604 added604 := by decide

def connector606 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added606 : List (List Vertex) := [[3, 6, 2, 5, 4, 0, 1, 7], [3, 5, 0, 7]]
theorem accepted606 : SyntheticAccepted (decode 606) 2 1
    connector606 added606 := by decide

def connector607 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added607 : List (List Vertex) := [[2, 5, 3, 6, 1, 0, 4, 7], [2, 6, 0, 7]]
theorem accepted607 : SyntheticAccepted (decode 607) 2 0
    connector607 added607 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
