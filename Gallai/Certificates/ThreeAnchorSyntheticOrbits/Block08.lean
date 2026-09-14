/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector608 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added608 : List (List Vertex) := [[2, 7, 4, 5, 3, 0], [2, 0]]
theorem accepted608 : SyntheticAccepted (decode 608) 0 1
    connector608 added608 := by decide

def connector610 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added610 : List (List Vertex) := [[2, 5, 4, 7, 0, 3], [2, 0, 5, 3]]
theorem accepted610 : SyntheticAccepted (decode 610) 2 1
    connector610 added610 := by decide

def connector611 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added611 : List (List Vertex) := [[2, 5, 4, 7, 0, 3, 6], [2, 0, 6]]
theorem accepted611 : SyntheticAccepted (decode 611) 2 0
    connector611 added611 := by decide

def connector615 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added615 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 3], [1, 0, 4, 5, 3]]
theorem accepted615 : SyntheticAccepted (decode 615) 1 2
    connector615 added615 := by decide

def connector616 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added616 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 4], [1, 5, 4]]
theorem accepted616 : SyntheticAccepted (decode 616) 2 1
    connector616 added616 := by decide

def connector620 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added620 : List (List Vertex) := [[2, 5, 4, 7, 1, 6, 3, 0], [2, 0]]
theorem accepted620 : SyntheticAccepted (decode 620) 2 0
    connector620 added620 := by decide

def connector621 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added621 : List (List Vertex) := [[4, 7, 2, 5, 3, 0, 1, 6], [4, 5, 0, 6]]
theorem accepted621 : SyntheticAccepted (decode 621) 1 2
    connector621 added621 := by decide

def connector623 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added623 : List (List Vertex) := [[2, 5, 4, 7, 1, 0, 3, 6], [2, 7, 0, 6]]
theorem accepted623 : SyntheticAccepted (decode 623) 1 0
    connector623 added623 := by decide

def connector625 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added625 : List (List Vertex) := [[2, 7, 4, 0, 6, 3, 5], [2, 0, 5]]
theorem accepted625 : SyntheticAccepted (decode 625) 1 0
    connector625 added625 := by decide

def connector626 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added626 : List (List Vertex) := [[2, 6, 3, 0, 7, 4, 5], [2, 0, 5]]
theorem accepted626 : SyntheticAccepted (decode 626) 2 0
    connector626 added626 := by decide

def connector627 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added627 : List (List Vertex) := [[2, 7, 0, 4, 5, 3, 6], [2, 0, 6]]
theorem accepted627 : SyntheticAccepted (decode 627) 1 2
    connector627 added627 := by decide

def connector628 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added628 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 4, 0], [1, 0]]
theorem accepted628 : SyntheticAccepted (decode 628) 1 0
    connector628 added628 := by decide

def connector630 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added630 : List (List Vertex) := [[3, 6, 1, 5, 4, 0, 2, 7], [3, 5, 0, 7]]
theorem accepted630 : SyntheticAccepted (decode 630) 2 1
    connector630 added630 := by decide

def connector631 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added631 : List (List Vertex) := [[1, 5, 3, 6, 2, 0, 4, 7], [1, 6, 0, 7]]
theorem accepted631 : SyntheticAccepted (decode 631) 2 0
    connector631 added631 := by decide

def connector632 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added632 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 3, 0], [1, 0]]
theorem accepted632 : SyntheticAccepted (decode 632) 2 0
    connector632 added632 := by decide

def connector633 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added633 : List (List Vertex) := [[4, 7, 1, 5, 3, 0, 2, 6], [4, 5, 0, 6]]
theorem accepted633 : SyntheticAccepted (decode 633) 1 2
    connector633 added633 := by decide

def connector635 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added635 : List (List Vertex) := [[1, 5, 4, 7, 2, 0, 3, 6], [1, 7, 0, 6]]
theorem accepted635 : SyntheticAccepted (decode 635) 1 0
    connector635 added635 := by decide

def connector636 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added636 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted636 : SyntheticAccepted (decode 636) 1 2
    connector636 added636 := by decide

def connector637 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added637 : List (List Vertex) := [[3, 6, 1, 7, 4, 5, 0, 2], [3, 0, 6, 2]]
theorem accepted637 : SyntheticAccepted (decode 637) 0 2
    connector637 added637 := by decide

def connector638 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added638 : List (List Vertex) := [[4, 7, 1, 6, 3, 5, 0, 2], [4, 0, 7, 2]]
theorem accepted638 : SyntheticAccepted (decode 638) 0 1
    connector638 added638 := by decide

def connector644 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added644 : List (List Vertex) := [[1, 5, 4, 7, 3, 0], [1, 0]]
theorem accepted644 : SyntheticAccepted (decode 644) 0 1
    connector644 added644 := by decide

def connector646 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added646 : List (List Vertex) := [[1, 5, 3, 0, 7, 4], [1, 0, 5, 4]]
theorem accepted646 : SyntheticAccepted (decode 646) 2 1
    connector646 added646 := by decide

def connector647 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added647 : List (List Vertex) := [[1, 6, 0, 3, 5, 4, 7], [1, 0, 7]]
theorem accepted647 : SyntheticAccepted (decode 647) 2 0
    connector647 added647 := by decide

def connector648 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added648 : List (List Vertex) := [[1, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted648 : SyntheticAccepted (decode 648) 0 2
    connector648 added648 := by decide

def connector649 : List Vertex := [6, 0, 2, 1, 7]
def added649 : List (List Vertex) := [[1, 5, 3, 0, 4, 7], [1, 0, 5, 4, 3, 7]]
theorem accepted649 : SyntheticAccepted (decode 649) 1 2
    connector649 added649 := by decide

def connector651 : List Vertex := [6, 0, 2, 1, 5]
def added651 : List (List Vertex) := [[1, 7, 3, 0, 4, 5], [1, 0, 7, 4, 3, 5]]
theorem accepted651 : SyntheticAccepted (decode 651) 1 0
    connector651 added651 := by decide

def connector652 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added652 : List (List Vertex) := [[1, 7, 4, 5, 3, 0], [1, 0]]
theorem accepted652 : SyntheticAccepted (decode 652) 2 1
    connector652 added652 := by decide

def connector653 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added653 : List (List Vertex) := [[1, 6, 0, 3, 7, 4, 5], [1, 0, 5]]
theorem accepted653 : SyntheticAccepted (decode 653) 0 2
    connector653 added653 := by decide

def connector654 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added654 : List (List Vertex) := [[1, 7, 3, 0, 5, 4], [1, 0, 7, 4]]
theorem accepted654 : SyntheticAccepted (decode 654) 0 1
    connector654 added654 := by decide

def connector656 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added656 : List (List Vertex) := [[2, 5, 4, 7, 3, 0], [2, 0]]
theorem accepted656 : SyntheticAccepted (decode 656) 0 1
    connector656 added656 := by decide

def connector658 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added658 : List (List Vertex) := [[2, 5, 3, 0, 7, 4], [2, 0, 5, 4]]
theorem accepted658 : SyntheticAccepted (decode 658) 2 1
    connector658 added658 := by decide

def connector659 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added659 : List (List Vertex) := [[2, 6, 0, 3, 5, 4, 7], [2, 0, 7]]
theorem accepted659 : SyntheticAccepted (decode 659) 2 0
    connector659 added659 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
