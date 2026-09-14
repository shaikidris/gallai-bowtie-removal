/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail608 : List Vertex := [5, 3, 4, 0, 2, 1]
def added608 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5]]
theorem accepted608 : OriginalAccepted (decode 608) 0 1 0
    tail608 added608 := by decide

def tail610 : List Vertex := [5, 3, 4, 0, 2, 1]
def added610 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7, 0, 5]]
theorem accepted610 : OriginalAccepted (decode 610) 2 1 0
    tail610 added610 := by decide

def tail611 : List Vertex := [6, 3, 4, 0, 2, 1]
def added611 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 4], [4, 5, 7, 0, 6]]
theorem accepted611 : OriginalAccepted (decode 611) 2 0 1
    tail611 added611 := by decide

def tail615 : List Vertex := [7, 4, 3, 0, 2, 1]
def added615 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 0, 4], [4, 5, 1, 0, 6, 7]]
theorem accepted615 : OriginalAccepted (decode 615) 1 2 2
    tail615 added615 := by decide

def tail616 : List Vertex := [5, 3, 4, 0, 2, 1]
def added616 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7, 1, 5]]
theorem accepted616 : OriginalAccepted (decode 616) 2 1 0
    tail616 added616 := by decide

def tail620 : List Vertex := [5, 3, 4, 0, 1, 2]
def added620 : List (List Vertex) := [[2, 5, 4, 7, 1, 6, 3, 0], [5, 7, 2, 0]]
theorem accepted620 : OriginalAccepted (decode 620) 2 0 0
    tail620 added620 := by decide

def tail621 : List Vertex := [6, 1, 2, 0, 4, 3]
def added621 : List (List Vertex) := [[4, 5, 2, 7, 1, 0, 3, 6], [3, 5, 0, 6, 7, 4]]
theorem accepted621 : OriginalAccepted (decode 621) 1 2 1
    tail621 added621 := by decide

def tail623 : List Vertex := [6, 3, 4, 0, 2, 1]
def added623 : List (List Vertex) := [[2, 7, 4, 5, 3, 0, 1, 6], [1, 7, 0, 6, 5, 2]]
theorem accepted623 : OriginalAccepted (decode 623) 1 0 1
    tail623 added623 := by decide

def tail625 : List Vertex := [5, 4, 3, 0, 2, 1]
def added625 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted625 : OriginalAccepted (decode 625) 1 0 0
    tail625 added625 := by decide

def tail626 : List Vertex := [5, 3, 4, 0, 2, 1]
def added626 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 5, 4], [4, 7, 0, 5]]
theorem accepted626 : OriginalAccepted (decode 626) 2 0 0
    tail626 added626 := by decide

def tail627 : List Vertex := [7, 4, 3, 0, 2, 1]
def added627 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted627 : OriginalAccepted (decode 627) 1 2 2
    tail627 added627 := by decide

def tail628 : List Vertex := [5, 4, 3, 0, 2, 1]
def added628 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 4, 0], [5, 6, 1, 0]]
theorem accepted628 : OriginalAccepted (decode 628) 1 0 0
    tail628 added628 := by decide

def tail630 : List Vertex := [7, 2, 1, 0, 3, 4]
def added630 : List (List Vertex) := [[3, 5, 1, 6, 2, 0, 4, 7], [4, 5, 0, 7, 6, 3]]
theorem accepted630 : OriginalAccepted (decode 630) 2 1 2
    tail630 added630 := by decide

def tail631 : List Vertex := [7, 4, 3, 0, 1, 2]
def added631 : List (List Vertex) := [[1, 6, 3, 5, 4, 0, 2, 7], [2, 6, 0, 7, 5, 1]]
theorem accepted631 : OriginalAccepted (decode 631) 2 0 2
    tail631 added631 := by decide

def tail632 : List Vertex := [5, 3, 4, 0, 2, 1]
def added632 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 3, 0], [5, 7, 1, 0]]
theorem accepted632 : OriginalAccepted (decode 632) 2 0 0
    tail632 added632 := by decide

def tail633 : List Vertex := [6, 2, 1, 0, 4, 3]
def added633 : List (List Vertex) := [[4, 5, 1, 7, 2, 0, 3, 6], [3, 5, 0, 6, 7, 4]]
theorem accepted633 : OriginalAccepted (decode 633) 1 2 1
    tail633 added633 := by decide

def tail635 : List Vertex := [6, 3, 4, 0, 1, 2]
def added635 : List (List Vertex) := [[1, 7, 4, 5, 3, 0, 2, 6], [2, 7, 0, 6, 5, 1]]
theorem accepted635 : OriginalAccepted (decode 635) 1 0 1
    tail635 added635 := by decide

def tail636 : List Vertex := [7, 4, 3, 0, 2, 1]
def added636 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 4, 0], [7, 6, 1, 0]]
theorem accepted636 : OriginalAccepted (decode 636) 1 2 2
    tail636 added636 := by decide

def tail637 : List Vertex := [6, 2, 1, 0, 4, 3]
def added637 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 0, 2], [2, 7, 5, 0, 3, 6]]
theorem accepted637 : OriginalAccepted (decode 637) 0 2 1
    tail637 added637 := by decide

def tail638 : List Vertex := [7, 2, 1, 0, 3, 4]
def added638 : List (List Vertex) := [[4, 5, 3, 6, 1, 7, 0, 2], [2, 6, 5, 0, 4, 7]]
theorem accepted638 : OriginalAccepted (decode 638) 0 1 2
    tail638 added638 := by decide

def tail644 : List Vertex := [5, 4, 3, 0, 1, 2]
def added644 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 1, 6], [5, 6]]
theorem accepted644 : OriginalAccepted (decode 644) 0 1 0
    tail644 added644 := by decide

def tail646 : List Vertex := [5, 4, 3, 0, 1, 2]
def added646 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 1, 6], [5, 0, 7, 6]]
theorem accepted646 : OriginalAccepted (decode 646) 2 1 0
    tail646 added646 := by decide

def tail647 : List Vertex := [7, 4, 3, 0, 1, 2]
def added647 : List (List Vertex) := [[2, 0, 6, 1, 5, 7, 3], [3, 5, 4, 0, 7]]
theorem accepted647 : OriginalAccepted (decode 647) 2 0 2
    tail647 added647 := by decide

def tail648 : List Vertex := [5, 4, 3, 0, 1, 2]
def added648 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 5]]
theorem accepted648 : OriginalAccepted (decode 648) 0 2 0
    tail648 added648 := by decide

def tail649 : List Vertex := [5, 4, 3, 0, 1, 2]
def added649 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 6, 0, 5]]
theorem accepted649 : OriginalAccepted (decode 649) 1 2 0
    tail649 added649 := by decide

def tail651 : List Vertex := [7, 4, 3, 0, 1, 2]
def added651 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 3], [3, 5, 6, 0, 7]]
theorem accepted651 : OriginalAccepted (decode 651) 1 0 2
    tail651 added651 := by decide

def tail652 : List Vertex := [7, 4, 3, 0, 1, 2]
def added652 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 1, 6], [7, 6]]
theorem accepted652 : OriginalAccepted (decode 652) 2 1 2
    tail652 added652 := by decide

def tail653 : List Vertex := [5, 4, 3, 0, 1, 2]
def added653 : List (List Vertex) := [[2, 0, 6, 1, 7, 5, 3], [3, 7, 4, 0, 5]]
theorem accepted653 : OriginalAccepted (decode 653) 0 2 0
    tail653 added653 := by decide

def tail654 : List Vertex := [7, 4, 3, 0, 1, 2]
def added654 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 1, 6], [7, 0, 5, 6]]
theorem accepted654 : OriginalAccepted (decode 654) 0 1 2
    tail654 added654 := by decide

def tail656 : List Vertex := [5, 4, 3, 0, 2, 1]
def added656 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 2, 6], [5, 6]]
theorem accepted656 : OriginalAccepted (decode 656) 0 1 0
    tail656 added656 := by decide

def tail658 : List Vertex := [5, 4, 3, 0, 2, 1]
def added658 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 2, 6], [5, 0, 7, 6]]
theorem accepted658 : OriginalAccepted (decode 658) 2 1 0
    tail658 added658 := by decide

def tail659 : List Vertex := [7, 4, 3, 0, 2, 1]
def added659 : List (List Vertex) := [[1, 0, 6, 2, 5, 7, 3], [3, 5, 4, 0, 7]]
theorem accepted659 : OriginalAccepted (decode 659) 2 0 2
    tail659 added659 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
