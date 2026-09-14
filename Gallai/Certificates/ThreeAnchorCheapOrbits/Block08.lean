/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails623 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 2, 1], [6, 5, 3, 0, 2, 7, 1]]
def added623 : List (List Vertex) := [[7, 4, 0, 1, 6]]
def attachments623 : Fin tails623.length → Fin 3 := ![2, 1]
theorem accepted623 : CheapOriginalAccepted (decode 623) 1 0
    tails623 added623 attachments623 := by decide

def tails625 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 2, 1], [5, 6, 2, 0, 1]]
def added625 : List (List Vertex) := [[6, 3, 0, 4, 5]]
def attachments625 : Fin tails625.length → Fin 3 := ![1, 0]
theorem accepted625 : CheapOriginalAccepted (decode 625) 1 0
    tails625 added625 attachments625 := by decide

def tails626 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 7, 2, 0, 1]]
def added626 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments626 : Fin tails626.length → Fin 3 := ![2, 0]
theorem accepted626 : CheapOriginalAccepted (decode 626) 2 0
    tails626 added626 attachments626 := by decide

def tails627 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 2, 1], [7, 6, 3, 4, 0, 1]]
def added627 : List (List Vertex) := [[6, 2, 0, 7]]
def attachments627 : Fin tails627.length → Fin 3 := ![1, 2]
theorem accepted627 : CheapOriginalAccepted (decode 627) 1 2
    tails627 added627 attachments627 := by decide

def tails628 : List (List Vertex) := [[6, 5, 3, 0, 4, 7, 2, 1], [5, 4, 3, 6, 2, 0, 1]]
def added628 : List (List Vertex) := [[6, 1, 5]]
def attachments628 : Fin tails628.length → Fin 3 := ![1, 0]
theorem accepted628 : CheapOriginalAccepted (decode 628) 1 0
    tails628 added628 attachments628 := by decide

def tails630 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 6, 2, 0, 3, 5, 4]]
def added630 : List (List Vertex) := [[5, 1, 0, 4, 7]]
def attachments630 : Fin tails630.length → Fin 3 := ![0, 2]
theorem accepted630 : CheapOriginalAccepted (decode 630) 2 1
    tails630 added630 attachments630 := by decide

def tails631 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 5, 4, 0, 1, 6, 2]]
def added631 : List (List Vertex) := [[6, 3, 0, 2, 7]]
def attachments631 : Fin tails631.length → Fin 3 := ![1, 2]
theorem accepted631 : CheapOriginalAccepted (decode 631) 2 0
    tails631 added631 attachments631 := by decide

def tails632 : List (List Vertex) := [[7, 5, 4, 0, 3, 6, 2, 1], [5, 3, 4, 7, 2, 0, 1]]
def added632 : List (List Vertex) := [[7, 1, 5]]
def attachments632 : Fin tails632.length → Fin 3 := ![2, 0]
theorem accepted632 : CheapOriginalAccepted (decode 632) 2 0
    tails632 added632 attachments632 := by decide

def tails633 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 7, 2, 0, 4, 5, 3]]
def added633 : List (List Vertex) := [[5, 1, 0, 3, 6]]
def attachments633 : Fin tails633.length → Fin 3 := ![0, 1]
theorem accepted633 : CheapOriginalAccepted (decode 633) 1 2
    tails633 added633 attachments633 := by decide

def tails635 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 1, 2], [6, 5, 3, 0, 1, 7, 2]]
def added635 : List (List Vertex) := [[7, 4, 0, 2, 6]]
def attachments635 : Fin tails635.length → Fin 3 := ![2, 1]
theorem accepted635 : CheapOriginalAccepted (decode 635) 1 0
    tails635 added635 attachments635 := by decide

def tails636 : List (List Vertex) := [[6, 7, 4, 5, 3, 0, 2, 1], [7, 2, 6, 3, 4, 0, 1]]
def added636 : List (List Vertex) := [[6, 1, 7]]
def attachments636 : Fin tails636.length → Fin 3 := ![1, 2]
theorem accepted636 : CheapOriginalAccepted (decode 636) 1 2
    tails636 added636 attachments636 := by decide

def tails637 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 1, 0, 2, 7, 5, 3]]
def added637 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments637 : Fin tails637.length → Fin 3 := ![0, 1]
theorem accepted637 : CheapOriginalAccepted (decode 637) 0 2
    tails637 added637 attachments637 := by decide

def tails638 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 1, 0, 2, 6, 5, 4]]
def added638 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments638 : Fin tails638.length → Fin 3 := ![0, 2]
theorem accepted638 : CheapOriginalAccepted (decode 638) 0 1
    tails638 added638 attachments638 := by decide

def tails644 : List (List Vertex) := [[5, 3, 7, 4, 0, 2, 1, 6], [6, 5, 4, 3, 0, 1]]
def added644 : List (List Vertex) := [[1, 5]]
def attachments644 : Fin tails644.length → Fin 3 := ![0, 1]
theorem accepted644 : CheapOriginalAccepted (decode 644) 0 1
    tails644 added644 attachments644 := by decide

def tails646 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 1, 2], [7, 4, 5, 1, 0, 2]]
def added646 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments646 : Fin tails646.length → Fin 3 := ![0, 2]
theorem accepted646 : CheapOriginalAccepted (decode 646) 2 1
    tails646 added646 attachments646 := by decide

def tails647 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 5, 4, 0, 1, 6]]
def added647 : List (List Vertex) := [[2, 0, 3, 7]]
def attachments647 : Fin tails647.length → Fin 3 := ![1, 2]
theorem accepted647 : CheapOriginalAccepted (decode 647) 2 0
    tails647 added647 attachments647 := by decide

def tails649 : List (List Vertex) := [[5, 1, 2, 0, 3, 4, 7, 6], [6, 0, 4, 5, 3, 7, 1]]
def added649 : List (List Vertex) := [[1, 0, 5]]
def attachments649 : Fin tails649.length → Fin 3 := ![0, 1]
theorem accepted649 : CheapOriginalAccepted (decode 649) 1 2
    tails649 added649 attachments649 := by decide

def tails651 : List (List Vertex) := [[7, 1, 2, 0, 3, 4, 5, 6], [6, 0, 4, 7, 3, 5, 1]]
def added651 : List (List Vertex) := [[1, 0, 7]]
def attachments651 : Fin tails651.length → Fin 3 := ![2, 1]
theorem accepted651 : CheapOriginalAccepted (decode 651) 1 0
    tails651 added651 attachments651 := by decide

def tails652 : List (List Vertex) := [[7, 3, 5, 4, 0, 2, 1, 6], [6, 7, 4, 3, 0, 1]]
def added652 : List (List Vertex) := [[1, 7]]
def attachments652 : Fin tails652.length → Fin 3 := ![2, 1]
theorem accepted652 : CheapOriginalAccepted (decode 652) 2 1
    tails652 added652 attachments652 := by decide

def tails653 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 7, 4, 0, 1, 6]]
def added653 : List (List Vertex) := [[2, 0, 3, 5]]
def attachments653 : Fin tails653.length → Fin 3 := ![1, 0]
theorem accepted653 : CheapOriginalAccepted (decode 653) 0 2
    tails653 added653 attachments653 := by decide

def tails654 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 1, 2], [5, 4, 7, 1, 0, 2]]
def added654 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments654 : Fin tails654.length → Fin 3 := ![2, 0]
theorem accepted654 : CheapOriginalAccepted (decode 654) 0 1
    tails654 added654 attachments654 := by decide

def tails656 : List (List Vertex) := [[5, 3, 7, 4, 0, 1, 2, 6], [6, 5, 4, 3, 0, 2]]
def added656 : List (List Vertex) := [[2, 5]]
def attachments656 : Fin tails656.length → Fin 3 := ![0, 1]
theorem accepted656 : CheapOriginalAccepted (decode 656) 0 1
    tails656 added656 attachments656 := by decide

def tails658 : List (List Vertex) := [[5, 0, 4, 3, 7, 6, 2, 1], [7, 4, 5, 2, 0, 1]]
def added658 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments658 : Fin tails658.length → Fin 3 := ![0, 2]
theorem accepted658 : CheapOriginalAccepted (decode 658) 2 1
    tails658 added658 attachments658 := by decide

def tails659 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 5, 4, 0, 2, 6]]
def added659 : List (List Vertex) := [[1, 0, 3, 7]]
def attachments659 : Fin tails659.length → Fin 3 := ![1, 2]
theorem accepted659 : CheapOriginalAccepted (decode 659) 2 0
    tails659 added659 attachments659 := by decide

def tails663 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 6, 2, 0, 4, 5, 1]]
def added663 : List (List Vertex) := [[6, 1, 0, 3, 7]]
def attachments663 : Fin tails663.length → Fin 3 := ![1, 2]
theorem accepted663 : CheapOriginalAccepted (decode 663) 1 2
    tails663 added663 attachments663 := by decide

def tails664 : List (List Vertex) := [[5, 1, 0, 2, 6, 7, 4, 3], [7, 1, 2, 5, 4, 0, 3]]
def added664 : List (List Vertex) := [[5, 3, 7]]
def attachments664 : Fin tails664.length → Fin 3 := ![0, 2]
theorem accepted664 : CheapOriginalAccepted (decode 664) 2 1
    tails664 added664 attachments664 := by decide

def tails668 : List (List Vertex) := [[7, 5, 2, 6, 1, 0, 4, 3], [5, 4, 7, 1, 2, 0, 3]]
def added668 : List (List Vertex) := [[7, 3, 5]]
def attachments668 : Fin tails668.length → Fin 3 := ![2, 0]
theorem accepted668 : CheapOriginalAccepted (decode 668) 2 0
    tails668 added668 attachments668 := by decide

def tails669 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 3, 0, 4, 7, 6, 2]]
def added669 : List (List Vertex) := [[6, 1, 0, 2, 5]]
def attachments669 : Fin tails669.length → Fin 3 := ![1, 0]
theorem accepted669 : CheapOriginalAccepted (decode 669) 1 2
    tails669 added669 attachments669 := by decide

def tails671 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 3, 0, 4, 5, 6, 1]]
def added671 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments671 : Fin tails671.length → Fin 3 := ![1, 2]
theorem accepted671 : CheapOriginalAccepted (decode 671) 1 0
    tails671 added671 attachments671 := by decide

def tails673 : List (List Vertex) := [[5, 2, 1, 0, 3, 4, 7, 6], [6, 0, 4, 5, 3, 7, 2]]
def added673 : List (List Vertex) := [[2, 0, 5]]
def attachments673 : Fin tails673.length → Fin 3 := ![0, 1]
theorem accepted673 : CheapOriginalAccepted (decode 673) 1 2
    tails673 added673 attachments673 := by decide

def tails675 : List (List Vertex) := [[7, 2, 1, 0, 3, 4, 5, 6], [6, 0, 4, 7, 3, 5, 2]]
def added675 : List (List Vertex) := [[2, 0, 7]]
def attachments675 : Fin tails675.length → Fin 3 := ![2, 1]
theorem accepted675 : CheapOriginalAccepted (decode 675) 1 0
    tails675 added675 attachments675 := by decide

def tails676 : List (List Vertex) := [[5, 2, 0, 1, 6, 7, 4, 3], [7, 2, 1, 5, 4, 0, 3]]
def added676 : List (List Vertex) := [[5, 3, 7]]
def attachments676 : Fin tails676.length → Fin 3 := ![0, 2]
theorem accepted676 : CheapOriginalAccepted (decode 676) 2 1
    tails676 added676 attachments676 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
