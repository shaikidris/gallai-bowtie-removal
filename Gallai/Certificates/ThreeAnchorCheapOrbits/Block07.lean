/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails566 : List (List Vertex) := [[5, 0, 1, 6, 2, 7, 4, 3], [7, 5, 1, 2, 0, 3]]
def added566 : List (List Vertex) := [[5, 4, 0, 7]]
def attachments566 : Fin tails566.length → Fin 3 := ![0, 2]
theorem accepted566 : CheapOriginalAccepted (decode 566) 0 2
    tails566 added566 attachments566 := by decide

def tails567 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 7, 4, 0, 3]]
def added567 : List (List Vertex) := [[7, 2, 0, 1, 6]]
def attachments567 : Fin tails567.length → Fin 3 := ![2, 1]
theorem accepted567 : CheapOriginalAccepted (decode 567) 2 1
    tails567 added567 attachments567 := by decide

def tails568 : List (List Vertex) := [[7, 6, 2, 1, 0, 3, 4, 5], [5, 1, 7, 2, 0, 4]]
def added568 : List (List Vertex) := [[4, 7]]
def attachments568 : Fin tails568.length → Fin 3 := ![2, 0]
theorem accepted568 : CheapOriginalAccepted (decode 568) 2 1
    tails568 added568 attachments568 := by decide

def tails569 : List (List Vertex) := [[5, 4, 3, 0, 1, 7, 2, 6], [6, 0, 2, 1, 5, 7, 4]]
def added569 : List (List Vertex) := [[4, 0, 5]]
def attachments569 : Fin tails569.length → Fin 3 := ![0, 1]
theorem accepted569 : CheapOriginalAccepted (decode 569) 0 2
    tails569 added569 attachments569 := by decide

def tails570 : List (List Vertex) := [[7, 0, 1, 2, 6, 5, 4, 3], [5, 1, 7, 4, 0, 3]]
def added570 : List (List Vertex) := [[7, 2, 0, 5]]
def attachments570 : Fin tails570.length → Fin 3 := ![2, 0]
theorem accepted570 : CheapOriginalAccepted (decode 570) 0 1
    tails570 added570 attachments570 := by decide

def tails572 : List (List Vertex) := [[7, 1, 6, 2, 0, 3, 4, 5], [5, 7, 2, 1, 0, 4]]
def added572 : List (List Vertex) := [[4, 7]]
def attachments572 : Fin tails572.length → Fin 3 := ![2, 0]
theorem accepted572 : CheapOriginalAccepted (decode 572) 2 0
    tails572 added572 attachments572 := by decide

def tails573 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 4, 3], [6, 7, 2, 0, 4, 5]]
def added573 : List (List Vertex) := [[3, 0, 1, 6]]
def attachments573 : Fin tails573.length → Fin 3 := ![0, 1]
theorem accepted573 : CheapOriginalAccepted (decode 573) 1 2
    tails573 added573 attachments573 := by decide

def tails575 : List (List Vertex) := [[7, 0, 2, 1, 6, 5, 4, 3], [6, 2, 7, 4, 0, 3]]
def added575 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments575 : Fin tails575.length → Fin 3 := ![2, 1]
theorem accepted575 : CheapOriginalAccepted (decode 575) 1 0
    tails575 added575 attachments575 := by decide

def tails580 : List (List Vertex) := [[5, 7, 4, 3, 0, 2, 1, 6], [6, 3, 5, 4, 0, 1]]
def added580 : List (List Vertex) := [[1, 5]]
def attachments580 : Fin tails580.length → Fin 3 := ![0, 1]
theorem accepted580 : CheapOriginalAccepted (decode 580) 0 2
    tails580 added580 attachments580 := by decide

def tails581 : List (List Vertex) := [[5, 0, 3, 4, 7, 6, 1, 2], [6, 3, 5, 1, 0, 2]]
def added581 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments581 : Fin tails581.length → Fin 3 := ![0, 1]
theorem accepted581 : CheapOriginalAccepted (decode 581) 1 2
    tails581 added581 attachments581 := by decide

def tails583 : List (List Vertex) := [[6, 1, 2, 0, 3, 5, 4, 7], [7, 0, 4, 3, 6, 5, 1]]
def added583 : List (List Vertex) := [[1, 0, 6]]
def attachments583 : Fin tails583.length → Fin 3 := ![1, 2]
theorem accepted583 : CheapOriginalAccepted (decode 583) 1 0
    tails583 added583 attachments583 := by decide

def tails584 : List (List Vertex) := [[5, 6, 3, 4, 0, 2, 1, 7], [7, 4, 5, 3, 0, 1]]
def added584 : List (List Vertex) := [[1, 5]]
def attachments584 : Fin tails584.length → Fin 3 := ![0, 2]
theorem accepted584 : CheapOriginalAccepted (decode 584) 0 1
    tails584 added584 attachments584 := by decide

def tails586 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 1, 2], [7, 4, 5, 1, 0, 2]]
def added586 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments586 : Fin tails586.length → Fin 3 := ![0, 2]
theorem accepted586 : CheapOriginalAccepted (decode 586) 2 1
    tails586 added586 attachments586 := by decide

def tails587 : List (List Vertex) := [[7, 1, 2, 0, 4, 5, 3, 6], [6, 0, 3, 4, 7, 5, 1]]
def added587 : List (List Vertex) := [[1, 0, 7]]
def attachments587 : Fin tails587.length → Fin 3 := ![2, 1]
theorem accepted587 : CheapOriginalAccepted (decode 587) 2 0
    tails587 added587 attachments587 := by decide

def tails589 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 1, 2], [5, 6, 1, 0, 2]]
def added589 : List (List Vertex) := [[6, 3, 0, 4, 5]]
def attachments589 : Fin tails589.length → Fin 3 := ![1, 0]
theorem accepted589 : CheapOriginalAccepted (decode 589) 1 0
    tails589 added589 attachments589 := by decide

def tails590 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 7, 1, 0, 2]]
def added590 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments590 : Fin tails590.length → Fin 3 := ![2, 0]
theorem accepted590 : CheapOriginalAccepted (decode 590) 2 0
    tails590 added590 attachments590 := by decide

def tails591 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 1, 2], [7, 6, 3, 4, 0, 2]]
def added591 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments591 : Fin tails591.length → Fin 3 := ![1, 2]
theorem accepted591 : CheapOriginalAccepted (decode 591) 1 2
    tails591 added591 attachments591 := by decide

def tails592 : List (List Vertex) := [[5, 7, 4, 3, 0, 1, 2, 6], [6, 3, 5, 4, 0, 2]]
def added592 : List (List Vertex) := [[2, 5]]
def attachments592 : Fin tails592.length → Fin 3 := ![0, 1]
theorem accepted592 : CheapOriginalAccepted (decode 592) 0 2
    tails592 added592 attachments592 := by decide

def tails593 : List (List Vertex) := [[5, 0, 3, 4, 7, 6, 2, 1], [6, 3, 5, 2, 0, 1]]
def added593 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments593 : Fin tails593.length → Fin 3 := ![0, 1]
theorem accepted593 : CheapOriginalAccepted (decode 593) 1 2
    tails593 added593 attachments593 := by decide

def tails595 : List (List Vertex) := [[6, 2, 1, 0, 3, 5, 4, 7], [7, 0, 4, 3, 6, 5, 2]]
def added595 : List (List Vertex) := [[2, 0, 6]]
def attachments595 : Fin tails595.length → Fin 3 := ![1, 2]
theorem accepted595 : CheapOriginalAccepted (decode 595) 1 0
    tails595 added595 attachments595 := by decide

def tails596 : List (List Vertex) := [[5, 3, 0, 4, 7, 6, 2, 1], [6, 3, 4, 5, 2, 0, 1]]
def added596 : List (List Vertex) := [[5, 1, 6]]
def attachments596 : Fin tails596.length → Fin 3 := ![0, 1]
theorem accepted596 : CheapOriginalAccepted (decode 596) 1 2
    tails596 added596 attachments596 := by decide

def tails603 : List (List Vertex) := [[7, 0, 4, 5, 3, 6, 2, 1], [6, 7, 4, 3, 0, 2, 5, 1]]
def added603 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments603 : Fin tails603.length → Fin 3 := ![2, 1]
theorem accepted603 : CheapOriginalAccepted (decode 603) 2 1
    tails603 added603 attachments603 := by decide

def tails604 : List (List Vertex) := [[6, 5, 3, 0, 4, 7, 1, 2], [5, 4, 3, 6, 1, 0, 2]]
def added604 : List (List Vertex) := [[6, 2, 5]]
def attachments604 : Fin tails604.length → Fin 3 := ![1, 0]
theorem accepted604 : CheapOriginalAccepted (decode 604) 1 0
    tails604 added604 attachments604 := by decide

def tails606 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 3, 4], [7, 6, 1, 0, 3, 5, 4]]
def added606 : List (List Vertex) := [[5, 2, 0, 4, 7]]
def attachments606 : Fin tails606.length → Fin 3 := ![0, 2]
theorem accepted606 : CheapOriginalAccepted (decode 606) 2 1
    tails606 added606 attachments606 := by decide

def tails607 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 5, 4, 0, 2, 6, 1]]
def added607 : List (List Vertex) := [[6, 3, 0, 1, 7]]
def attachments607 : Fin tails607.length → Fin 3 := ![1, 2]
theorem accepted607 : CheapOriginalAccepted (decode 607) 2 0
    tails607 added607 attachments607 := by decide

def tails608 : List (List Vertex) := [[5, 6, 3, 4, 0, 1, 2, 7], [7, 4, 5, 3, 0, 2]]
def added608 : List (List Vertex) := [[2, 5]]
def attachments608 : Fin tails608.length → Fin 3 := ![0, 2]
theorem accepted608 : CheapOriginalAccepted (decode 608) 0 1
    tails608 added608 attachments608 := by decide

def tails610 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 2, 1], [7, 4, 5, 2, 0, 1]]
def added610 : List (List Vertex) := [[5, 3, 0, 7]]
def attachments610 : Fin tails610.length → Fin 3 := ![0, 2]
theorem accepted610 : CheapOriginalAccepted (decode 610) 2 1
    tails610 added610 attachments610 := by decide

def tails611 : List (List Vertex) := [[7, 2, 1, 0, 4, 5, 3, 6], [6, 0, 3, 4, 7, 5, 2]]
def added611 : List (List Vertex) := [[2, 0, 7]]
def attachments611 : Fin tails611.length → Fin 3 := ![2, 1]
theorem accepted611 : CheapOriginalAccepted (decode 611) 2 0
    tails611 added611 attachments611 := by decide

def tails615 : List (List Vertex) := [[6, 0, 3, 5, 4, 7, 2, 1], [7, 6, 3, 4, 0, 2, 5, 1]]
def added615 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments615 : Fin tails615.length → Fin 3 := ![1, 2]
theorem accepted615 : CheapOriginalAccepted (decode 615) 1 2
    tails615 added615 attachments615 := by decide

def tails616 : List (List Vertex) := [[5, 4, 0, 3, 6, 7, 2, 1], [7, 4, 3, 5, 2, 0, 1]]
def added616 : List (List Vertex) := [[5, 1, 7]]
def attachments616 : Fin tails616.length → Fin 3 := ![0, 2]
theorem accepted616 : CheapOriginalAccepted (decode 616) 2 1
    tails616 added616 attachments616 := by decide

def tails620 : List (List Vertex) := [[7, 5, 4, 0, 3, 6, 1, 2], [5, 3, 4, 7, 1, 0, 2]]
def added620 : List (List Vertex) := [[7, 2, 5]]
def attachments620 : Fin tails620.length → Fin 3 := ![2, 0]
theorem accepted620 : CheapOriginalAccepted (decode 620) 2 0
    tails620 added620 attachments620 := by decide

def tails621 : List (List Vertex) := [[5, 0, 6, 1, 2, 7, 4, 3], [6, 7, 1, 0, 4, 5, 3]]
def added621 : List (List Vertex) := [[5, 2, 0, 3, 6]]
def attachments621 : Fin tails621.length → Fin 3 := ![0, 1]
theorem accepted621 : CheapOriginalAccepted (decode 621) 1 2
    tails621 added621 attachments621 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
