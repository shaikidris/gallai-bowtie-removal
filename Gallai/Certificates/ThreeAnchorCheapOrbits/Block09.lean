/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails684 : List (List Vertex) := [[7, 2, 0, 1, 6, 5, 4, 3], [5, 2, 1, 7, 4, 0, 3]]
def added684 : List (List Vertex) := [[7, 3, 5]]
def attachments684 : Fin tails684.length → Fin 3 := ![2, 0]
theorem accepted684 : CheapOriginalAccepted (decode 684) 0 1
    tails684 added684 attachments684 := by decide

def tails688 : List (List Vertex) := [[7, 3, 5, 4, 0, 1, 2, 6], [6, 7, 4, 3, 0, 2]]
def added688 : List (List Vertex) := [[2, 7]]
def attachments688 : Fin tails688.length → Fin 3 := ![2, 1]
theorem accepted688 : CheapOriginalAccepted (decode 688) 2 1
    tails688 added688 attachments688 := by decide

def tails689 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 7, 4, 0, 2, 6]]
def added689 : List (List Vertex) := [[1, 0, 3, 5]]
def attachments689 : Fin tails689.length → Fin 3 := ![1, 0]
theorem accepted689 : CheapOriginalAccepted (decode 689) 0 2
    tails689 added689 attachments689 := by decide

def tails690 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 2, 1], [5, 4, 7, 2, 0, 1]]
def added690 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments690 : Fin tails690.length → Fin 3 := ![2, 0]
theorem accepted690 : CheapOriginalAccepted (decode 690) 0 1
    tails690 added690 attachments690 := by decide

def tails692 : List (List Vertex) := [[5, 7, 2, 6, 1, 0, 4, 3], [7, 4, 5, 1, 2, 0, 3]]
def added692 : List (List Vertex) := [[5, 3, 7]]
def attachments692 : Fin tails692.length → Fin 3 := ![0, 2]
theorem accepted692 : CheapOriginalAccepted (decode 692) 0 2
    tails692 added692 attachments692 := by decide

def tails693 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 3, 0, 4, 7, 6, 1]]
def added693 : List (List Vertex) := [[6, 2, 0, 1, 5]]
def attachments693 : Fin tails693.length → Fin 3 := ![1, 0]
theorem accepted693 : CheapOriginalAccepted (decode 693) 1 2
    tails693 added693 attachments693 := by decide

def tails695 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 3, 0, 4, 5, 6, 2]]
def added695 : List (List Vertex) := [[6, 1, 0, 2, 7]]
def attachments695 : Fin tails695.length → Fin 3 := ![1, 2]
theorem accepted695 : CheapOriginalAccepted (decode 695) 1 0
    tails695 added695 attachments695 := by decide

def tails696 : List (List Vertex) := [[7, 1, 0, 2, 6, 5, 4, 3], [5, 1, 2, 7, 4, 0, 3]]
def added696 : List (List Vertex) := [[7, 3, 5]]
def attachments696 : Fin tails696.length → Fin 3 := ![2, 0]
theorem accepted696 : CheapOriginalAccepted (decode 696) 0 1
    tails696 added696 attachments696 := by decide

def tails701 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 6, 2, 0, 4, 7, 1]]
def added701 : List (List Vertex) := [[6, 1, 0, 3, 5]]
def attachments701 : Fin tails701.length → Fin 3 := ![1, 0]
theorem accepted701 : CheapOriginalAccepted (decode 701) 1 0
    tails701 added701 attachments701 := by decide

def tails709 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 1, 2], [5, 6, 3, 4, 0, 2]]
def added709 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments709 : Fin tails709.length → Fin 3 := ![1, 0]
theorem accepted709 : CheapOriginalAccepted (decode 709) 1 0
    tails709 added709 attachments709 := by decide

def tails710 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 5, 1, 0, 2]]
def added710 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments710 : Fin tails710.length → Fin 3 := ![0, 2]
theorem accepted710 : CheapOriginalAccepted (decode 710) 0 2
    tails710 added710 attachments710 := by decide

def tails711 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 1, 2], [7, 6, 1, 0, 2]]
def added711 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments711 : Fin tails711.length → Fin 3 := ![1, 2]
theorem accepted711 : CheapOriginalAccepted (decode 711) 1 2
    tails711 added711 attachments711 := by decide

def tails712 : List (List Vertex) := [[7, 6, 3, 4, 0, 2, 1, 5], [5, 4, 7, 3, 0, 1]]
def added712 : List (List Vertex) := [[1, 7]]
def attachments712 : Fin tails712.length → Fin 3 := ![2, 0]
theorem accepted712 : CheapOriginalAccepted (decode 712) 2 1
    tails712 added712 attachments712 := by decide

def tails713 : List (List Vertex) := [[5, 1, 2, 0, 4, 7, 3, 6], [6, 0, 3, 4, 5, 7, 1]]
def added713 : List (List Vertex) := [[1, 0, 5]]
def attachments713 : Fin tails713.length → Fin 3 := ![0, 1]
theorem accepted713 : CheapOriginalAccepted (decode 713) 0 2
    tails713 added713 attachments713 := by decide

def tails714 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 1, 2], [5, 4, 7, 1, 0, 2]]
def added714 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments714 : Fin tails714.length → Fin 3 := ![2, 0]
theorem accepted714 : CheapOriginalAccepted (decode 714) 0 1
    tails714 added714 attachments714 := by decide

def tails716 : List (List Vertex) := [[7, 5, 4, 3, 0, 2, 1, 6], [6, 3, 7, 4, 0, 1]]
def added716 : List (List Vertex) := [[1, 7]]
def attachments716 : Fin tails716.length → Fin 3 := ![2, 1]
theorem accepted716 : CheapOriginalAccepted (decode 716) 2 0
    tails716 added716 attachments716 := by decide

def tails717 : List (List Vertex) := [[6, 1, 2, 0, 3, 7, 4, 5], [5, 0, 4, 3, 6, 7, 1]]
def added717 : List (List Vertex) := [[1, 0, 6]]
def attachments717 : Fin tails717.length → Fin 3 := ![1, 0]
theorem accepted717 : CheapOriginalAccepted (decode 717) 1 2
    tails717 added717 attachments717 := by decide

def tails719 : List (List Vertex) := [[7, 0, 3, 4, 5, 6, 1, 2], [6, 3, 7, 1, 0, 2]]
def added719 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments719 : Fin tails719.length → Fin 3 := ![2, 1]
theorem accepted719 : CheapOriginalAccepted (decode 719) 1 0
    tails719 added719 attachments719 := by decide

def tails721 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 2, 1], [5, 6, 3, 4, 0, 1]]
def added721 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments721 : Fin tails721.length → Fin 3 := ![1, 0]
theorem accepted721 : CheapOriginalAccepted (decode 721) 1 0
    tails721 added721 attachments721 := by decide

def tails722 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 5, 2, 0, 1]]
def added722 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments722 : Fin tails722.length → Fin 3 := ![0, 2]
theorem accepted722 : CheapOriginalAccepted (decode 722) 0 2
    tails722 added722 attachments722 := by decide

def tails723 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 2, 1], [7, 6, 2, 0, 1]]
def added723 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments723 : Fin tails723.length → Fin 3 := ![1, 2]
theorem accepted723 : CheapOriginalAccepted (decode 723) 1 2
    tails723 added723 attachments723 := by decide

def tails724 : List (List Vertex) := [[6, 5, 4, 7, 3, 0, 2, 1], [5, 2, 6, 3, 4, 0, 1]]
def added724 : List (List Vertex) := [[6, 1, 5]]
def attachments724 : Fin tails724.length → Fin 3 := ![1, 0]
theorem accepted724 : CheapOriginalAccepted (decode 724) 1 0
    tails724 added724 attachments724 := by decide

def tails726 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 1, 0, 2, 6, 7, 4]]
def added726 : List (List Vertex) := [[7, 3, 0, 4, 5]]
def attachments726 : Fin tails726.length → Fin 3 := ![2, 0]
theorem accepted726 : CheapOriginalAccepted (decode 726) 2 1
    tails726 added726 attachments726 := by decide

def tails727 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 1, 0, 2, 5, 7, 3]]
def added727 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments727 : Fin tails727.length → Fin 3 := ![2, 1]
theorem accepted727 : CheapOriginalAccepted (decode 727) 2 0
    tails727 added727 attachments727 := by decide

def tails728 : List (List Vertex) := [[5, 7, 4, 0, 3, 6, 2, 1], [7, 3, 4, 5, 2, 0, 1]]
def added728 : List (List Vertex) := [[5, 1, 7]]
def attachments728 : Fin tails728.length → Fin 3 := ![0, 2]
theorem accepted728 : CheapOriginalAccepted (decode 728) 0 2
    tails728 added728 attachments728 := by decide

def tails729 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 1, 2], [6, 7, 3, 0, 1, 5, 2]]
def added729 : List (List Vertex) := [[5, 4, 0, 2, 6]]
def attachments729 : Fin tails729.length → Fin 3 := ![0, 1]
theorem accepted729 : CheapOriginalAccepted (decode 729) 1 2
    tails729 added729 attachments729 := by decide

def tails731 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 4, 3], [6, 5, 2, 0, 4, 7, 3]]
def added731 : List (List Vertex) := [[7, 1, 0, 3, 6]]
def attachments731 : Fin tails731.length → Fin 3 := ![2, 1]
theorem accepted731 : CheapOriginalAccepted (decode 731) 1 0
    tails731 added731 attachments731 := by decide

def tails732 : List (List Vertex) := [[6, 7, 3, 0, 4, 5, 2, 1], [7, 4, 3, 6, 2, 0, 1]]
def added732 : List (List Vertex) := [[6, 1, 7]]
def attachments732 : Fin tails732.length → Fin 3 := ![1, 2]
theorem accepted732 : CheapOriginalAccepted (decode 732) 1 2
    tails732 added732 attachments732 := by decide

def tails733 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 1, 2], [5, 7, 4, 0, 1, 6, 2]]
def added733 : List (List Vertex) := [[6, 3, 0, 2, 5]]
def attachments733 : Fin tails733.length → Fin 3 := ![1, 0]
theorem accepted733 : CheapOriginalAccepted (decode 733) 0 2
    tails733 added733 attachments733 := by decide

def tails734 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 3, 4], [5, 6, 2, 0, 3, 7, 4]]
def added734 : List (List Vertex) := [[7, 1, 0, 4, 5]]
def attachments734 : Fin tails734.length → Fin 3 := ![2, 0]
theorem accepted734 : CheapOriginalAccepted (decode 734) 0 1
    tails734 added734 attachments734 := by decide

def tails736 : List (List Vertex) := [[7, 6, 3, 4, 0, 1, 2, 5], [5, 4, 7, 3, 0, 2]]
def added736 : List (List Vertex) := [[2, 7]]
def attachments736 : Fin tails736.length → Fin 3 := ![2, 0]
theorem accepted736 : CheapOriginalAccepted (decode 736) 2 1
    tails736 added736 attachments736 := by decide

def tails737 : List (List Vertex) := [[5, 2, 1, 0, 4, 7, 3, 6], [6, 0, 3, 4, 5, 7, 2]]
def added737 : List (List Vertex) := [[2, 0, 5]]
def attachments737 : Fin tails737.length → Fin 3 := ![0, 1]
theorem accepted737 : CheapOriginalAccepted (decode 737) 0 2
    tails737 added737 attachments737 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
