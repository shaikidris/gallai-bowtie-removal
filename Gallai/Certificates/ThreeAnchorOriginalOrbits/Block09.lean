/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail663 : List Vertex := [7, 4, 3, 0, 2, 1]
def added663 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 0, 4], [4, 5, 1, 0, 6, 7]]
theorem accepted663 : OriginalAccepted (decode 663) 1 2 2
    tail663 added663 := by decide

def tail664 : List Vertex := [5, 2, 1, 0, 4, 3]
def added664 : List (List Vertex) := [[3, 0, 2, 6, 7, 4, 5, 1], [1, 7, 3, 5]]
theorem accepted664 : OriginalAccepted (decode 664) 2 1 0
    tail664 added664 := by decide

def tail668 : List Vertex := [5, 2, 1, 0, 4, 3]
def added668 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 2, 0], [5, 7, 3, 0]]
theorem accepted668 : OriginalAccepted (decode 668) 2 0 0
    tail668 added668 := by decide

def tail669 : List Vertex := [5, 4, 3, 0, 1, 2]
def added669 : List (List Vertex) := [[2, 6, 1, 7, 3, 5, 0, 4], [4, 7, 6, 0, 2, 5]]
theorem accepted669 : OriginalAccepted (decode 669) 1 2 0
    tail669 added669 := by decide

def tail671 : List Vertex := [7, 4, 3, 0, 2, 1]
def added671 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 0, 4], [4, 5, 6, 0, 1, 7]]
theorem accepted671 : OriginalAccepted (decode 671) 1 0 2
    tail671 added671 := by decide

def tail672 : List Vertex := [5, 4, 3, 0, 2, 1]
def added672 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 5]]
theorem accepted672 : OriginalAccepted (decode 672) 0 2 0
    tail672 added672 := by decide

def tail673 : List Vertex := [5, 4, 3, 0, 2, 1]
def added673 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 6, 0, 5]]
theorem accepted673 : OriginalAccepted (decode 673) 1 2 0
    tail673 added673 := by decide

def tail675 : List Vertex := [7, 4, 3, 0, 2, 1]
def added675 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [3, 5, 6, 0, 7]]
theorem accepted675 : OriginalAccepted (decode 675) 1 0 2
    tail675 added675 := by decide

def tail676 : List Vertex := [5, 1, 2, 0, 4, 3]
def added676 : List (List Vertex) := [[3, 0, 1, 6, 7, 4, 5, 2], [2, 7, 3, 5]]
theorem accepted676 : OriginalAccepted (decode 676) 2 1 0
    tail676 added676 := by decide

def tail684 : List Vertex := [7, 1, 2, 0, 4, 3]
def added684 : List (List Vertex) := [[3, 0, 1, 6, 5, 4, 7, 2], [2, 5, 3, 7]]
theorem accepted684 : OriginalAccepted (decode 684) 0 1 2
    tail684 added684 := by decide

def tail688 : List Vertex := [7, 4, 3, 0, 2, 1]
def added688 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 2, 6], [7, 6]]
theorem accepted688 : OriginalAccepted (decode 688) 2 1 2
    tail688 added688 := by decide

def tail689 : List Vertex := [5, 4, 3, 0, 2, 1]
def added689 : List (List Vertex) := [[1, 0, 6, 2, 7, 5, 3], [3, 7, 4, 0, 5]]
theorem accepted689 : OriginalAccepted (decode 689) 0 2 0
    tail689 added689 := by decide

def tail690 : List Vertex := [7, 4, 3, 0, 2, 1]
def added690 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 2, 6], [7, 0, 5, 6]]
theorem accepted690 : OriginalAccepted (decode 690) 0 1 2
    tail690 added690 := by decide

def tail692 : List Vertex := [7, 2, 1, 0, 4, 3]
def added692 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 2, 0], [7, 5, 3, 0]]
theorem accepted692 : OriginalAccepted (decode 692) 0 2 2
    tail692 added692 := by decide

def tail693 : List Vertex := [5, 4, 3, 0, 2, 1]
def added693 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 0, 4], [4, 7, 6, 0, 1, 5]]
theorem accepted693 : OriginalAccepted (decode 693) 1 2 0
    tail693 added693 := by decide

def tail695 : List Vertex := [7, 4, 3, 0, 1, 2]
def added695 : List (List Vertex) := [[2, 6, 1, 5, 3, 7, 0, 4], [4, 5, 6, 0, 2, 7]]
theorem accepted695 : OriginalAccepted (decode 695) 1 0 2
    tail695 added695 := by decide

def tail696 : List Vertex := [7, 2, 1, 0, 4, 3]
def added696 : List (List Vertex) := [[3, 0, 2, 6, 5, 4, 7, 1], [1, 5, 3, 7]]
theorem accepted696 : OriginalAccepted (decode 696) 0 1 2
    tail696 added696 := by decide

def tail701 : List Vertex := [5, 4, 3, 0, 2, 1]
def added701 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 0, 4], [4, 7, 1, 0, 6, 5]]
theorem accepted701 : OriginalAccepted (decode 701) 1 0 0
    tail701 added701 := by decide

def tail709 : List Vertex := [5, 4, 3, 0, 1, 2]
def added709 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 5, 1], [1, 6, 0, 5]]
theorem accepted709 : OriginalAccepted (decode 709) 1 0 0
    tail709 added709 := by decide

def tail710 : List Vertex := [7, 3, 4, 0, 1, 2]
def added710 : List (List Vertex) := [[2, 0, 3, 6, 1, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted710 : OriginalAccepted (decode 710) 0 2 2
    tail710 added710 := by decide

def tail711 : List Vertex := [7, 4, 3, 0, 1, 2]
def added711 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 7, 3], [3, 6, 0, 7]]
theorem accepted711 : OriginalAccepted (decode 711) 1 2 2
    tail711 added711 := by decide

def tail712 : List Vertex := [7, 3, 4, 0, 1, 2]
def added712 : List (List Vertex) := [[2, 0, 3, 6, 7, 1, 5, 4], [4, 7]]
theorem accepted712 : OriginalAccepted (decode 712) 2 1 2
    tail712 added712 := by decide

def tail713 : List Vertex := [6, 3, 4, 0, 1, 2]
def added713 : List (List Vertex) := [[2, 0, 3, 7, 1, 5, 4], [4, 7, 5, 0, 6]]
theorem accepted713 : OriginalAccepted (decode 713) 0 2 1
    tail713 added713 := by decide

def tail714 : List Vertex := [7, 3, 4, 0, 1, 2]
def added714 : List (List Vertex) := [[2, 0, 3, 6, 5, 1, 7, 4], [4, 5, 0, 7]]
theorem accepted714 : OriginalAccepted (decode 714) 0 1 2
    tail714 added714 := by decide

def tail716 : List Vertex := [7, 4, 3, 0, 1, 2]
def added716 : List (List Vertex) := [[2, 0, 4, 5, 7, 1, 6, 3], [3, 7]]
theorem accepted716 : OriginalAccepted (decode 716) 2 0 2
    tail716 added716 := by decide

def tail717 : List Vertex := [5, 4, 3, 0, 1, 2]
def added717 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 6, 0, 5]]
theorem accepted717 : OriginalAccepted (decode 717) 1 2 0
    tail717 added717 := by decide

def tail719 : List Vertex := [7, 4, 3, 0, 1, 2]
def added719 : List (List Vertex) := [[2, 0, 4, 5, 6, 1, 7, 3], [3, 6, 0, 7]]
theorem accepted719 : OriginalAccepted (decode 719) 1 0 2
    tail719 added719 := by decide

def tail721 : List Vertex := [5, 4, 3, 0, 2, 1]
def added721 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 5, 2], [2, 6, 0, 5]]
theorem accepted721 : OriginalAccepted (decode 721) 1 0 0
    tail721 added721 := by decide

def tail722 : List Vertex := [7, 3, 4, 0, 2, 1]
def added722 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 7, 4], [4, 5, 0, 7]]
theorem accepted722 : OriginalAccepted (decode 722) 0 2 2
    tail722 added722 := by decide

def tail723 : List Vertex := [7, 4, 3, 0, 2, 1]
def added723 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 7, 3], [3, 6, 0, 7]]
theorem accepted723 : OriginalAccepted (decode 723) 1 2 2
    tail723 added723 := by decide

def tail724 : List Vertex := [5, 4, 3, 0, 2, 1]
def added724 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 4, 0], [5, 6, 1, 0]]
theorem accepted724 : OriginalAccepted (decode 724) 1 0 0
    tail724 added724 := by decide

def tail726 : List Vertex := [5, 2, 1, 0, 3, 4]
def added726 : List (List Vertex) := [[4, 7, 3, 6, 1, 5, 0, 2], [2, 6, 7, 0, 4, 5]]
theorem accepted726 : OriginalAccepted (decode 726) 2 1 0
    tail726 added726 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
