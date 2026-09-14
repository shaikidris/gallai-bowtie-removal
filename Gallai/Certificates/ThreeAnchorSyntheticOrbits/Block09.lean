/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector663 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added663 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 3], [1, 0, 4, 5, 3]]
theorem accepted663 : SyntheticAccepted (decode 663) 1 2
    connector663 added663 := by decide

def connector664 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added664 : List (List Vertex) := [[3, 0, 2, 5, 4, 7, 1], [3, 5, 1]]
theorem accepted664 : SyntheticAccepted (decode 664) 2 1
    connector664 added664 := by decide

def connector668 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added668 : List (List Vertex) := [[3, 5, 4, 7, 1, 6, 2, 0], [3, 0]]
theorem accepted668 : SyntheticAccepted (decode 668) 2 0
    connector668 added668 := by decide

def connector669 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added669 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 0, 4], [2, 0, 5, 4]]
theorem accepted669 : SyntheticAccepted (decode 669) 1 2
    connector669 added669 := by decide

def connector671 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added671 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 0, 4], [1, 0, 7, 4]]
theorem accepted671 : SyntheticAccepted (decode 671) 1 0
    connector671 added671 := by decide

def connector672 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added672 : List (List Vertex) := [[2, 7, 3, 5, 4, 0], [2, 0]]
theorem accepted672 : SyntheticAccepted (decode 672) 0 2
    connector672 added672 := by decide

def connector673 : List Vertex := [6, 0, 1, 2, 7]
def added673 : List (List Vertex) := [[2, 5, 3, 0, 4, 7], [2, 0, 5, 4, 3, 7]]
theorem accepted673 : SyntheticAccepted (decode 673) 1 2
    connector673 added673 := by decide

def connector675 : List Vertex := [6, 0, 1, 2, 5]
def added675 : List (List Vertex) := [[2, 7, 3, 0, 4, 5], [2, 0, 7, 4, 3, 5]]
theorem accepted675 : SyntheticAccepted (decode 675) 1 0
    connector675 added675 := by decide

def connector676 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added676 : List (List Vertex) := [[3, 0, 1, 5, 4, 7, 2], [3, 5, 2]]
theorem accepted676 : SyntheticAccepted (decode 676) 2 1
    connector676 added676 := by decide

def connector684 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added684 : List (List Vertex) := [[3, 0, 1, 7, 4, 5, 2], [3, 7, 2]]
theorem accepted684 : SyntheticAccepted (decode 684) 0 1
    connector684 added684 := by decide

def connector688 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added688 : List (List Vertex) := [[2, 7, 4, 5, 3, 0], [2, 0]]
theorem accepted688 : SyntheticAccepted (decode 688) 2 1
    connector688 added688 := by decide

def connector689 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added689 : List (List Vertex) := [[2, 6, 0, 3, 7, 4, 5], [2, 0, 5]]
theorem accepted689 : SyntheticAccepted (decode 689) 0 2
    connector689 added689 := by decide

def connector690 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added690 : List (List Vertex) := [[2, 7, 3, 0, 5, 4], [2, 0, 7, 4]]
theorem accepted690 : SyntheticAccepted (decode 690) 0 1
    connector690 added690 := by decide

def connector692 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added692 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 2, 0], [3, 0]]
theorem accepted692 : SyntheticAccepted (decode 692) 0 2
    connector692 added692 := by decide

def connector693 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added693 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 0, 4], [1, 0, 5, 4]]
theorem accepted693 : SyntheticAccepted (decode 693) 1 2
    connector693 added693 := by decide

def connector695 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added695 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 0, 4], [2, 0, 7, 4]]
theorem accepted695 : SyntheticAccepted (decode 695) 1 0
    connector695 added695 := by decide

def connector696 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added696 : List (List Vertex) := [[3, 0, 2, 7, 4, 5, 1], [3, 7, 1]]
theorem accepted696 : SyntheticAccepted (decode 696) 0 1
    connector696 added696 := by decide

def connector701 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added701 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 3], [1, 0, 4, 7, 3]]
theorem accepted701 : SyntheticAccepted (decode 701) 1 0
    connector701 added701 := by decide

def connector709 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added709 : List (List Vertex) := [[1, 5, 0, 4, 7, 3, 6], [1, 0, 6]]
theorem accepted709 : SyntheticAccepted (decode 709) 1 0
    connector709 added709 := by decide

def connector710 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added710 : List (List Vertex) := [[1, 6, 3, 0, 5, 4, 7], [1, 0, 7]]
theorem accepted710 : SyntheticAccepted (decode 710) 0 2
    connector710 added710 := by decide

def connector711 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added711 : List (List Vertex) := [[1, 5, 4, 0, 6, 3, 7], [1, 0, 7]]
theorem accepted711 : SyntheticAccepted (decode 711) 1 2
    connector711 added711 := by decide

def connector712 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added712 : List (List Vertex) := [[1, 5, 4, 7, 3, 0], [1, 0]]
theorem accepted712 : SyntheticAccepted (decode 712) 2 1
    connector712 added712 := by decide

def connector713 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added713 : List (List Vertex) := [[1, 7, 4, 5, 0, 3, 6], [1, 0, 6]]
theorem accepted713 : SyntheticAccepted (decode 713) 0 2
    connector713 added713 := by decide

def connector714 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added714 : List (List Vertex) := [[1, 7, 4, 5, 0, 3], [1, 0, 7, 3]]
theorem accepted714 : SyntheticAccepted (decode 714) 0 1
    connector714 added714 := by decide

def connector716 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added716 : List (List Vertex) := [[1, 6, 3, 7, 4, 0], [1, 0]]
theorem accepted716 : SyntheticAccepted (decode 716) 2 0
    connector716 added716 := by decide

def connector717 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added717 : List (List Vertex) := [[1, 7, 3, 6, 0, 4, 5], [1, 0, 5]]
theorem accepted717 : SyntheticAccepted (decode 717) 1 2
    connector717 added717 := by decide

def connector719 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added719 : List (List Vertex) := [[1, 7, 3, 6, 0, 4], [1, 0, 7, 4]]
theorem accepted719 : SyntheticAccepted (decode 719) 1 0
    connector719 added719 := by decide

def connector721 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added721 : List (List Vertex) := [[2, 5, 0, 4, 7, 3, 6], [2, 0, 6]]
theorem accepted721 : SyntheticAccepted (decode 721) 1 0
    connector721 added721 := by decide

def connector722 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added722 : List (List Vertex) := [[2, 6, 3, 0, 5, 4, 7], [2, 0, 7]]
theorem accepted722 : SyntheticAccepted (decode 722) 0 2
    connector722 added722 := by decide

def connector723 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added723 : List (List Vertex) := [[2, 5, 4, 0, 6, 3, 7], [2, 0, 7]]
theorem accepted723 : SyntheticAccepted (decode 723) 1 2
    connector723 added723 := by decide

def connector724 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added724 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 4, 0], [1, 0]]
theorem accepted724 : SyntheticAccepted (decode 724) 1 0
    connector724 added724 := by decide

def connector726 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added726 : List (List Vertex) := [[4, 5, 1, 6, 3, 7, 0, 2], [4, 0, 5, 2]]
theorem accepted726 : SyntheticAccepted (decode 726) 2 1
    connector726 added726 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
