/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails738 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 2, 1], [5, 4, 7, 2, 0, 1]]
def added738 : List (List Vertex) := [[7, 3, 0, 5]]
def attachments738 : Fin tails738.length → Fin 3 := ![2, 0]
theorem accepted738 : CheapOriginalAccepted (decode 738) 0 1
    tails738 added738 attachments738 := by decide

def tails740 : List (List Vertex) := [[5, 7, 4, 0, 3, 6, 1, 2], [7, 3, 4, 5, 1, 0, 2]]
def added740 : List (List Vertex) := [[5, 2, 7]]
def attachments740 : Fin tails740.length → Fin 3 := ![0, 2]
theorem accepted740 : CheapOriginalAccepted (decode 740) 0 2
    tails740 added740 attachments740 := by decide

def tails741 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 2, 1], [6, 7, 3, 0, 2, 5, 1]]
def added741 : List (List Vertex) := [[5, 4, 0, 1, 6]]
def attachments741 : Fin tails741.length → Fin 3 := ![0, 1]
theorem accepted741 : CheapOriginalAccepted (decode 741) 1 2
    tails741 added741 attachments741 := by decide

def tails743 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 4, 3], [6, 5, 1, 0, 4, 7, 3]]
def added743 : List (List Vertex) := [[7, 2, 0, 3, 6]]
def attachments743 : Fin tails743.length → Fin 3 := ![2, 1]
theorem accepted743 : CheapOriginalAccepted (decode 743) 1 0
    tails743 added743 attachments743 := by decide

def tails744 : List (List Vertex) := [[7, 4, 0, 3, 6, 5, 2, 1], [5, 4, 3, 7, 2, 0, 1]]
def added744 : List (List Vertex) := [[7, 1, 5]]
def attachments744 : Fin tails744.length → Fin 3 := ![2, 0]
theorem accepted744 : CheapOriginalAccepted (decode 744) 0 1
    tails744 added744 attachments744 := by decide

def tails749 : List (List Vertex) := [[6, 0, 3, 7, 4, 5, 2, 1], [5, 6, 3, 4, 0, 2, 7, 1]]
def added749 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments749 : Fin tails749.length → Fin 3 := ![1, 0]
theorem accepted749 : CheapOriginalAccepted (decode 749) 1 0
    tails749 added749 attachments749 := by decide

def tails752 : List (List Vertex) := [[7, 5, 4, 3, 0, 1, 2, 6], [6, 3, 7, 4, 0, 2]]
def added752 : List (List Vertex) := [[2, 7]]
def attachments752 : Fin tails752.length → Fin 3 := ![2, 1]
theorem accepted752 : CheapOriginalAccepted (decode 752) 2 0
    tails752 added752 attachments752 := by decide

def tails753 : List (List Vertex) := [[6, 2, 1, 0, 3, 7, 4, 5], [5, 0, 4, 3, 6, 7, 2]]
def added753 : List (List Vertex) := [[2, 0, 6]]
def attachments753 : Fin tails753.length → Fin 3 := ![1, 0]
theorem accepted753 : CheapOriginalAccepted (decode 753) 1 2
    tails753 added753 attachments753 := by decide

def tails755 : List (List Vertex) := [[7, 0, 3, 4, 5, 6, 2, 1], [6, 3, 7, 2, 0, 1]]
def added755 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments755 : Fin tails755.length → Fin 3 := ![2, 1]
theorem accepted755 : CheapOriginalAccepted (decode 755) 1 0
    tails755 added755 attachments755 := by decide

def tails756 : List (List Vertex) := [[6, 7, 3, 0, 4, 5, 1, 2], [7, 4, 3, 6, 1, 0, 2]]
def added756 : List (List Vertex) := [[6, 2, 7]]
def attachments756 : Fin tails756.length → Fin 3 := ![1, 2]
theorem accepted756 : CheapOriginalAccepted (decode 756) 1 2
    tails756 added756 attachments756 := by decide

def tails757 : List (List Vertex) := [[6, 0, 5, 4, 3, 7, 2, 1], [5, 7, 4, 0, 2, 6, 1]]
def added757 : List (List Vertex) := [[6, 3, 0, 1, 5]]
def attachments757 : Fin tails757.length → Fin 3 := ![1, 0]
theorem accepted757 : CheapOriginalAccepted (decode 757) 0 2
    tails757 added757 attachments757 := by decide

def tails758 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 3, 4], [5, 6, 1, 0, 3, 7, 4]]
def added758 : List (List Vertex) := [[7, 2, 0, 4, 5]]
def attachments758 : Fin tails758.length → Fin 3 := ![2, 0]
theorem accepted758 : CheapOriginalAccepted (decode 758) 0 1
    tails758 added758 attachments758 := by decide

def tails761 : List (List Vertex) := [[5, 0, 4, 7, 3, 6, 2, 1], [6, 5, 4, 3, 0, 2, 7, 1]]
def added761 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments761 : Fin tails761.length → Fin 3 := ![0, 1]
theorem accepted761 : CheapOriginalAccepted (decode 761) 0 1
    tails761 added761 attachments761 := by decide

def tails764 : List (List Vertex) := [[7, 3, 0, 4, 5, 6, 2, 1], [6, 3, 4, 7, 2, 0, 1]]
def added764 : List (List Vertex) := [[7, 1, 6]]
def attachments764 : Fin tails764.length → Fin 3 := ![2, 1]
theorem accepted764 : CheapOriginalAccepted (decode 764) 1 0
    tails764 added764 attachments764 := by decide

def tails788 : List (List Vertex) := [[6, 1, 5, 2, 0, 3, 4, 7], [7, 6, 2, 1, 0, 4]]
def added788 : List (List Vertex) := [[4, 6]]
def attachments788 : Fin tails788.length → Fin 3 := ![1, 2]
theorem accepted788 : CheapOriginalAccepted (decode 788) 1 2
    tails788 added788 attachments788 := by decide

def tails789 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 4, 3], [5, 2, 6, 4, 0, 3]]
def added789 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments789 : Fin tails789.length → Fin 3 := ![1, 0]
theorem accepted789 : CheapOriginalAccepted (decode 789) 0 2
    tails789 added789 attachments789 := by decide

def tails790 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 6, 2, 0, 4, 7]]
def added790 : List (List Vertex) := [[3, 0, 1, 5]]
def attachments790 : Fin tails790.length → Fin 3 := ![2, 0]
theorem accepted790 : CheapOriginalAccepted (decode 790) 0 1
    tails790 added790 attachments790 := by decide

def tails793 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 6, 4, 0, 3]]
def added793 : List (List Vertex) := [[6, 2, 0, 1, 5]]
def attachments793 : Fin tails793.length → Fin 3 := ![1, 0]
theorem accepted793 : CheapOriginalAccepted (decode 793) 1 0
    tails793 added793 attachments793 := by decide

def tails794 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 4, 3], [5, 7, 4, 0, 3]]
def added794 : List (List Vertex) := [[7, 1, 0, 2, 5]]
def attachments794 : Fin tails794.length → Fin 3 := ![2, 0]
theorem accepted794 : CheapOriginalAccepted (decode 794) 2 0
    tails794 added794 attachments794 := by decide

def tails795 : List (List Vertex) := [[7, 0, 1, 5, 2, 6, 4, 3], [6, 7, 1, 2, 0, 3]]
def added795 : List (List Vertex) := [[7, 4, 0, 6]]
def attachments795 : Fin tails795.length → Fin 3 := ![2, 1]
theorem accepted795 : CheapOriginalAccepted (decode 795) 2 1
    tails795 added795 attachments795 := by decide

def tails796 : List (List Vertex) := [[6, 5, 2, 1, 0, 3, 4, 7], [7, 1, 6, 2, 0, 4]]
def added796 : List (List Vertex) := [[4, 6]]
def attachments796 : Fin tails796.length → Fin 3 := ![1, 2]
theorem accepted796 : CheapOriginalAccepted (decode 796) 1 0
    tails796 added796 attachments796 := by decide

def tails798 : List (List Vertex) := [[7, 4, 3, 0, 1, 6, 2, 5], [5, 0, 2, 1, 7, 6, 4]]
def added798 : List (List Vertex) := [[4, 0, 7]]
def attachments798 : Fin tails798.length → Fin 3 := ![2, 0]
theorem accepted798 : CheapOriginalAccepted (decode 798) 2 1
    tails798 added798 attachments798 := by decide

def tails799 : List (List Vertex) := [[6, 0, 1, 2, 5, 7, 4, 3], [7, 1, 6, 4, 0, 3]]
def added799 : List (List Vertex) := [[6, 2, 0, 7]]
def attachments799 : Fin tails799.length → Fin 3 := ![1, 2]
theorem accepted799 : CheapOriginalAccepted (decode 799) 2 0
    tails799 added799 attachments799 := by decide

def tails805 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 4, 3], [5, 6, 4, 0, 3]]
def added805 : List (List Vertex) := [[6, 1, 0, 2, 5]]
def attachments805 : Fin tails805.length → Fin 3 := ![1, 0]
theorem accepted805 : CheapOriginalAccepted (decode 805) 1 0
    tails805 added805 attachments805 := by decide

def tails806 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 7, 4, 0, 3]]
def added806 : List (List Vertex) := [[7, 2, 0, 1, 5]]
def attachments806 : Fin tails806.length → Fin 3 := ![2, 0]
theorem accepted806 : CheapOriginalAccepted (decode 806) 2 0
    tails806 added806 attachments806 := by decide

def tails807 : List (List Vertex) := [[6, 0, 1, 5, 2, 7, 4, 3], [7, 6, 1, 2, 0, 3]]
def added807 : List (List Vertex) := [[6, 4, 0, 7]]
def attachments807 : Fin tails807.length → Fin 3 := ![1, 2]
theorem accepted807 : CheapOriginalAccepted (decode 807) 1 2
    tails807 added807 attachments807 := by decide

def tails808 : List (List Vertex) := [[7, 1, 5, 2, 0, 3, 4, 6], [6, 7, 2, 1, 0, 4]]
def added808 : List (List Vertex) := [[4, 7]]
def attachments808 : Fin tails808.length → Fin 3 := ![2, 1]
theorem accepted808 : CheapOriginalAccepted (decode 808) 2 1
    tails808 added808 attachments808 := by decide

def tails809 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 7, 2, 0, 4, 6]]
def added809 : List (List Vertex) := [[3, 0, 1, 5]]
def attachments809 : Fin tails809.length → Fin 3 := ![1, 0]
theorem accepted809 : CheapOriginalAccepted (decode 809) 0 2
    tails809 added809 attachments809 := by decide

def tails810 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 4, 3], [5, 2, 7, 4, 0, 3]]
def added810 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments810 : Fin tails810.length → Fin 3 := ![2, 0]
theorem accepted810 : CheapOriginalAccepted (decode 810) 0 1
    tails810 added810 attachments810 := by decide

def tails812 : List (List Vertex) := [[7, 5, 2, 1, 0, 3, 4, 6], [6, 1, 7, 2, 0, 4]]
def added812 : List (List Vertex) := [[4, 7]]
def attachments812 : Fin tails812.length → Fin 3 := ![2, 1]
theorem accepted812 : CheapOriginalAccepted (decode 812) 2 0
    tails812 added812 attachments812 := by decide

def tails813 : List (List Vertex) := [[6, 4, 3, 0, 1, 7, 2, 5], [5, 0, 2, 1, 6, 7, 4]]
def added813 : List (List Vertex) := [[4, 0, 6]]
def attachments813 : Fin tails813.length → Fin 3 := ![1, 0]
theorem accepted813 : CheapOriginalAccepted (decode 813) 1 2
    tails813 added813 attachments813 := by decide

def tails815 : List (List Vertex) := [[7, 0, 1, 2, 5, 6, 4, 3], [6, 1, 7, 4, 0, 3]]
def added815 : List (List Vertex) := [[7, 2, 0, 6]]
def attachments815 : Fin tails815.length → Fin 3 := ![2, 1]
theorem accepted815 : CheapOriginalAccepted (decode 815) 1 0
    tails815 added815 attachments815 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
