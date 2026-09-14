/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector727 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added727 : List (List Vertex) := [[3, 6, 1, 5, 4, 7, 0, 2], [3, 0, 6, 2]]
theorem accepted727 : SyntheticAccepted (decode 727) 2 0
    connector727 added727 := by decide

def connector728 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added728 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 3, 0], [1, 0]]
theorem accepted728 : SyntheticAccepted (decode 728) 0 2
    connector728 added728 := by decide

def connector729 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added729 : List (List Vertex) := [[1, 7, 4, 5, 2, 0, 3, 6], [1, 5, 0, 6]]
theorem accepted729 : SyntheticAccepted (decode 729) 1 2
    connector729 added729 := by decide

def connector731 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added731 : List (List Vertex) := [[4, 5, 1, 7, 3, 0, 2, 6], [4, 7, 0, 6]]
theorem accepted731 : SyntheticAccepted (decode 731) 1 0
    connector731 added731 := by decide

def connector732 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added732 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 4, 0], [1, 0]]
theorem accepted732 : SyntheticAccepted (decode 732) 1 2
    connector732 added732 := by decide

def connector733 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added733 : List (List Vertex) := [[1, 7, 3, 6, 2, 0, 4, 5], [1, 6, 0, 5]]
theorem accepted733 : SyntheticAccepted (decode 733) 0 2
    connector733 added733 := by decide

def connector734 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added734 : List (List Vertex) := [[3, 6, 1, 7, 4, 0, 2, 5], [3, 7, 0, 5]]
theorem accepted734 : SyntheticAccepted (decode 734) 0 1
    connector734 added734 := by decide

def connector736 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added736 : List (List Vertex) := [[2, 5, 4, 7, 3, 0], [2, 0]]
theorem accepted736 : SyntheticAccepted (decode 736) 2 1
    connector736 added736 := by decide

def connector737 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added737 : List (List Vertex) := [[2, 7, 4, 5, 0, 3, 6], [2, 0, 6]]
theorem accepted737 : SyntheticAccepted (decode 737) 0 2
    connector737 added737 := by decide

def connector738 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added738 : List (List Vertex) := [[2, 7, 4, 5, 0, 3], [2, 0, 7, 3]]
theorem accepted738 : SyntheticAccepted (decode 738) 0 1
    connector738 added738 := by decide

def connector740 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added740 : List (List Vertex) := [[2, 7, 4, 5, 1, 6, 3, 0], [2, 0]]
theorem accepted740 : SyntheticAccepted (decode 740) 0 2
    connector740 added740 := by decide

def connector741 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added741 : List (List Vertex) := [[2, 7, 4, 5, 1, 0, 3, 6], [2, 5, 0, 6]]
theorem accepted741 : SyntheticAccepted (decode 741) 1 2
    connector741 added741 := by decide

def connector743 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added743 : List (List Vertex) := [[4, 5, 2, 7, 3, 0, 1, 6], [4, 7, 0, 6]]
theorem accepted743 : SyntheticAccepted (decode 743) 1 0
    connector743 added743 := by decide

def connector744 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added744 : List (List Vertex) := [[1, 0, 3, 7, 2, 5, 4], [1, 7, 4]]
theorem accepted744 : SyntheticAccepted (decode 744) 0 1
    connector744 added744 := by decide

def connector749 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added749 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 3], [1, 0, 4, 7, 3]]
theorem accepted749 : SyntheticAccepted (decode 749) 1 0
    connector749 added749 := by decide

def connector752 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added752 : List (List Vertex) := [[2, 6, 3, 7, 4, 0], [2, 0]]
theorem accepted752 : SyntheticAccepted (decode 752) 2 0
    connector752 added752 := by decide

def connector753 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added753 : List (List Vertex) := [[2, 7, 3, 6, 0, 4, 5], [2, 0, 5]]
theorem accepted753 : SyntheticAccepted (decode 753) 1 2
    connector753 added753 := by decide

def connector755 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added755 : List (List Vertex) := [[2, 7, 3, 6, 0, 4], [2, 0, 7, 4]]
theorem accepted755 : SyntheticAccepted (decode 755) 1 0
    connector755 added755 := by decide

def connector756 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added756 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 4, 0], [2, 0]]
theorem accepted756 : SyntheticAccepted (decode 756) 1 2
    connector756 added756 := by decide

def connector757 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added757 : List (List Vertex) := [[2, 7, 3, 6, 1, 0, 4, 5], [2, 6, 0, 5]]
theorem accepted757 : SyntheticAccepted (decode 757) 0 2
    connector757 added757 := by decide

def connector758 : List Vertex := [5, 4, 3, 0, 2, 1, 6]
def added758 : List (List Vertex) := [[3, 6, 2, 7, 4, 0, 1, 5], [3, 7, 0, 5]]
theorem accepted758 : SyntheticAccepted (decode 758) 0 1
    connector758 added758 := by decide

def connector761 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added761 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 4], [1, 0, 3, 7, 4]]
theorem accepted761 : SyntheticAccepted (decode 761) 0 1
    connector761 added761 := by decide

def connector764 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added764 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [1, 7, 3]]
theorem accepted764 : SyntheticAccepted (decode 764) 1 0
    connector764 added764 := by decide

def connector788 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added788 : List (List Vertex) := [[4, 6, 2, 5, 1, 0], [4, 0]]
theorem accepted788 : SyntheticAccepted (decode 788) 1 2
    connector788 added788 := by decide

def connector789 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added789 : List (List Vertex) := [[4, 6, 1, 0, 5, 2], [4, 0, 6, 2]]
theorem accepted789 : SyntheticAccepted (decode 789) 0 2
    connector789 added789 := by decide

def connector790 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added790 : List (List Vertex) := [[4, 7, 0, 1, 6, 2, 5], [4, 0, 5]]
theorem accepted790 : SyntheticAccepted (decode 790) 0 1
    connector790 added790 := by decide

def connector793 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added793 : List (List Vertex) := [[4, 7, 1, 0, 6, 2, 5], [4, 0, 5]]
theorem accepted793 : SyntheticAccepted (decode 793) 1 0
    connector793 added793 := by decide

def connector794 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added794 : List (List Vertex) := [[4, 6, 2, 0, 7, 1, 5], [4, 0, 5]]
theorem accepted794 : SyntheticAccepted (decode 794) 2 0
    connector794 added794 := by decide

def connector795 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added795 : List (List Vertex) := [[4, 6, 0, 2, 5, 1, 7], [4, 0, 7]]
theorem accepted795 : SyntheticAccepted (decode 795) 2 1
    connector795 added795 := by decide

def connector796 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added796 : List (List Vertex) := [[4, 7, 1, 6, 2, 0], [4, 0]]
theorem accepted796 : SyntheticAccepted (decode 796) 1 0
    connector796 added796 := by decide

def connector798 : List Vertex := [7, 4, 3, 0, 1, 2, 6]
def added798 : List (List Vertex) := [[4, 6, 1, 7, 0, 2, 5], [4, 0, 5]]
theorem accepted798 : SyntheticAccepted (decode 798) 2 1
    connector798 added798 := by decide

def connector799 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added799 : List (List Vertex) := [[4, 6, 1, 7, 0, 2], [4, 0, 6, 2]]
theorem accepted799 : SyntheticAccepted (decode 799) 2 0
    connector799 added799 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
