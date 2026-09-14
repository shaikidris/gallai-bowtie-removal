/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail727 : List Vertex := [6, 2, 1, 0, 4, 3]
def added727 : List (List Vertex) := [[3, 7, 4, 5, 1, 6, 0, 2], [2, 5, 7, 0, 3, 6]]
theorem accepted727 : OriginalAccepted (decode 727) 2 0 1
    tail727 added727 := by decide

def tail728 : List Vertex := [7, 3, 4, 0, 2, 1]
def added728 : List (List Vertex) := [[1, 7, 4, 5, 2, 6, 3, 0], [7, 5, 1, 0]]
theorem accepted728 : OriginalAccepted (decode 728) 0 2 2
    tail728 added728 := by decide

def tail729 : List Vertex := [6, 3, 4, 0, 1, 2]
def added729 : List (List Vertex) := [[1, 5, 4, 7, 3, 0, 2, 6], [2, 5, 0, 6, 7, 1]]
theorem accepted729 : OriginalAccepted (decode 729) 1 2 1
    tail729 added729 := by decide

def tail731 : List Vertex := [6, 2, 1, 0, 4, 3]
def added731 : List (List Vertex) := [[4, 7, 1, 5, 2, 0, 3, 6], [3, 7, 0, 6, 5, 4]]
theorem accepted731 : OriginalAccepted (decode 731) 1 0 1
    tail731 added731 := by decide

def tail732 : List Vertex := [7, 4, 3, 0, 2, 1]
def added732 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 4, 0], [7, 6, 1, 0]]
theorem accepted732 : OriginalAccepted (decode 732) 1 2 2
    tail732 added732 := by decide

def tail733 : List Vertex := [5, 4, 3, 0, 1, 2]
def added733 : List (List Vertex) := [[1, 6, 3, 7, 4, 0, 2, 5], [2, 6, 0, 5, 7, 1]]
theorem accepted733 : OriginalAccepted (decode 733) 0 2 0
    tail733 added733 := by decide

def tail734 : List Vertex := [5, 2, 1, 0, 3, 4]
def added734 : List (List Vertex) := [[3, 7, 1, 6, 2, 0, 4, 5], [4, 7, 0, 5, 6, 3]]
theorem accepted734 : OriginalAccepted (decode 734) 0 1 0
    tail734 added734 := by decide

def tail736 : List Vertex := [7, 3, 4, 0, 2, 1]
def added736 : List (List Vertex) := [[1, 0, 3, 6, 7, 2, 5, 4], [4, 7]]
theorem accepted736 : OriginalAccepted (decode 736) 2 1 2
    tail736 added736 := by decide

def tail737 : List Vertex := [6, 3, 4, 0, 2, 1]
def added737 : List (List Vertex) := [[1, 0, 3, 7, 2, 5, 4], [4, 7, 5, 0, 6]]
theorem accepted737 : OriginalAccepted (decode 737) 0 2 1
    tail737 added737 := by decide

def tail738 : List Vertex := [7, 3, 4, 0, 2, 1]
def added738 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5, 0, 7]]
theorem accepted738 : OriginalAccepted (decode 738) 0 1 2
    tail738 added738 := by decide

def tail740 : List Vertex := [7, 3, 4, 0, 1, 2]
def added740 : List (List Vertex) := [[2, 7, 4, 5, 1, 6, 3, 0], [7, 5, 2, 0]]
theorem accepted740 : OriginalAccepted (decode 740) 0 2 2
    tail740 added740 := by decide

def tail741 : List Vertex := [6, 3, 4, 0, 2, 1]
def added741 : List (List Vertex) := [[2, 5, 4, 7, 3, 0, 1, 6], [1, 5, 0, 6, 7, 2]]
theorem accepted741 : OriginalAccepted (decode 741) 1 2 1
    tail741 added741 := by decide

def tail743 : List Vertex := [6, 1, 2, 0, 4, 3]
def added743 : List (List Vertex) := [[4, 7, 2, 5, 1, 0, 3, 6], [3, 7, 0, 6, 5, 4]]
theorem accepted743 : OriginalAccepted (decode 743) 1 0 1
    tail743 added743 := by decide

def tail744 : List Vertex := [7, 3, 4, 0, 2, 1]
def added744 : List (List Vertex) := [[1, 0, 3, 6, 5, 2, 7, 4], [4, 5, 1, 7]]
theorem accepted744 : OriginalAccepted (decode 744) 0 1 2
    tail744 added744 := by decide

def tail749 : List Vertex := [5, 4, 3, 0, 2, 1]
def added749 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 0, 4], [4, 7, 1, 0, 6, 5]]
theorem accepted749 : OriginalAccepted (decode 749) 1 0 0
    tail749 added749 := by decide

def tail752 : List Vertex := [7, 4, 3, 0, 2, 1]
def added752 : List (List Vertex) := [[1, 0, 4, 5, 7, 2, 6, 3], [3, 7]]
theorem accepted752 : OriginalAccepted (decode 752) 2 0 2
    tail752 added752 := by decide

def tail753 : List Vertex := [5, 4, 3, 0, 2, 1]
def added753 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 6, 0, 5]]
theorem accepted753 : OriginalAccepted (decode 753) 1 2 0
    tail753 added753 := by decide

def tail755 : List Vertex := [7, 4, 3, 0, 2, 1]
def added755 : List (List Vertex) := [[1, 0, 4, 5, 6, 2, 7, 3], [3, 6, 0, 7]]
theorem accepted755 : OriginalAccepted (decode 755) 1 0 2
    tail755 added755 := by decide

def tail756 : List Vertex := [7, 4, 3, 0, 1, 2]
def added756 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 4, 0], [7, 6, 2, 0]]
theorem accepted756 : OriginalAccepted (decode 756) 1 2 2
    tail756 added756 := by decide

def tail757 : List Vertex := [5, 4, 3, 0, 2, 1]
def added757 : List (List Vertex) := [[2, 6, 3, 7, 4, 0, 1, 5], [1, 6, 0, 5, 7, 2]]
theorem accepted757 : OriginalAccepted (decode 757) 0 2 0
    tail757 added757 := by decide

def tail758 : List Vertex := [5, 1, 2, 0, 3, 4]
def added758 : List (List Vertex) := [[3, 7, 2, 6, 1, 0, 4, 5], [4, 7, 0, 5, 6, 3]]
theorem accepted758 : OriginalAccepted (decode 758) 0 1 0
    tail758 added758 := by decide

def tail761 : List Vertex := [6, 3, 4, 0, 2, 1]
def added761 : List (List Vertex) := [[1, 5, 4, 7, 2, 6, 0, 3], [3, 7, 1, 0, 5, 6]]
theorem accepted761 : OriginalAccepted (decode 761) 0 1 1
    tail761 added761 := by decide

def tail764 : List Vertex := [7, 4, 3, 0, 2, 1]
def added764 : List (List Vertex) := [[1, 0, 4, 5, 6, 2, 7, 3], [3, 6, 1, 7]]
theorem accepted764 : OriginalAccepted (decode 764) 1 0 2
    tail764 added764 := by decide

def tail788 : List Vertex := [6, 2, 1, 0, 4, 3]
def added788 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 4, 7], [6, 7]]
theorem accepted788 : OriginalAccepted (decode 788) 1 2 1
    tail788 added788 := by decide

def tail789 : List Vertex := [6, 2, 1, 0, 4, 3]
def added789 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 4, 7], [6, 0, 5, 7]]
theorem accepted789 : OriginalAccepted (decode 789) 0 2 1
    tail789 added789 := by decide

def tail790 : List Vertex := [5, 2, 1, 0, 4, 3]
def added790 : List (List Vertex) := [[3, 0, 7, 4, 6, 5, 1], [1, 6, 2, 0, 5]]
theorem accepted790 : OriginalAccepted (decode 790) 0 1 0
    tail790 added790 := by decide

def tail793 : List Vertex := [5, 1, 2, 0, 4, 3]
def added793 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 5, 2], [2, 6, 0, 5]]
theorem accepted793 : OriginalAccepted (decode 793) 1 0 0
    tail793 added793 := by decide

def tail794 : List Vertex := [5, 2, 1, 0, 4, 3]
def added794 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 5, 1], [1, 7, 0, 5]]
theorem accepted794 : OriginalAccepted (decode 794) 2 0 0
    tail794 added794 := by decide

def tail795 : List Vertex := [6, 2, 1, 0, 4, 3]
def added795 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted795 : OriginalAccepted (decode 795) 2 1 1
    tail795 added795 := by decide

def tail796 : List Vertex := [6, 2, 1, 0, 4, 3]
def added796 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6]]
theorem accepted796 : OriginalAccepted (decode 796) 1 0 1
    tail796 added796 := by decide

def tail798 : List Vertex := [5, 2, 1, 0, 4, 3]
def added798 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [1, 6, 7, 0, 5]]
theorem accepted798 : OriginalAccepted (decode 798) 2 1 0
    tail798 added798 := by decide

def tail799 : List Vertex := [6, 2, 1, 0, 4, 3]
def added799 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7, 0, 6]]
theorem accepted799 : OriginalAccepted (decode 799) 2 0 1
    tail799 added799 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
