/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail805 : List Vertex := [5, 2, 1, 0, 4, 3]
def added805 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 5, 1], [1, 6, 0, 5]]
theorem accepted805 : OriginalAccepted (decode 805) 1 0 0
    tail805 added805 := by decide

def tail806 : List Vertex := [5, 1, 2, 0, 4, 3]
def added806 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 5, 2], [2, 7, 0, 5]]
theorem accepted806 : OriginalAccepted (decode 806) 2 0 0
    tail806 added806 := by decide

def tail807 : List Vertex := [7, 2, 1, 0, 4, 3]
def added807 : List (List Vertex) := [[3, 0, 2, 5, 1, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted807 : OriginalAccepted (decode 807) 1 2 2
    tail807 added807 := by decide

def tail808 : List Vertex := [7, 2, 1, 0, 4, 3]
def added808 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 4, 6], [7, 6]]
theorem accepted808 : OriginalAccepted (decode 808) 2 1 2
    tail808 added808 := by decide

def tail809 : List Vertex := [5, 2, 1, 0, 4, 3]
def added809 : List (List Vertex) := [[3, 0, 6, 4, 7, 5, 1], [1, 7, 2, 0, 5]]
theorem accepted809 : OriginalAccepted (decode 809) 0 2 0
    tail809 added809 := by decide

def tail810 : List Vertex := [7, 2, 1, 0, 4, 3]
def added810 : List (List Vertex) := [[3, 0, 2, 5, 1, 7, 4, 6], [7, 0, 5, 6]]
theorem accepted810 : OriginalAccepted (decode 810) 0 1 2
    tail810 added810 := by decide

def tail812 : List Vertex := [7, 2, 1, 0, 4, 3]
def added812 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7]]
theorem accepted812 : OriginalAccepted (decode 812) 2 0 2
    tail812 added812 := by decide

def tail813 : List Vertex := [5, 2, 1, 0, 4, 3]
def added813 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 6, 0, 5]]
theorem accepted813 : OriginalAccepted (decode 813) 1 2 0
    tail813 added813 := by decide

def tail815 : List Vertex := [7, 2, 1, 0, 4, 3]
def added815 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6, 0, 7]]
theorem accepted815 : OriginalAccepted (decode 815) 1 0 2
    tail815 added815 := by decide

def tail820 : List Vertex := [6, 1, 2, 0, 4, 3]
def added820 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6]]
theorem accepted820 : OriginalAccepted (decode 820) 1 0 1
    tail820 added820 := by decide

def tail822 : List Vertex := [5, 1, 2, 0, 4, 3]
def added822 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 2], [2, 6, 7, 0, 5]]
theorem accepted822 : OriginalAccepted (decode 822) 2 1 0
    tail822 added822 := by decide

def tail823 : List Vertex := [6, 1, 2, 0, 4, 3]
def added823 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7, 0, 6]]
theorem accepted823 : OriginalAccepted (decode 823) 2 0 1
    tail823 added823 := by decide

def tail824 : List Vertex := [7, 1, 2, 0, 4, 3]
def added824 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7]]
theorem accepted824 : OriginalAccepted (decode 824) 2 0 2
    tail824 added824 := by decide

def tail825 : List Vertex := [5, 1, 2, 0, 4, 3]
def added825 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 2], [2, 7, 6, 0, 5]]
theorem accepted825 : OriginalAccepted (decode 825) 1 2 0
    tail825 added825 := by decide

def tail827 : List Vertex := [7, 1, 2, 0, 4, 3]
def added827 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6, 0, 7]]
theorem accepted827 : OriginalAccepted (decode 827) 1 0 2
    tail827 added827 := by decide

def tail828 : List Vertex := [6, 2, 1, 0, 4, 3]
def added828 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 6]]
theorem accepted828 : OriginalAccepted (decode 828) 1 2 1
    tail828 added828 := by decide

def tail829 : List Vertex := [6, 2, 1, 0, 4, 3]
def added829 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [1, 7, 5, 0, 6]]
theorem accepted829 : OriginalAccepted (decode 829) 0 2 1
    tail829 added829 := by decide

def tail830 : List Vertex := [7, 2, 1, 0, 4, 3]
def added830 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [1, 6, 5, 0, 7]]
theorem accepted830 : OriginalAccepted (decode 830) 0 1 2
    tail830 added830 := by decide

def tail836 : List Vertex := [6, 4, 3, 0, 1, 2]
def added836 : List (List Vertex) := [[2, 0, 4, 7, 6, 1, 5, 3], [3, 6]]
theorem accepted836 : OriginalAccepted (decode 836) 1 2 1
    tail836 added836 := by decide

def tail837 : List Vertex := [6, 4, 3, 0, 1, 2]
def added837 : List (List Vertex) := [[2, 0, 4, 7, 5, 1, 6, 3], [3, 5, 0, 6]]
theorem accepted837 : OriginalAccepted (decode 837) 0 2 1
    tail837 added837 := by decide

def tail838 : List Vertex := [7, 4, 3, 0, 1, 2]
def added838 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 5, 0, 7]]
theorem accepted838 : OriginalAccepted (decode 838) 0 1 2
    tail838 added838 := by decide

def tail841 : List Vertex := [6, 4, 3, 0, 1, 2]
def added841 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted841 : OriginalAccepted (decode 841) 0 1 1
    tail841 added841 := by decide

def tail842 : List Vertex := [7, 4, 3, 0, 1, 2]
def added842 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted842 : OriginalAccepted (decode 842) 0 2 2
    tail842 added842 := by decide

def tail843 : List Vertex := [6, 3, 4, 0, 1, 2]
def added843 : List (List Vertex) := [[2, 0, 3, 5, 1, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted843 : OriginalAccepted (decode 843) 2 1 1
    tail843 added843 := by decide

def tail844 : List Vertex := [6, 3, 4, 0, 1, 2]
def added844 : List (List Vertex) := [[2, 0, 3, 5, 6, 1, 7, 4], [4, 6]]
theorem accepted844 : OriginalAccepted (decode 844) 1 0 1
    tail844 added844 := by decide

def tail846 : List Vertex := [5, 3, 4, 0, 1, 2]
def added846 : List (List Vertex) := [[2, 0, 3, 6, 1, 7, 4], [4, 6, 7, 0, 5]]
theorem accepted846 : OriginalAccepted (decode 846) 2 1 0
    tail846 added846 := by decide

def tail847 : List Vertex := [6, 3, 4, 0, 1, 2]
def added847 : List (List Vertex) := [[2, 0, 3, 5, 7, 1, 6, 4], [4, 7, 0, 6]]
theorem accepted847 : OriginalAccepted (decode 847) 2 0 1
    tail847 added847 := by decide

def tail848 : List Vertex := [6, 4, 3, 0, 2, 1]
def added848 : List (List Vertex) := [[1, 0, 4, 7, 6, 2, 5, 3], [3, 6]]
theorem accepted848 : OriginalAccepted (decode 848) 1 2 1
    tail848 added848 := by decide

def tail849 : List Vertex := [6, 4, 3, 0, 2, 1]
def added849 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5, 0, 6]]
theorem accepted849 : OriginalAccepted (decode 849) 0 2 1
    tail849 added849 := by decide

def tail850 : List Vertex := [7, 4, 3, 0, 2, 1]
def added850 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 5, 0, 7]]
theorem accepted850 : OriginalAccepted (decode 850) 0 1 2
    tail850 added850 := by decide

def tail852 : List Vertex := [6, 4, 3, 0, 2, 1]
def added852 : List (List Vertex) := [[1, 0, 4, 7, 5, 2, 6, 3], [3, 5, 1, 6]]
theorem accepted852 : OriginalAccepted (decode 852) 0 2 1
    tail852 added852 := by decide

def tail856 : List Vertex := [6, 4, 3, 0, 1, 2]
def added856 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 4, 0], [6, 5, 2, 0]]
theorem accepted856 : OriginalAccepted (decode 856) 0 1 1
    tail856 added856 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
