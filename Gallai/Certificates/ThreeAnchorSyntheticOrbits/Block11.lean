/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector805 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added805 : List (List Vertex) := [[4, 7, 2, 0, 6, 1, 5], [4, 0, 5]]
theorem accepted805 : SyntheticAccepted (decode 805) 1 0
    connector805 added805 := by decide

def connector806 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added806 : List (List Vertex) := [[4, 6, 1, 0, 7, 2, 5], [4, 0, 5]]
theorem accepted806 : SyntheticAccepted (decode 806) 2 0
    connector806 added806 := by decide

def connector807 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added807 : List (List Vertex) := [[4, 7, 0, 2, 5, 1, 6], [4, 0, 6]]
theorem accepted807 : SyntheticAccepted (decode 807) 1 2
    connector807 added807 := by decide

def connector808 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added808 : List (List Vertex) := [[4, 7, 2, 5, 1, 0], [4, 0]]
theorem accepted808 : SyntheticAccepted (decode 808) 2 1
    connector808 added808 := by decide

def connector809 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added809 : List (List Vertex) := [[4, 6, 0, 1, 7, 2, 5], [4, 0, 5]]
theorem accepted809 : SyntheticAccepted (decode 809) 0 2
    connector809 added809 := by decide

def connector810 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added810 : List (List Vertex) := [[4, 7, 1, 0, 5, 2], [4, 0, 7, 2]]
theorem accepted810 : SyntheticAccepted (decode 810) 0 1
    connector810 added810 := by decide

def connector812 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added812 : List (List Vertex) := [[4, 6, 1, 7, 2, 0], [4, 0]]
theorem accepted812 : SyntheticAccepted (decode 812) 2 0
    connector812 added812 := by decide

def connector813 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added813 : List (List Vertex) := [[4, 7, 1, 6, 0, 2, 5], [4, 0, 5]]
theorem accepted813 : SyntheticAccepted (decode 813) 1 2
    connector813 added813 := by decide

def connector815 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added815 : List (List Vertex) := [[4, 7, 1, 6, 0, 2], [4, 0, 7, 2]]
theorem accepted815 : SyntheticAccepted (decode 815) 1 0
    connector815 added815 := by decide

def connector820 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added820 : List (List Vertex) := [[4, 7, 2, 6, 1, 0], [4, 0]]
theorem accepted820 : SyntheticAccepted (decode 820) 1 0
    connector820 added820 := by decide

def connector822 : List Vertex := [7, 4, 3, 0, 2, 1, 6]
def added822 : List (List Vertex) := [[4, 6, 2, 7, 0, 1, 5], [4, 0, 5]]
theorem accepted822 : SyntheticAccepted (decode 822) 2 1
    connector822 added822 := by decide

def connector823 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added823 : List (List Vertex) := [[4, 6, 2, 7, 0, 1], [4, 0, 6, 1]]
theorem accepted823 : SyntheticAccepted (decode 823) 2 0
    connector823 added823 := by decide

def connector824 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added824 : List (List Vertex) := [[4, 6, 2, 7, 1, 0], [4, 0]]
theorem accepted824 : SyntheticAccepted (decode 824) 2 0
    connector824 added824 := by decide

def connector825 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added825 : List (List Vertex) := [[4, 7, 2, 6, 0, 1, 5], [4, 0, 5]]
theorem accepted825 : SyntheticAccepted (decode 825) 1 2
    connector825 added825 := by decide

def connector827 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added827 : List (List Vertex) := [[4, 7, 2, 6, 0, 1], [4, 0, 7, 1]]
theorem accepted827 : SyntheticAccepted (decode 827) 1 0
    connector827 added827 := by decide

def connector828 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added828 : List (List Vertex) := [[4, 7, 1, 6, 2, 0], [4, 0]]
theorem accepted828 : SyntheticAccepted (decode 828) 1 2
    connector828 added828 := by decide

def connector829 : List Vertex := [5, 0, 3, 4, 7]
def added829 : List (List Vertex) := [[4, 6, 1, 0, 2, 7], [4, 0, 6, 2, 1, 7]]
theorem accepted829 : SyntheticAccepted (decode 829) 0 2
    connector829 added829 := by decide

def connector830 : List Vertex := [5, 0, 3, 4, 6]
def added830 : List (List Vertex) := [[4, 7, 1, 0, 2, 6], [4, 0, 7, 2, 1, 6]]
theorem accepted830 : SyntheticAccepted (decode 830) 0 1
    connector830 added830 := by decide

def connector836 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added836 : List (List Vertex) := [[1, 5, 3, 6, 4, 0], [1, 0]]
theorem accepted836 : SyntheticAccepted (decode 836) 1 2
    connector836 added836 := by decide

def connector837 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added837 : List (List Vertex) := [[1, 6, 3, 5, 0, 4], [1, 0, 6, 4]]
theorem accepted837 : SyntheticAccepted (decode 837) 0 2
    connector837 added837 := by decide

def connector838 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added838 : List (List Vertex) := [[1, 6, 3, 5, 0, 4, 7], [1, 0, 7]]
theorem accepted838 : SyntheticAccepted (decode 838) 0 1
    connector838 added838 := by decide

def connector841 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added841 : List (List Vertex) := [[1, 7, 4, 0, 5, 3, 6], [1, 0, 6]]
theorem accepted841 : SyntheticAccepted (decode 841) 0 1
    connector841 added841 := by decide

def connector842 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added842 : List (List Vertex) := [[1, 7, 0, 4, 6, 3, 5], [1, 0, 5]]
theorem accepted842 : SyntheticAccepted (decode 842) 0 2
    connector842 added842 := by decide

def connector843 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added843 : List (List Vertex) := [[1, 5, 3, 0, 7, 4, 6], [1, 0, 6]]
theorem accepted843 : SyntheticAccepted (decode 843) 2 1
    connector843 added843 := by decide

def connector844 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added844 : List (List Vertex) := [[1, 7, 4, 6, 3, 0], [1, 0]]
theorem accepted844 : SyntheticAccepted (decode 844) 1 0
    connector844 added844 := by decide

def connector846 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added846 : List (List Vertex) := [[1, 6, 4, 7, 0, 3, 5], [1, 0, 5]]
theorem accepted846 : SyntheticAccepted (decode 846) 2 1
    connector846 added846 := by decide

def connector847 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added847 : List (List Vertex) := [[1, 6, 4, 7, 0, 3], [1, 0, 6, 3]]
theorem accepted847 : SyntheticAccepted (decode 847) 2 0
    connector847 added847 := by decide

def connector848 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added848 : List (List Vertex) := [[2, 5, 3, 6, 4, 0], [2, 0]]
theorem accepted848 : SyntheticAccepted (decode 848) 1 2
    connector848 added848 := by decide

def connector849 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added849 : List (List Vertex) := [[2, 6, 3, 5, 0, 4], [2, 0, 6, 4]]
theorem accepted849 : SyntheticAccepted (decode 849) 0 2
    connector849 added849 := by decide

def connector850 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added850 : List (List Vertex) := [[2, 6, 3, 5, 0, 4, 7], [2, 0, 7]]
theorem accepted850 : SyntheticAccepted (decode 850) 0 1
    connector850 added850 := by decide

def connector852 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added852 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [1, 6, 3]]
theorem accepted852 : SyntheticAccepted (decode 852) 0 2
    connector852 added852 := by decide

def connector856 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added856 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 4, 0], [2, 0]]
theorem accepted856 : SyntheticAccepted (decode 856) 0 1
    connector856 added856 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
