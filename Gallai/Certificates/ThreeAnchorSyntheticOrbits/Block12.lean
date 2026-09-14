/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector858 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added858 : List (List Vertex) := [[2, 6, 3, 5, 1, 0, 4, 7], [2, 5, 0, 7]]
theorem accepted858 : SyntheticAccepted (decode 858) 2 1
    connector858 added858 := by decide

def connector859 : List Vertex := [7, 4, 3, 0, 2, 1, 5]
def added859 : List (List Vertex) := [[3, 5, 2, 6, 4, 0, 1, 7], [3, 6, 0, 7]]
theorem accepted859 : SyntheticAccepted (decode 859) 2 0
    connector859 added859 := by decide

def connector862 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added862 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 4], [1, 0, 3, 6, 4]]
theorem accepted862 : SyntheticAccepted (decode 862) 2 0
    connector862 added862 := by decide

def connector865 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added865 : List (List Vertex) := [[2, 7, 4, 0, 5, 3, 6], [2, 0, 6]]
theorem accepted865 : SyntheticAccepted (decode 865) 0 1
    connector865 added865 := by decide

def connector866 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added866 : List (List Vertex) := [[2, 7, 0, 4, 6, 3, 5], [2, 0, 5]]
theorem accepted866 : SyntheticAccepted (decode 866) 0 2
    connector866 added866 := by decide

def connector867 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added867 : List (List Vertex) := [[2, 5, 3, 0, 7, 4, 6], [2, 0, 6]]
theorem accepted867 : SyntheticAccepted (decode 867) 2 1
    connector867 added867 := by decide

def connector868 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added868 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 4, 0], [1, 0]]
theorem accepted868 : SyntheticAccepted (decode 868) 0 1
    connector868 added868 := by decide

def connector870 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added870 : List (List Vertex) := [[1, 6, 3, 5, 2, 0, 4, 7], [1, 5, 0, 7]]
theorem accepted870 : SyntheticAccepted (decode 870) 2 1
    connector870 added870 := by decide

def connector871 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added871 : List (List Vertex) := [[3, 5, 1, 6, 4, 0, 2, 7], [3, 6, 0, 7]]
theorem accepted871 : SyntheticAccepted (decode 871) 2 0
    connector871 added871 := by decide

def connector872 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added872 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 4, 0], [1, 0]]
theorem accepted872 : SyntheticAccepted (decode 872) 0 2
    connector872 added872 := by decide

def connector873 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added873 : List (List Vertex) := [[3, 5, 1, 7, 4, 6, 0, 2], [3, 0, 5, 2]]
theorem accepted873 : SyntheticAccepted (decode 873) 1 2
    connector873 added873 := by decide

def connector875 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added875 : List (List Vertex) := [[4, 7, 1, 5, 3, 6, 0, 2], [4, 0, 7, 2]]
theorem accepted875 : SyntheticAccepted (decode 875) 1 0
    connector875 added875 := by decide

def connector876 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added876 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 3, 0], [1, 0]]
theorem accepted876 : SyntheticAccepted (decode 876) 2 1
    connector876 added876 := by decide

def connector877 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added877 : List (List Vertex) := [[4, 7, 1, 6, 3, 0, 2, 5], [4, 6, 0, 5]]
theorem accepted877 : SyntheticAccepted (decode 877) 0 2
    connector877 added877 := by decide

def connector878 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added878 : List (List Vertex) := [[1, 6, 4, 7, 2, 0, 3, 5], [1, 7, 0, 5]]
theorem accepted878 : SyntheticAccepted (decode 878) 0 1
    connector878 added878 := by decide

def connector880 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added880 : List (List Vertex) := [[2, 7, 4, 6, 3, 0], [2, 0]]
theorem accepted880 : SyntheticAccepted (decode 880) 1 0
    connector880 added880 := by decide

def connector882 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added882 : List (List Vertex) := [[2, 6, 4, 7, 0, 3, 5], [2, 0, 5]]
theorem accepted882 : SyntheticAccepted (decode 882) 2 1
    connector882 added882 := by decide

def connector883 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added883 : List (List Vertex) := [[2, 6, 4, 7, 0, 3], [2, 0, 6, 3]]
theorem accepted883 : SyntheticAccepted (decode 883) 2 0
    connector883 added883 := by decide

def connector886 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added886 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 3], [1, 0, 4, 6, 3]]
theorem accepted886 : SyntheticAccepted (decode 886) 0 2
    connector886 added886 := by decide

def connector888 : List Vertex := [7, 2, 1, 0, 4, 3, 6]
def added888 : List (List Vertex) := [[2, 6, 4, 7, 1, 5, 3, 0], [2, 0]]
theorem accepted888 : SyntheticAccepted (decode 888) 2 1
    connector888 added888 := by decide

def connector889 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added889 : List (List Vertex) := [[4, 7, 2, 6, 3, 0, 1, 5], [4, 6, 0, 5]]
theorem accepted889 : SyntheticAccepted (decode 889) 0 2
    connector889 added889 := by decide

def connector890 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added890 : List (List Vertex) := [[2, 6, 4, 7, 1, 0, 3, 5], [2, 7, 0, 5]]
theorem accepted890 : SyntheticAccepted (decode 890) 0 1
    connector890 added890 := by decide

def connector892 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added892 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 4], [1, 6, 4]]
theorem accepted892 : SyntheticAccepted (decode 892) 2 0
    connector892 added892 := by decide

def connector901 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added901 : List (List Vertex) := [[1, 6, 0, 4, 7, 3, 5], [1, 0, 5]]
theorem accepted901 : SyntheticAccepted (decode 901) 0 1
    connector901 added901 := by decide

def connector902 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added902 : List (List Vertex) := [[1, 6, 4, 0, 5, 3, 7], [1, 0, 7]]
theorem accepted902 : SyntheticAccepted (decode 902) 0 2
    connector902 added902 := by decide

def connector903 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added903 : List (List Vertex) := [[1, 5, 3, 0, 6, 4, 7], [1, 0, 7]]
theorem accepted903 : SyntheticAccepted (decode 903) 1 2
    connector903 added903 := by decide

def connector904 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added904 : List (List Vertex) := [[1, 5, 3, 7, 4, 0], [1, 0]]
theorem accepted904 : SyntheticAccepted (decode 904) 2 1
    connector904 added904 := by decide

def connector905 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added905 : List (List Vertex) := [[1, 7, 3, 5, 0, 4, 6], [1, 0, 6]]
theorem accepted905 : SyntheticAccepted (decode 905) 0 2
    connector905 added905 := by decide

def connector906 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added906 : List (List Vertex) := [[1, 7, 3, 5, 0, 4], [1, 0, 7, 4]]
theorem accepted906 : SyntheticAccepted (decode 906) 0 1
    connector906 added906 := by decide

def connector908 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added908 : List (List Vertex) := [[1, 6, 4, 7, 3, 0], [1, 0]]
theorem accepted908 : SyntheticAccepted (decode 908) 2 0
    connector908 added908 := by decide

def connector909 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added909 : List (List Vertex) := [[1, 7, 4, 6, 0, 3, 5], [1, 0, 5]]
theorem accepted909 : SyntheticAccepted (decode 909) 1 2
    connector909 added909 := by decide

def connector911 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added911 : List (List Vertex) := [[1, 7, 4, 6, 0, 3], [1, 0, 7, 3]]
theorem accepted911 : SyntheticAccepted (decode 911) 1 0
    connector911 added911 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
