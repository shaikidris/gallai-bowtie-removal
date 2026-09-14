/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail858 : List Vertex := [7, 4, 3, 0, 2, 1]
def added858 : List (List Vertex) := [[2, 5, 3, 6, 4, 0, 1, 7], [1, 5, 0, 7, 6, 2]]
theorem accepted858 : OriginalAccepted (decode 858) 2 1 2
    tail858 added858 := by decide

def tail859 : List Vertex := [7, 1, 2, 0, 3, 4]
def added859 : List (List Vertex) := [[3, 6, 2, 5, 1, 0, 4, 7], [4, 6, 0, 7, 5, 3]]
theorem accepted859 : OriginalAccepted (decode 859) 2 0 2
    tail859 added859 := by decide

def tail862 : List Vertex := [5, 3, 4, 0, 2, 1]
def added862 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 0, 3], [3, 6, 1, 0, 7, 5]]
theorem accepted862 : OriginalAccepted (decode 862) 2 0 0
    tail862 added862 := by decide

def tail865 : List Vertex := [6, 4, 3, 0, 2, 1]
def added865 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted865 : OriginalAccepted (decode 865) 0 1 1
    tail865 added865 := by decide

def tail866 : List Vertex := [7, 4, 3, 0, 2, 1]
def added866 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted866 : OriginalAccepted (decode 866) 0 2 2
    tail866 added866 := by decide

def tail867 : List Vertex := [6, 3, 4, 0, 2, 1]
def added867 : List (List Vertex) := [[1, 0, 3, 5, 2, 7, 6, 4], [4, 7, 0, 6]]
theorem accepted867 : OriginalAccepted (decode 867) 2 1 1
    tail867 added867 := by decide

def tail868 : List Vertex := [6, 4, 3, 0, 2, 1]
def added868 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 4, 0], [6, 5, 1, 0]]
theorem accepted868 : OriginalAccepted (decode 868) 0 1 1
    tail868 added868 := by decide

def tail870 : List Vertex := [7, 4, 3, 0, 1, 2]
def added870 : List (List Vertex) := [[1, 5, 3, 6, 4, 0, 2, 7], [2, 5, 0, 7, 6, 1]]
theorem accepted870 : OriginalAccepted (decode 870) 2 1 2
    tail870 added870 := by decide

def tail871 : List Vertex := [7, 2, 1, 0, 3, 4]
def added871 : List (List Vertex) := [[3, 6, 1, 5, 2, 0, 4, 7], [4, 6, 0, 7, 5, 3]]
theorem accepted871 : OriginalAccepted (decode 871) 2 0 2
    tail871 added871 := by decide

def tail872 : List Vertex := [7, 4, 3, 0, 2, 1]
def added872 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 4, 0], [7, 5, 1, 0]]
theorem accepted872 : OriginalAccepted (decode 872) 0 2 2
    tail872 added872 := by decide

def tail873 : List Vertex := [5, 2, 1, 0, 4, 3]
def added873 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 0, 2], [2, 7, 6, 0, 3, 5]]
theorem accepted873 : OriginalAccepted (decode 873) 1 2 0
    tail873 added873 := by decide

def tail875 : List Vertex := [7, 2, 1, 0, 3, 4]
def added875 : List (List Vertex) := [[4, 6, 3, 5, 1, 7, 0, 2], [2, 5, 6, 0, 4, 7]]
theorem accepted875 : OriginalAccepted (decode 875) 1 0 2
    tail875 added875 := by decide

def tail876 : List Vertex := [6, 3, 4, 0, 2, 1]
def added876 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 3, 0], [6, 7, 1, 0]]
theorem accepted876 : OriginalAccepted (decode 876) 2 1 1
    tail876 added876 := by decide

def tail877 : List Vertex := [5, 2, 1, 0, 4, 3]
def added877 : List (List Vertex) := [[4, 6, 1, 7, 2, 0, 3, 5], [3, 6, 0, 5, 7, 4]]
theorem accepted877 : OriginalAccepted (decode 877) 0 2 0
    tail877 added877 := by decide

def tail878 : List Vertex := [5, 3, 4, 0, 1, 2]
def added878 : List (List Vertex) := [[1, 7, 4, 6, 3, 0, 2, 5], [2, 7, 0, 5, 6, 1]]
theorem accepted878 : OriginalAccepted (decode 878) 0 1 0
    tail878 added878 := by decide

def tail880 : List Vertex := [6, 3, 4, 0, 2, 1]
def added880 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6]]
theorem accepted880 : OriginalAccepted (decode 880) 1 0 1
    tail880 added880 := by decide

def tail882 : List Vertex := [5, 3, 4, 0, 2, 1]
def added882 : List (List Vertex) := [[1, 0, 3, 6, 2, 7, 4], [4, 6, 7, 0, 5]]
theorem accepted882 : OriginalAccepted (decode 882) 2 1 0
    tail882 added882 := by decide

def tail883 : List Vertex := [6, 3, 4, 0, 2, 1]
def added883 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7, 0, 6]]
theorem accepted883 : OriginalAccepted (decode 883) 2 0 1
    tail883 added883 := by decide

def tail886 : List Vertex := [7, 4, 3, 0, 2, 1]
def added886 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 0, 4], [4, 6, 1, 0, 5, 7]]
theorem accepted886 : OriginalAccepted (decode 886) 0 2 2
    tail886 added886 := by decide

def tail888 : List Vertex := [6, 3, 4, 0, 1, 2]
def added888 : List (List Vertex) := [[2, 6, 4, 7, 1, 5, 3, 0], [6, 7, 2, 0]]
theorem accepted888 : OriginalAccepted (decode 888) 2 1 1
    tail888 added888 := by decide

def tail889 : List Vertex := [5, 1, 2, 0, 4, 3]
def added889 : List (List Vertex) := [[4, 6, 2, 7, 1, 0, 3, 5], [3, 6, 0, 5, 7, 4]]
theorem accepted889 : OriginalAccepted (decode 889) 0 2 0
    tail889 added889 := by decide

def tail890 : List Vertex := [5, 3, 4, 0, 2, 1]
def added890 : List (List Vertex) := [[2, 7, 4, 6, 3, 0, 1, 5], [1, 7, 0, 5, 6, 2]]
theorem accepted890 : OriginalAccepted (decode 890) 0 1 0
    tail890 added890 := by decide

def tail892 : List Vertex := [6, 3, 4, 0, 2, 1]
def added892 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7, 1, 6]]
theorem accepted892 : OriginalAccepted (decode 892) 2 0 1
    tail892 added892 := by decide

def tail901 : List Vertex := [6, 4, 3, 0, 1, 2]
def added901 : List (List Vertex) := [[2, 0, 4, 7, 3, 5, 6, 1], [1, 5, 0, 6]]
theorem accepted901 : OriginalAccepted (decode 901) 0 1 1
    tail901 added901 := by decide

def tail902 : List Vertex := [7, 4, 3, 0, 1, 2]
def added902 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 7, 3], [3, 5, 0, 7]]
theorem accepted902 : OriginalAccepted (decode 902) 0 2 2
    tail902 added902 := by decide

def tail903 : List Vertex := [7, 3, 4, 0, 1, 2]
def added903 : List (List Vertex) := [[2, 0, 3, 5, 1, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted903 : OriginalAccepted (decode 903) 1 2 2
    tail903 added903 := by decide

def tail904 : List Vertex := [7, 4, 3, 0, 1, 2]
def added904 : List (List Vertex) := [[2, 0, 4, 6, 7, 1, 5, 3], [3, 7]]
theorem accepted904 : OriginalAccepted (decode 904) 2 1 2
    tail904 added904 := by decide

def tail905 : List Vertex := [6, 4, 3, 0, 1, 2]
def added905 : List (List Vertex) := [[2, 0, 4, 7, 1, 5, 3], [3, 7, 5, 0, 6]]
theorem accepted905 : OriginalAccepted (decode 905) 0 2 1
    tail905 added905 := by decide

def tail906 : List Vertex := [7, 4, 3, 0, 1, 2]
def added906 : List (List Vertex) := [[2, 0, 4, 6, 5, 1, 7, 3], [3, 5, 0, 7]]
theorem accepted906 : OriginalAccepted (decode 906) 0 1 2
    tail906 added906 := by decide

def tail908 : List Vertex := [7, 3, 4, 0, 1, 2]
def added908 : List (List Vertex) := [[2, 0, 3, 5, 7, 1, 6, 4], [4, 7]]
theorem accepted908 : OriginalAccepted (decode 908) 2 0 2
    tail908 added908 := by decide

def tail909 : List Vertex := [5, 3, 4, 0, 1, 2]
def added909 : List (List Vertex) := [[2, 0, 3, 7, 1, 6, 4], [4, 7, 6, 0, 5]]
theorem accepted909 : OriginalAccepted (decode 909) 1 2 0
    tail909 added909 := by decide

def tail911 : List Vertex := [7, 3, 4, 0, 1, 2]
def added911 : List (List Vertex) := [[2, 0, 3, 5, 6, 1, 7, 4], [4, 6, 0, 7]]
theorem accepted911 : OriginalAccepted (decode 911) 1 0 2
    tail911 added911 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
