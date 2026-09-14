/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail969 : List Vertex := [6, 4, 3, 0, 1, 2]
def added969 : List (List Vertex) := [[2, 0, 5, 1, 7, 6, 3], [3, 7, 4, 0, 6]]
theorem accepted969 : OriginalAccepted (decode 969) 1 2 1
    tail969 added969 := by decide

def tail971 : List Vertex := [7, 4, 3, 0, 1, 2]
def added971 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 1, 5], [7, 0, 6, 5]]
theorem accepted971 : OriginalAccepted (decode 971) 1 0 2
    tail971 added971 := by decide

def tail972 : List Vertex := [6, 4, 3, 0, 1, 2]
def added972 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 6]]
theorem accepted972 : OriginalAccepted (decode 972) 1 2 1
    tail972 added972 := by decide

def tail973 : List Vertex := [6, 4, 3, 0, 1, 2]
def added973 : List (List Vertex) := [[2, 0, 4, 7, 1, 6, 3], [3, 7, 5, 0, 6]]
theorem accepted973 : OriginalAccepted (decode 973) 0 2 1
    tail973 added973 := by decide

def tail974 : List Vertex := [7, 4, 3, 0, 1, 2]
def added974 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 3], [3, 6, 5, 0, 7]]
theorem accepted974 : OriginalAccepted (decode 974) 0 1 2
    tail974 added974 := by decide

def tail976 : List Vertex := [6, 4, 3, 0, 2, 1]
def added976 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 2, 5], [6, 5]]
theorem accepted976 : OriginalAccepted (decode 976) 1 0 1
    tail976 added976 := by decide

def tail978 : List Vertex := [7, 4, 3, 0, 2, 1]
def added978 : List (List Vertex) := [[1, 0, 5, 2, 6, 7, 3], [3, 6, 4, 0, 7]]
theorem accepted978 : OriginalAccepted (decode 978) 2 1 2
    tail978 added978 := by decide

def tail979 : List Vertex := [6, 4, 3, 0, 2, 1]
def added979 : List (List Vertex) := [[1, 0, 4, 7, 3, 6, 2, 5], [6, 0, 7, 5]]
theorem accepted979 : OriginalAccepted (decode 979) 2 0 1
    tail979 added979 := by decide

def tail982 : List Vertex := [7, 4, 3, 0, 2, 1]
def added982 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 0, 4], [4, 6, 1, 0, 5, 7]]
theorem accepted982 : OriginalAccepted (decode 982) 0 2 2
    tail982 added982 := by decide

def tail984 : List Vertex := [6, 2, 1, 0, 4, 3]
def added984 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 2, 0], [6, 7, 3, 0]]
theorem accepted984 : OriginalAccepted (decode 984) 2 1 1
    tail984 added984 := by decide

def tail985 : List Vertex := [6, 4, 3, 0, 1, 2]
def added985 : List (List Vertex) := [[2, 5, 1, 7, 3, 6, 0, 4], [4, 7, 5, 0, 2, 6]]
theorem accepted985 : OriginalAccepted (decode 985) 0 2 1
    tail985 added985 := by decide

def tail986 : List Vertex := [7, 4, 3, 0, 2, 1]
def added986 : List (List Vertex) := [[1, 5, 2, 6, 3, 7, 0, 4], [4, 6, 5, 0, 1, 7]]
theorem accepted986 : OriginalAccepted (decode 986) 0 1 2
    tail986 added986 := by decide

def tail988 : List Vertex := [6, 2, 1, 0, 4, 3]
def added988 : List (List Vertex) := [[3, 0, 2, 5, 7, 4, 6, 1], [1, 7, 3, 6]]
theorem accepted988 : OriginalAccepted (decode 988) 2 0 1
    tail988 added988 := by decide

def tail992 : List Vertex := [7, 4, 3, 0, 2, 1]
def added992 : List (List Vertex) := [[1, 0, 4, 6, 3, 7, 2, 5], [7, 5]]
theorem accepted992 : OriginalAccepted (decode 992) 2 0 2
    tail992 added992 := by decide

def tail993 : List Vertex := [6, 4, 3, 0, 2, 1]
def added993 : List (List Vertex) := [[1, 0, 5, 2, 7, 6, 3], [3, 7, 4, 0, 6]]
theorem accepted993 : OriginalAccepted (decode 993) 1 2 1
    tail993 added993 := by decide

def tail995 : List Vertex := [7, 4, 3, 0, 2, 1]
def added995 : List (List Vertex) := [[1, 0, 4, 6, 3, 7, 2, 5], [7, 0, 6, 5]]
theorem accepted995 : OriginalAccepted (decode 995) 1 0 2
    tail995 added995 := by decide

def tail996 : List Vertex := [7, 2, 1, 0, 4, 3]
def added996 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 2, 0], [7, 6, 3, 0]]
theorem accepted996 : OriginalAccepted (decode 996) 1 2 2
    tail996 added996 := by decide

def tail997 : List Vertex := [6, 4, 3, 0, 2, 1]
def added997 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 0, 4], [4, 7, 5, 0, 1, 6]]
theorem accepted997 : OriginalAccepted (decode 997) 0 2 1
    tail997 added997 := by decide

def tail998 : List Vertex := [7, 4, 3, 0, 1, 2]
def added998 : List (List Vertex) := [[2, 5, 1, 6, 3, 7, 0, 4], [4, 6, 5, 0, 2, 7]]
theorem accepted998 : OriginalAccepted (decode 998) 0 1 2
    tail998 added998 := by decide

def tail1001 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1001 : List (List Vertex) := [[1, 5, 2, 7, 3, 6, 0, 4], [4, 7, 1, 0, 5, 6]]
theorem accepted1001 : OriginalAccepted (decode 1001) 0 1 1
    tail1001 added1001 := by decide

def tail1004 : List Vertex := [7, 2, 1, 0, 4, 3]
def added1004 : List (List Vertex) := [[3, 0, 2, 5, 6, 4, 7, 1], [1, 6, 3, 7]]
theorem accepted1004 : OriginalAccepted (decode 1004) 1 0 2
    tail1004 added1004 := by decide

def tail1008 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1008 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 6]]
theorem accepted1008 : OriginalAccepted (decode 1008) 1 2 1
    tail1008 added1008 := by decide

def tail1009 : List Vertex := [6, 4, 3, 0, 2, 1]
def added1009 : List (List Vertex) := [[1, 0, 4, 7, 2, 6, 3], [3, 7, 5, 0, 6]]
theorem accepted1009 : OriginalAccepted (decode 1009) 0 2 1
    tail1009 added1009 := by decide

def tail1010 : List Vertex := [7, 4, 3, 0, 2, 1]
def added1010 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 3], [3, 6, 5, 0, 7]]
theorem accepted1010 : OriginalAccepted (decode 1010) 0 1 2
    tail1010 added1010 := by decide

def tail1012 : List Vertex := [6, 1, 2, 0, 4, 3]
def added1012 : List (List Vertex) := [[3, 0, 1, 5, 7, 4, 6, 2], [2, 7, 3, 6]]
theorem accepted1012 : OriginalAccepted (decode 1012) 2 0 1
    tail1012 added1012 := by decide

def tail1016 : List Vertex := [7, 1, 2, 0, 4, 3]
def added1016 : List (List Vertex) := [[3, 0, 1, 5, 6, 4, 7, 2], [2, 6, 3, 7]]
theorem accepted1016 : OriginalAccepted (decode 1016) 1 0 2
    tail1016 added1016 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
