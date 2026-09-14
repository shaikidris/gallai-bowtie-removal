/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector969 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added969 : List (List Vertex) := [[1, 5, 0, 3, 7, 4, 6], [1, 0, 6]]
theorem accepted969 : SyntheticAccepted (decode 969) 1 2
    connector969 added969 := by decide

def connector971 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added971 : List (List Vertex) := [[1, 7, 3, 0, 6, 4], [1, 0, 7, 4]]
theorem accepted971 : SyntheticAccepted (decode 971) 1 0
    connector971 added971 := by decide

def connector972 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added972 : List (List Vertex) := [[1, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted972 : SyntheticAccepted (decode 972) 1 2
    connector972 added972 := by decide

def connector973 : List Vertex := [5, 0, 2, 1, 7]
def added973 : List (List Vertex) := [[1, 6, 3, 0, 4, 7], [1, 0, 6, 4, 3, 7]]
theorem accepted973 : SyntheticAccepted (decode 973) 0 2
    connector973 added973 := by decide

def connector974 : List Vertex := [5, 0, 2, 1, 6]
def added974 : List (List Vertex) := [[1, 7, 3, 0, 4, 6], [1, 0, 7, 4, 3, 6]]
theorem accepted974 : SyntheticAccepted (decode 974) 0 1
    connector974 added974 := by decide

def connector976 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added976 : List (List Vertex) := [[2, 6, 4, 7, 3, 0], [2, 0]]
theorem accepted976 : SyntheticAccepted (decode 976) 1 0
    connector976 added976 := by decide

def connector978 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added978 : List (List Vertex) := [[2, 5, 0, 3, 6, 4, 7], [2, 0, 7]]
theorem accepted978 : SyntheticAccepted (decode 978) 2 1
    connector978 added978 := by decide

def connector979 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added979 : List (List Vertex) := [[2, 6, 3, 0, 7, 4], [2, 0, 6, 4]]
theorem accepted979 : SyntheticAccepted (decode 979) 2 0
    connector979 added979 := by decide

def connector982 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added982 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 3], [1, 0, 4, 6, 3]]
theorem accepted982 : SyntheticAccepted (decode 982) 0 2
    connector982 added982 := by decide

def connector984 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added984 : List (List Vertex) := [[3, 6, 4, 7, 1, 5, 2, 0], [3, 0]]
theorem accepted984 : SyntheticAccepted (decode 984) 2 1
    connector984 added984 := by decide

def connector985 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added985 : List (List Vertex) := [[2, 6, 3, 7, 1, 5, 0, 4], [2, 0, 6, 4]]
theorem accepted985 : SyntheticAccepted (decode 985) 0 2
    connector985 added985 := by decide

def connector986 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added986 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 0, 4], [1, 0, 7, 4]]
theorem accepted986 : SyntheticAccepted (decode 986) 0 1
    connector986 added986 := by decide

def connector988 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added988 : List (List Vertex) := [[3, 0, 2, 6, 4, 7, 1], [3, 6, 1]]
theorem accepted988 : SyntheticAccepted (decode 988) 2 0
    connector988 added988 := by decide

def connector992 : List Vertex := [7, 3, 4, 0, 1, 2, 5]
def added992 : List (List Vertex) := [[2, 7, 4, 6, 3, 0], [2, 0]]
theorem accepted992 : SyntheticAccepted (decode 992) 2 0
    connector992 added992 := by decide

def connector993 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added993 : List (List Vertex) := [[2, 5, 0, 3, 7, 4, 6], [2, 0, 6]]
theorem accepted993 : SyntheticAccepted (decode 993) 1 2
    connector993 added993 := by decide

def connector995 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added995 : List (List Vertex) := [[2, 7, 3, 0, 6, 4], [2, 0, 7, 4]]
theorem accepted995 : SyntheticAccepted (decode 995) 1 0
    connector995 added995 := by decide

def connector996 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added996 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted996 : SyntheticAccepted (decode 996) 1 2
    connector996 added996 := by decide

def connector997 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added997 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 0, 4], [1, 0, 6, 4]]
theorem accepted997 : SyntheticAccepted (decode 997) 0 2
    connector997 added997 := by decide

def connector998 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added998 : List (List Vertex) := [[2, 7, 3, 6, 1, 5, 0, 4], [2, 0, 7, 4]]
theorem accepted998 : SyntheticAccepted (decode 998) 0 1
    connector998 added998 := by decide

def connector1001 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added1001 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 3], [1, 0, 4, 7, 3]]
theorem accepted1001 : SyntheticAccepted (decode 1001) 0 1
    connector1001 added1001 := by decide

def connector1004 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added1004 : List (List Vertex) := [[3, 0, 2, 7, 4, 6, 1], [3, 7, 1]]
theorem accepted1004 : SyntheticAccepted (decode 1004) 1 0
    connector1004 added1004 := by decide

def connector1008 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added1008 : List (List Vertex) := [[2, 7, 3, 6, 4, 0], [2, 0]]
theorem accepted1008 : SyntheticAccepted (decode 1008) 1 2
    connector1008 added1008 := by decide

def connector1009 : List Vertex := [5, 0, 1, 2, 7]
def added1009 : List (List Vertex) := [[2, 6, 3, 0, 4, 7], [2, 0, 6, 4, 3, 7]]
theorem accepted1009 : SyntheticAccepted (decode 1009) 0 2
    connector1009 added1009 := by decide

def connector1010 : List Vertex := [5, 0, 1, 2, 6]
def added1010 : List (List Vertex) := [[2, 7, 3, 0, 4, 6], [2, 0, 7, 4, 3, 6]]
theorem accepted1010 : SyntheticAccepted (decode 1010) 0 1
    connector1010 added1010 := by decide

def connector1012 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added1012 : List (List Vertex) := [[3, 0, 1, 6, 4, 7, 2], [3, 6, 2]]
theorem accepted1012 : SyntheticAccepted (decode 1012) 2 0
    connector1012 added1012 := by decide

def connector1016 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added1016 : List (List Vertex) := [[3, 0, 1, 7, 4, 6, 2], [3, 7, 2]]
theorem accepted1016 : SyntheticAccepted (decode 1016) 1 0
    connector1016 added1016 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
