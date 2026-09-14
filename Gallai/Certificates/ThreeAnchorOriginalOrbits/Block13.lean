/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail913 : List Vertex := [6, 4, 3, 0, 2, 1]
def added913 : List (List Vertex) := [[1, 0, 4, 7, 3, 5, 6, 2], [2, 5, 0, 6]]
theorem accepted913 : OriginalAccepted (decode 913) 0 1 1
    tail913 added913 := by decide

def tail914 : List Vertex := [7, 4, 3, 0, 2, 1]
def added914 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 7, 3], [3, 5, 0, 7]]
theorem accepted914 : OriginalAccepted (decode 914) 0 2 2
    tail914 added914 := by decide

def tail915 : List Vertex := [7, 3, 4, 0, 2, 1]
def added915 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 7, 4], [4, 6, 0, 7]]
theorem accepted915 : OriginalAccepted (decode 915) 1 2 2
    tail915 added915 := by decide

def tail916 : List Vertex := [6, 4, 3, 0, 2, 1]
def added916 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 4, 0], [6, 5, 1, 0]]
theorem accepted916 : OriginalAccepted (decode 916) 0 1 1
    tail916 added916 := by decide

def tail918 : List Vertex := [5, 2, 1, 0, 4, 3]
def added918 : List (List Vertex) := [[3, 7, 4, 6, 1, 5, 0, 2], [2, 6, 7, 0, 3, 5]]
theorem accepted918 : OriginalAccepted (decode 918) 2 1 0
    tail918 added918 := by decide

def tail919 : List Vertex := [6, 2, 1, 0, 3, 4]
def added919 : List (List Vertex) := [[4, 7, 3, 5, 1, 6, 0, 2], [2, 5, 7, 0, 4, 6]]
theorem accepted919 : OriginalAccepted (decode 919) 2 0 1
    tail919 added919 := by decide

def tail920 : List Vertex := [7, 4, 3, 0, 2, 1]
def added920 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 4, 0], [7, 5, 1, 0]]
theorem accepted920 : OriginalAccepted (decode 920) 0 2 2
    tail920 added920 := by decide

def tail921 : List Vertex := [6, 4, 3, 0, 1, 2]
def added921 : List (List Vertex) := [[1, 5, 3, 7, 4, 0, 2, 6], [2, 5, 0, 6, 7, 1]]
theorem accepted921 : OriginalAccepted (decode 921) 1 2 1
    tail921 added921 := by decide

def tail923 : List Vertex := [6, 2, 1, 0, 3, 4]
def added923 : List (List Vertex) := [[3, 7, 1, 5, 2, 0, 4, 6], [4, 7, 0, 6, 5, 3]]
theorem accepted923 : OriginalAccepted (decode 923) 1 0 1
    tail923 added923 := by decide

def tail924 : List Vertex := [7, 3, 4, 0, 2, 1]
def added924 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 3, 0], [7, 6, 1, 0]]
theorem accepted924 : OriginalAccepted (decode 924) 1 2 2
    tail924 added924 := by decide

def tail925 : List Vertex := [5, 3, 4, 0, 1, 2]
def added925 : List (List Vertex) := [[1, 6, 4, 7, 3, 0, 2, 5], [2, 6, 0, 5, 7, 1]]
theorem accepted925 : OriginalAccepted (decode 925) 0 2 0
    tail925 added925 := by decide

def tail926 : List Vertex := [5, 2, 1, 0, 4, 3]
def added926 : List (List Vertex) := [[4, 7, 1, 6, 2, 0, 3, 5], [3, 7, 0, 5, 6, 4]]
theorem accepted926 : OriginalAccepted (decode 926) 0 1 0
    tail926 added926 := by decide

def tail928 : List Vertex := [7, 4, 3, 0, 2, 1]
def added928 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7]]
theorem accepted928 : OriginalAccepted (decode 928) 2 1 2
    tail928 added928 := by decide

def tail929 : List Vertex := [6, 4, 3, 0, 2, 1]
def added929 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [3, 7, 5, 0, 6]]
theorem accepted929 : OriginalAccepted (decode 929) 0 2 1
    tail929 added929 := by decide

def tail930 : List Vertex := [7, 4, 3, 0, 2, 1]
def added930 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5, 0, 7]]
theorem accepted930 : OriginalAccepted (decode 930) 0 1 2
    tail930 added930 := by decide

def tail932 : List Vertex := [7, 4, 3, 0, 1, 2]
def added932 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 4, 0], [7, 5, 2, 0]]
theorem accepted932 : OriginalAccepted (decode 932) 0 2 2
    tail932 added932 := by decide

def tail933 : List Vertex := [6, 4, 3, 0, 2, 1]
def added933 : List (List Vertex) := [[2, 5, 3, 7, 4, 0, 1, 6], [1, 5, 0, 6, 7, 2]]
theorem accepted933 : OriginalAccepted (decode 933) 1 2 1
    tail933 added933 := by decide

def tail935 : List Vertex := [6, 1, 2, 0, 3, 4]
def added935 : List (List Vertex) := [[3, 7, 2, 5, 1, 0, 4, 6], [4, 7, 0, 6, 5, 3]]
theorem accepted935 : OriginalAccepted (decode 935) 1 0 1
    tail935 added935 := by decide

def tail936 : List Vertex := [7, 4, 3, 0, 2, 1]
def added936 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5, 1, 7]]
theorem accepted936 : OriginalAccepted (decode 936) 0 1 2
    tail936 added936 := by decide

def tail941 : List Vertex := [5, 3, 4, 0, 2, 1]
def added941 : List (List Vertex) := [[1, 6, 4, 7, 2, 5, 0, 3], [3, 7, 1, 0, 6, 5]]
theorem accepted941 : OriginalAccepted (decode 941) 1 0 0
    tail941 added941 := by decide

def tail944 : List Vertex := [7, 3, 4, 0, 2, 1]
def added944 : List (List Vertex) := [[1, 0, 3, 5, 7, 2, 6, 4], [4, 7]]
theorem accepted944 : OriginalAccepted (decode 944) 2 0 2
    tail944 added944 := by decide

def tail945 : List Vertex := [5, 3, 4, 0, 2, 1]
def added945 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 4], [4, 7, 6, 0, 5]]
theorem accepted945 : OriginalAccepted (decode 945) 1 2 0
    tail945 added945 := by decide

def tail947 : List Vertex := [7, 3, 4, 0, 2, 1]
def added947 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6, 0, 7]]
theorem accepted947 : OriginalAccepted (decode 947) 1 0 2
    tail947 added947 := by decide

def tail948 : List Vertex := [7, 3, 4, 0, 1, 2]
def added948 : List (List Vertex) := [[2, 7, 4, 6, 1, 5, 3, 0], [7, 6, 2, 0]]
theorem accepted948 : OriginalAccepted (decode 948) 1 2 2
    tail948 added948 := by decide

def tail949 : List Vertex := [5, 3, 4, 0, 2, 1]
def added949 : List (List Vertex) := [[2, 6, 4, 7, 3, 0, 1, 5], [1, 6, 0, 5, 7, 2]]
theorem accepted949 : OriginalAccepted (decode 949) 0 2 0
    tail949 added949 := by decide

def tail950 : List Vertex := [5, 1, 2, 0, 4, 3]
def added950 : List (List Vertex) := [[4, 7, 2, 6, 1, 0, 3, 5], [3, 7, 0, 5, 6, 4]]
theorem accepted950 : OriginalAccepted (decode 950) 0 1 0
    tail950 added950 := by decide

def tail953 : List Vertex := [6, 4, 3, 0, 2, 1]
def added953 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 0, 4], [4, 7, 1, 0, 5, 6]]
theorem accepted953 : OriginalAccepted (decode 953) 0 1 1
    tail953 added953 := by decide

def tail956 : List Vertex := [7, 3, 4, 0, 2, 1]
def added956 : List (List Vertex) := [[1, 0, 3, 5, 6, 2, 7, 4], [4, 6, 1, 7]]
theorem accepted956 : OriginalAccepted (decode 956) 1 0 2
    tail956 added956 := by decide

def tail964 : List Vertex := [6, 4, 3, 0, 1, 2]
def added964 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 1, 5], [6, 5]]
theorem accepted964 : OriginalAccepted (decode 964) 1 0 1
    tail964 added964 := by decide

def tail966 : List Vertex := [7, 4, 3, 0, 1, 2]
def added966 : List (List Vertex) := [[2, 0, 5, 1, 6, 7, 3], [3, 6, 4, 0, 7]]
theorem accepted966 : OriginalAccepted (decode 966) 2 1 2
    tail966 added966 := by decide

def tail967 : List Vertex := [6, 4, 3, 0, 1, 2]
def added967 : List (List Vertex) := [[2, 0, 4, 7, 3, 6, 1, 5], [6, 0, 7, 5]]
theorem accepted967 : OriginalAccepted (decode 967) 2 0 1
    tail967 added967 := by decide

def tail968 : List Vertex := [7, 4, 3, 0, 1, 2]
def added968 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 1, 5], [7, 5]]
theorem accepted968 : OriginalAccepted (decode 968) 2 0 2
    tail968 added968 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
