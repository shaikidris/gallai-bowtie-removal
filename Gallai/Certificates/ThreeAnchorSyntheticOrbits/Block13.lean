/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector913 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added913 : List (List Vertex) := [[2, 6, 0, 4, 7, 3, 5], [2, 0, 5]]
theorem accepted913 : SyntheticAccepted (decode 913) 0 1
    connector913 added913 := by decide

def connector914 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added914 : List (List Vertex) := [[2, 6, 4, 0, 5, 3, 7], [2, 0, 7]]
theorem accepted914 : SyntheticAccepted (decode 914) 0 2
    connector914 added914 := by decide

def connector915 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added915 : List (List Vertex) := [[2, 5, 3, 0, 6, 4, 7], [2, 0, 7]]
theorem accepted915 : SyntheticAccepted (decode 915) 1 2
    connector915 added915 := by decide

def connector916 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added916 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 4, 0], [1, 0]]
theorem accepted916 : SyntheticAccepted (decode 916) 0 1
    connector916 added916 := by decide

def connector918 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added918 : List (List Vertex) := [[3, 5, 1, 6, 4, 7, 0, 2], [3, 0, 5, 2]]
theorem accepted918 : SyntheticAccepted (decode 918) 2 1
    connector918 added918 := by decide

def connector919 : List Vertex := [7, 4, 3, 0, 1, 2, 5]
def added919 : List (List Vertex) := [[4, 6, 1, 5, 3, 7, 0, 2], [4, 0, 6, 2]]
theorem accepted919 : SyntheticAccepted (decode 919) 2 0
    connector919 added919 := by decide

def connector920 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added920 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 4, 0], [1, 0]]
theorem accepted920 : SyntheticAccepted (decode 920) 0 2
    connector920 added920 := by decide

def connector921 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added921 : List (List Vertex) := [[1, 7, 3, 5, 2, 0, 4, 6], [1, 5, 0, 6]]
theorem accepted921 : SyntheticAccepted (decode 921) 1 2
    connector921 added921 := by decide

def connector923 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added923 : List (List Vertex) := [[3, 5, 1, 7, 4, 0, 2, 6], [3, 7, 0, 6]]
theorem accepted923 : SyntheticAccepted (decode 923) 1 0
    connector923 added923 := by decide

def connector924 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added924 : List (List Vertex) := [[1, 7, 4, 6, 2, 5, 3, 0], [1, 0]]
theorem accepted924 : SyntheticAccepted (decode 924) 1 2
    connector924 added924 := by decide

def connector925 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added925 : List (List Vertex) := [[1, 7, 4, 6, 2, 0, 3, 5], [1, 6, 0, 5]]
theorem accepted925 : SyntheticAccepted (decode 925) 0 2
    connector925 added925 := by decide

def connector926 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added926 : List (List Vertex) := [[4, 6, 1, 7, 3, 0, 2, 5], [4, 7, 0, 5]]
theorem accepted926 : SyntheticAccepted (decode 926) 0 1
    connector926 added926 := by decide

def connector928 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added928 : List (List Vertex) := [[2, 5, 3, 7, 4, 0], [2, 0]]
theorem accepted928 : SyntheticAccepted (decode 928) 2 1
    connector928 added928 := by decide

def connector929 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added929 : List (List Vertex) := [[2, 7, 3, 5, 0, 4, 6], [2, 0, 6]]
theorem accepted929 : SyntheticAccepted (decode 929) 0 2
    connector929 added929 := by decide

def connector930 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added930 : List (List Vertex) := [[2, 7, 3, 5, 0, 4], [2, 0, 7, 4]]
theorem accepted930 : SyntheticAccepted (decode 930) 0 1
    connector930 added930 := by decide

def connector932 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added932 : List (List Vertex) := [[2, 7, 3, 5, 1, 6, 4, 0], [2, 0]]
theorem accepted932 : SyntheticAccepted (decode 932) 0 2
    connector932 added932 := by decide

def connector933 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added933 : List (List Vertex) := [[2, 7, 3, 5, 1, 0, 4, 6], [2, 5, 0, 6]]
theorem accepted933 : SyntheticAccepted (decode 933) 1 2
    connector933 added933 := by decide

def connector935 : List Vertex := [6, 4, 3, 0, 2, 1, 5]
def added935 : List (List Vertex) := [[3, 5, 2, 7, 4, 0, 1, 6], [3, 7, 0, 6]]
theorem accepted935 : SyntheticAccepted (decode 935) 1 0
    connector935 added935 := by decide

def connector936 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added936 : List (List Vertex) := [[1, 0, 4, 7, 2, 5, 3], [1, 7, 3]]
theorem accepted936 : SyntheticAccepted (decode 936) 0 1
    connector936 added936 := by decide

def connector941 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added941 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 4], [1, 0, 3, 7, 4]]
theorem accepted941 : SyntheticAccepted (decode 941) 1 0
    connector941 added941 := by decide

def connector944 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added944 : List (List Vertex) := [[2, 6, 4, 7, 3, 0], [2, 0]]
theorem accepted944 : SyntheticAccepted (decode 944) 2 0
    connector944 added944 := by decide

def connector945 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added945 : List (List Vertex) := [[2, 7, 4, 6, 0, 3, 5], [2, 0, 5]]
theorem accepted945 : SyntheticAccepted (decode 945) 1 2
    connector945 added945 := by decide

def connector947 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added947 : List (List Vertex) := [[2, 7, 4, 6, 0, 3], [2, 0, 7, 3]]
theorem accepted947 : SyntheticAccepted (decode 947) 1 0
    connector947 added947 := by decide

def connector948 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added948 : List (List Vertex) := [[2, 7, 4, 6, 1, 5, 3, 0], [2, 0]]
theorem accepted948 : SyntheticAccepted (decode 948) 1 2
    connector948 added948 := by decide

def connector949 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added949 : List (List Vertex) := [[2, 7, 4, 6, 1, 0, 3, 5], [2, 6, 0, 5]]
theorem accepted949 : SyntheticAccepted (decode 949) 0 2
    connector949 added949 := by decide

def connector950 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added950 : List (List Vertex) := [[4, 6, 2, 7, 3, 0, 1, 5], [4, 7, 0, 5]]
theorem accepted950 : SyntheticAccepted (decode 950) 0 1
    connector950 added950 := by decide

def connector953 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added953 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 3], [1, 0, 4, 7, 3]]
theorem accepted953 : SyntheticAccepted (decode 953) 0 1
    connector953 added953 := by decide

def connector956 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added956 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 4], [1, 7, 4]]
theorem accepted956 : SyntheticAccepted (decode 956) 1 0
    connector956 added956 := by decide

def connector964 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added964 : List (List Vertex) := [[1, 6, 4, 7, 3, 0], [1, 0]]
theorem accepted964 : SyntheticAccepted (decode 964) 1 0
    connector964 added964 := by decide

def connector966 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added966 : List (List Vertex) := [[1, 5, 0, 3, 6, 4, 7], [1, 0, 7]]
theorem accepted966 : SyntheticAccepted (decode 966) 2 1
    connector966 added966 := by decide

def connector967 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added967 : List (List Vertex) := [[1, 6, 3, 0, 7, 4], [1, 0, 6, 4]]
theorem accepted967 : SyntheticAccepted (decode 967) 2 0
    connector967 added967 := by decide

def connector968 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added968 : List (List Vertex) := [[1, 7, 4, 6, 3, 0], [1, 0]]
theorem accepted968 : SyntheticAccepted (decode 968) 2 0
    connector968 added968 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
