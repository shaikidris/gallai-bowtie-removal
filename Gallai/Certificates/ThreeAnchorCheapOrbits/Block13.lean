/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails925 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 1, 2], [5, 7, 3, 0, 1, 6, 2]]
def added925 : List (List Vertex) := [[6, 4, 0, 2, 5]]
def attachments925 : Fin tails925.length → Fin 3 := ![1, 0]
theorem accepted925 : CheapOriginalAccepted (decode 925) 0 2
    tails925 added925 attachments925 := by decide

def tails926 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 6, 2, 0, 4, 7, 3]]
def added926 : List (List Vertex) := [[7, 1, 0, 3, 5]]
def attachments926 : Fin tails926.length → Fin 3 := ![2, 0]
theorem accepted926 : CheapOriginalAccepted (decode 926) 0 1
    tails926 added926 attachments926 := by decide

def tails928 : List (List Vertex) := [[7, 6, 4, 3, 0, 1, 2, 5], [5, 3, 7, 4, 0, 2]]
def added928 : List (List Vertex) := [[2, 7]]
def attachments928 : Fin tails928.length → Fin 3 := ![2, 0]
theorem accepted928 : CheapOriginalAccepted (decode 928) 2 1
    tails928 added928 attachments928 := by decide

def tails929 : List (List Vertex) := [[5, 2, 1, 0, 3, 7, 4, 6], [6, 0, 4, 3, 5, 7, 2]]
def added929 : List (List Vertex) := [[2, 0, 5]]
def attachments929 : Fin tails929.length → Fin 3 := ![0, 1]
theorem accepted929 : CheapOriginalAccepted (decode 929) 0 2
    tails929 added929 attachments929 := by decide

def tails930 : List (List Vertex) := [[7, 0, 3, 4, 6, 5, 2, 1], [5, 3, 7, 2, 0, 1]]
def added930 : List (List Vertex) := [[7, 4, 0, 5]]
def attachments930 : Fin tails930.length → Fin 3 := ![2, 0]
theorem accepted930 : CheapOriginalAccepted (decode 930) 0 1
    tails930 added930 attachments930 := by decide

def tails932 : List (List Vertex) := [[5, 7, 3, 0, 4, 6, 1, 2], [7, 4, 3, 5, 1, 0, 2]]
def added932 : List (List Vertex) := [[5, 2, 7]]
def attachments932 : Fin tails932.length → Fin 3 := ![0, 2]
theorem accepted932 : CheapOriginalAccepted (decode 932) 0 2
    tails932 added932 attachments932 := by decide

def tails933 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 7, 4, 0, 2, 5, 1]]
def added933 : List (List Vertex) := [[5, 3, 0, 1, 6]]
def attachments933 : Fin tails933.length → Fin 3 := ![0, 1]
theorem accepted933 : CheapOriginalAccepted (decode 933) 1 2
    tails933 added933 attachments933 := by decide

def tails935 : List (List Vertex) := [[7, 0, 6, 1, 2, 5, 3, 4], [6, 5, 1, 0, 3, 7, 4]]
def added935 : List (List Vertex) := [[7, 2, 0, 4, 6]]
def attachments935 : Fin tails935.length → Fin 3 := ![2, 1]
theorem accepted935 : CheapOriginalAccepted (decode 935) 1 0
    tails935 added935 attachments935 := by decide

def tails936 : List (List Vertex) := [[7, 3, 0, 4, 6, 5, 2, 1], [5, 3, 4, 7, 2, 0, 1]]
def added936 : List (List Vertex) := [[7, 1, 5]]
def attachments936 : Fin tails936.length → Fin 3 := ![2, 0]
theorem accepted936 : CheapOriginalAccepted (decode 936) 0 1
    tails936 added936 attachments936 := by decide

def tails941 : List (List Vertex) := [[6, 0, 4, 7, 3, 5, 2, 1], [5, 6, 4, 3, 0, 2, 7, 1]]
def added941 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments941 : Fin tails941.length → Fin 3 := ![1, 0]
theorem accepted941 : CheapOriginalAccepted (decode 941) 1 0
    tails941 added941 attachments941 := by decide

def tails944 : List (List Vertex) := [[7, 5, 3, 4, 0, 1, 2, 6], [6, 4, 7, 3, 0, 2]]
def added944 : List (List Vertex) := [[2, 7]]
def attachments944 : Fin tails944.length → Fin 3 := ![2, 1]
theorem accepted944 : CheapOriginalAccepted (decode 944) 2 0
    tails944 added944 attachments944 := by decide

def tails945 : List (List Vertex) := [[6, 2, 1, 0, 4, 7, 3, 5], [5, 0, 3, 4, 6, 7, 2]]
def added945 : List (List Vertex) := [[2, 0, 6]]
def attachments945 : Fin tails945.length → Fin 3 := ![1, 0]
theorem accepted945 : CheapOriginalAccepted (decode 945) 1 2
    tails945 added945 attachments945 := by decide

def tails947 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 2, 1], [6, 4, 7, 2, 0, 1]]
def added947 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments947 : Fin tails947.length → Fin 3 := ![2, 1]
theorem accepted947 : CheapOriginalAccepted (decode 947) 1 0
    tails947 added947 attachments947 := by decide

def tails948 : List (List Vertex) := [[6, 7, 4, 0, 3, 5, 1, 2], [7, 3, 4, 6, 1, 0, 2]]
def added948 : List (List Vertex) := [[6, 2, 7]]
def attachments948 : Fin tails948.length → Fin 3 := ![1, 2]
theorem accepted948 : CheapOriginalAccepted (decode 948) 1 2
    tails948 added948 attachments948 := by decide

def tails949 : List (List Vertex) := [[6, 0, 5, 3, 4, 7, 2, 1], [5, 7, 3, 0, 2, 6, 1]]
def added949 : List (List Vertex) := [[6, 4, 0, 1, 5]]
def attachments949 : Fin tails949.length → Fin 3 := ![1, 0]
theorem accepted949 : CheapOriginalAccepted (decode 949) 0 2
    tails949 added949 attachments949 := by decide

def tails950 : List (List Vertex) := [[7, 0, 5, 1, 2, 6, 4, 3], [5, 6, 1, 0, 4, 7, 3]]
def added950 : List (List Vertex) := [[7, 2, 0, 3, 5]]
def attachments950 : Fin tails950.length → Fin 3 := ![2, 0]
theorem accepted950 : CheapOriginalAccepted (decode 950) 0 1
    tails950 added950 attachments950 := by decide

def tails953 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 2, 1], [6, 5, 3, 4, 0, 2, 7, 1]]
def added953 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments953 : Fin tails953.length → Fin 3 := ![0, 1]
theorem accepted953 : CheapOriginalAccepted (decode 953) 0 1
    tails953 added953 attachments953 := by decide

def tails956 : List (List Vertex) := [[7, 4, 0, 3, 5, 6, 2, 1], [6, 4, 3, 7, 2, 0, 1]]
def added956 : List (List Vertex) := [[7, 1, 6]]
def attachments956 : Fin tails956.length → Fin 3 := ![2, 1]
theorem accepted956 : CheapOriginalAccepted (decode 956) 1 0
    tails956 added956 attachments956 := by decide

def tails964 : List (List Vertex) := [[6, 3, 7, 4, 0, 2, 1, 5], [5, 6, 4, 3, 0, 1]]
def added964 : List (List Vertex) := [[1, 6]]
def attachments964 : Fin tails964.length → Fin 3 := ![1, 0]
theorem accepted964 : CheapOriginalAccepted (decode 964) 1 0
    tails964 added964 attachments964 := by decide

def tails966 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 6, 4, 0, 1, 5]]
def added966 : List (List Vertex) := [[2, 0, 3, 7]]
def attachments966 : Fin tails966.length → Fin 3 := ![0, 2]
theorem accepted966 : CheapOriginalAccepted (decode 966) 2 1
    tails966 added966 attachments966 := by decide

def tails967 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 1, 2], [7, 4, 6, 1, 0, 2]]
def added967 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments967 : Fin tails967.length → Fin 3 := ![1, 2]
theorem accepted967 : CheapOriginalAccepted (decode 967) 2 0
    tails967 added967 attachments967 := by decide

def tails968 : List (List Vertex) := [[7, 3, 6, 4, 0, 2, 1, 5], [5, 7, 4, 3, 0, 1]]
def added968 : List (List Vertex) := [[1, 7]]
def attachments968 : Fin tails968.length → Fin 3 := ![2, 0]
theorem accepted968 : CheapOriginalAccepted (decode 968) 2 0
    tails968 added968 attachments968 := by decide

def tails969 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 7, 4, 0, 1, 5]]
def added969 : List (List Vertex) := [[2, 0, 3, 6]]
def attachments969 : Fin tails969.length → Fin 3 := ![0, 1]
theorem accepted969 : CheapOriginalAccepted (decode 969) 1 2
    tails969 added969 attachments969 := by decide

def tails971 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 1, 2], [6, 4, 7, 1, 0, 2]]
def added971 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments971 : Fin tails971.length → Fin 3 := ![2, 1]
theorem accepted971 : CheapOriginalAccepted (decode 971) 1 0
    tails971 added971 attachments971 := by decide

def tails973 : List (List Vertex) := [[6, 1, 2, 0, 3, 4, 7, 5], [5, 0, 4, 6, 3, 7, 1]]
def added973 : List (List Vertex) := [[1, 0, 6]]
def attachments973 : Fin tails973.length → Fin 3 := ![1, 0]
theorem accepted973 : CheapOriginalAccepted (decode 973) 0 2
    tails973 added973 attachments973 := by decide

def tails974 : List (List Vertex) := [[7, 1, 2, 0, 3, 4, 6, 5], [5, 0, 4, 7, 3, 6, 1]]
def added974 : List (List Vertex) := [[1, 0, 7]]
def attachments974 : Fin tails974.length → Fin 3 := ![2, 0]
theorem accepted974 : CheapOriginalAccepted (decode 974) 0 1
    tails974 added974 attachments974 := by decide

def tails976 : List (List Vertex) := [[6, 3, 7, 4, 0, 1, 2, 5], [5, 6, 4, 3, 0, 2]]
def added976 : List (List Vertex) := [[2, 6]]
def attachments976 : Fin tails976.length → Fin 3 := ![1, 0]
theorem accepted976 : CheapOriginalAccepted (decode 976) 1 0
    tails976 added976 attachments976 := by decide

def tails978 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 6, 4, 0, 2, 5]]
def added978 : List (List Vertex) := [[1, 0, 3, 7]]
def attachments978 : Fin tails978.length → Fin 3 := ![0, 2]
theorem accepted978 : CheapOriginalAccepted (decode 978) 2 1
    tails978 added978 attachments978 := by decide

def tails979 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 2, 1], [7, 4, 6, 2, 0, 1]]
def added979 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments979 : Fin tails979.length → Fin 3 := ![1, 2]
theorem accepted979 : CheapOriginalAccepted (decode 979) 2 0
    tails979 added979 attachments979 := by decide

def tails982 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 5, 2, 0, 4, 6, 1]]
def added982 : List (List Vertex) := [[5, 1, 0, 3, 7]]
def attachments982 : Fin tails982.length → Fin 3 := ![0, 2]
theorem accepted982 : CheapOriginalAccepted (decode 982) 0 2
    tails982 added982 attachments982 := by decide

def tails984 : List (List Vertex) := [[7, 6, 2, 5, 1, 0, 4, 3], [6, 4, 7, 1, 2, 0, 3]]
def added984 : List (List Vertex) := [[7, 3, 6]]
def attachments984 : Fin tails984.length → Fin 3 := ![2, 1]
theorem accepted984 : CheapOriginalAccepted (decode 984) 2 1
    tails984 added984 attachments984 := by decide

def tails985 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 3, 0, 4, 7, 5, 2]]
def added985 : List (List Vertex) := [[5, 1, 0, 2, 6]]
def attachments985 : Fin tails985.length → Fin 3 := ![0, 1]
theorem accepted985 : CheapOriginalAccepted (decode 985) 0 2
    tails985 added985 attachments985 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
