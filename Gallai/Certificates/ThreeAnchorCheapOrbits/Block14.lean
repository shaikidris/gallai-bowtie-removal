/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails986 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 3, 0, 4, 6, 5, 1]]
def added986 : List (List Vertex) := [[5, 2, 0, 1, 7]]
def attachments986 : Fin tails986.length → Fin 3 := ![0, 2]
theorem accepted986 : CheapOriginalAccepted (decode 986) 0 1
    tails986 added986 attachments986 := by decide

def tails988 : List (List Vertex) := [[6, 1, 0, 2, 5, 7, 4, 3], [7, 1, 2, 6, 4, 0, 3]]
def added988 : List (List Vertex) := [[6, 3, 7]]
def attachments988 : Fin tails988.length → Fin 3 := ![1, 2]
theorem accepted988 : CheapOriginalAccepted (decode 988) 2 0
    tails988 added988 attachments988 := by decide

def tails992 : List (List Vertex) := [[7, 3, 6, 4, 0, 1, 2, 5], [5, 7, 4, 3, 0, 2]]
def added992 : List (List Vertex) := [[2, 7]]
def attachments992 : Fin tails992.length → Fin 3 := ![2, 0]
theorem accepted992 : CheapOriginalAccepted (decode 992) 2 0
    tails992 added992 attachments992 := by decide

def tails993 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 7, 4, 0, 2, 5]]
def added993 : List (List Vertex) := [[1, 0, 3, 6]]
def attachments993 : Fin tails993.length → Fin 3 := ![0, 1]
theorem accepted993 : CheapOriginalAccepted (decode 993) 1 2
    tails993 added993 attachments993 := by decide

def tails995 : List (List Vertex) := [[7, 0, 4, 3, 6, 5, 2, 1], [6, 4, 7, 2, 0, 1]]
def added995 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments995 : Fin tails995.length → Fin 3 := ![2, 1]
theorem accepted995 : CheapOriginalAccepted (decode 995) 1 0
    tails995 added995 attachments995 := by decide

def tails996 : List (List Vertex) := [[6, 7, 2, 5, 1, 0, 4, 3], [7, 4, 6, 1, 2, 0, 3]]
def added996 : List (List Vertex) := [[6, 3, 7]]
def attachments996 : Fin tails996.length → Fin 3 := ![1, 2]
theorem accepted996 : CheapOriginalAccepted (decode 996) 1 2
    tails996 added996 attachments996 := by decide

def tails997 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 3, 0, 4, 7, 5, 1]]
def added997 : List (List Vertex) := [[5, 2, 0, 1, 6]]
def attachments997 : Fin tails997.length → Fin 3 := ![0, 1]
theorem accepted997 : CheapOriginalAccepted (decode 997) 0 2
    tails997 added997 attachments997 := by decide

def tails998 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 3, 0, 4, 6, 5, 2]]
def added998 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments998 : Fin tails998.length → Fin 3 := ![0, 2]
theorem accepted998 : CheapOriginalAccepted (decode 998) 0 1
    tails998 added998 attachments998 := by decide

def tails1001 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 5, 2, 0, 4, 7, 1]]
def added1001 : List (List Vertex) := [[5, 1, 0, 3, 6]]
def attachments1001 : Fin tails1001.length → Fin 3 := ![0, 1]
theorem accepted1001 : CheapOriginalAccepted (decode 1001) 0 1
    tails1001 added1001 attachments1001 := by decide

def tails1004 : List (List Vertex) := [[7, 1, 0, 2, 5, 6, 4, 3], [6, 1, 2, 7, 4, 0, 3]]
def added1004 : List (List Vertex) := [[7, 3, 6]]
def attachments1004 : Fin tails1004.length → Fin 3 := ![2, 1]
theorem accepted1004 : CheapOriginalAccepted (decode 1004) 1 0
    tails1004 added1004 attachments1004 := by decide

def tails1009 : List (List Vertex) := [[6, 2, 1, 0, 3, 4, 7, 5], [5, 0, 4, 6, 3, 7, 2]]
def added1009 : List (List Vertex) := [[2, 0, 6]]
def attachments1009 : Fin tails1009.length → Fin 3 := ![1, 0]
theorem accepted1009 : CheapOriginalAccepted (decode 1009) 0 2
    tails1009 added1009 attachments1009 := by decide

def tails1010 : List (List Vertex) := [[7, 2, 1, 0, 3, 4, 6, 5], [5, 0, 4, 7, 3, 6, 2]]
def added1010 : List (List Vertex) := [[2, 0, 7]]
def attachments1010 : Fin tails1010.length → Fin 3 := ![2, 0]
theorem accepted1010 : CheapOriginalAccepted (decode 1010) 0 1
    tails1010 added1010 attachments1010 := by decide

def tails1012 : List (List Vertex) := [[6, 2, 0, 1, 5, 7, 4, 3], [7, 2, 1, 6, 4, 0, 3]]
def added1012 : List (List Vertex) := [[6, 3, 7]]
def attachments1012 : Fin tails1012.length → Fin 3 := ![1, 2]
theorem accepted1012 : CheapOriginalAccepted (decode 1012) 2 0
    tails1012 added1012 attachments1012 := by decide

def tails1016 : List (List Vertex) := [[7, 2, 0, 1, 5, 6, 4, 3], [6, 2, 1, 7, 4, 0, 3]]
def added1016 : List (List Vertex) := [[7, 3, 6]]
def attachments1016 : Fin tails1016.length → Fin 3 := ![2, 1]
theorem accepted1016 : CheapOriginalAccepted (decode 1016) 1 0
    tails1016 added1016 attachments1016 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
