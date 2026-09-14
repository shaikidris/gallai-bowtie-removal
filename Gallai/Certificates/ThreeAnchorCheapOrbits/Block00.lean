/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails86 : List (List Vertex) := [[5, 3, 4, 0, 1, 2, 6, 7], [7, 0, 2, 5, 1, 6, 3]]
def added86 : List (List Vertex) := [[3, 0, 5]]
def attachments86 : Fin tails86.length → Fin 3 := ![0, 2]
theorem accepted86 : CheapOriginalAccepted (decode 86) 2 1
    tails86 added86 attachments86 := by decide

def tails87 : List (List Vertex) := [[6, 3, 4, 0, 1, 2, 5, 7], [7, 0, 2, 6, 1, 5, 3]]
def added87 : List (List Vertex) := [[3, 0, 6]]
def attachments87 : Fin tails87.length → Fin 3 := ![1, 2]
theorem accepted87 : CheapOriginalAccepted (decode 87) 2 0
    tails87 added87 attachments87 := by decide

def tails88 : List (List Vertex) := [[5, 7, 1, 2, 0, 4, 3, 6], [6, 2, 5, 1, 0, 3]]
def added88 : List (List Vertex) := [[3, 5]]
def attachments88 : Fin tails88.length → Fin 3 := ![0, 1]
theorem accepted88 : CheapOriginalAccepted (decode 88) 0 2
    tails88 added88 attachments88 := by decide

def tails89 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 3, 4], [6, 2, 5, 3, 0, 4]]
def added89 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments89 : Fin tails89.length → Fin 3 := ![0, 1]
theorem accepted89 : CheapOriginalAccepted (decode 89) 1 2
    tails89 added89 attachments89 := by decide

def tails91 : List (List Vertex) := [[6, 3, 4, 0, 2, 5, 1, 7], [7, 0, 1, 2, 6, 5, 3]]
def added91 : List (List Vertex) := [[3, 0, 6]]
def attachments91 : Fin tails91.length → Fin 3 := ![1, 2]
theorem accepted91 : CheapOriginalAccepted (decode 91) 1 0
    tails91 added91 attachments91 := by decide

def tails92 : List (List Vertex) := [[6, 7, 1, 2, 0, 4, 3, 5], [5, 2, 6, 1, 0, 3]]
def added92 : List (List Vertex) := [[3, 6]]
def attachments92 : Fin tails92.length → Fin 3 := ![1, 0]
theorem accepted92 : CheapOriginalAccepted (decode 92) 1 2
    tails92 added92 attachments92 := by decide

def tails93 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 3, 4], [5, 2, 6, 3, 0, 4]]
def added93 : List (List Vertex) := [[6, 1, 0, 5]]
def attachments93 : Fin tails93.length → Fin 3 := ![1, 0]
theorem accepted93 : CheapOriginalAccepted (decode 93) 0 2
    tails93 added93 attachments93 := by decide

def tails94 : List (List Vertex) := [[5, 3, 4, 0, 2, 6, 1, 7], [7, 0, 1, 2, 5, 6, 3]]
def added94 : List (List Vertex) := [[3, 0, 5]]
def attachments94 : Fin tails94.length → Fin 3 := ![0, 2]
theorem accepted94 : CheapOriginalAccepted (decode 94) 0 1
    tails94 added94 attachments94 := by decide

def tails100 : List (List Vertex) := [[5, 7, 2, 1, 0, 4, 3, 6], [6, 1, 5, 2, 0, 3]]
def added100 : List (List Vertex) := [[3, 5]]
def attachments100 : Fin tails100.length → Fin 3 := ![0, 1]
theorem accepted100 : CheapOriginalAccepted (decode 100) 0 2
    tails100 added100 attachments100 := by decide

def tails101 : List (List Vertex) := [[5, 0, 1, 2, 7, 6, 3, 4], [6, 1, 5, 3, 0, 4]]
def added101 : List (List Vertex) := [[5, 2, 0, 6]]
def attachments101 : Fin tails101.length → Fin 3 := ![0, 1]
theorem accepted101 : CheapOriginalAccepted (decode 101) 1 2
    tails101 added101 attachments101 := by decide

def tails103 : List (List Vertex) := [[6, 3, 4, 0, 1, 5, 2, 7], [7, 0, 2, 1, 6, 5, 3]]
def added103 : List (List Vertex) := [[3, 0, 6]]
def attachments103 : Fin tails103.length → Fin 3 := ![1, 2]
theorem accepted103 : CheapOriginalAccepted (decode 103) 1 0
    tails103 added103 attachments103 := by decide

def tails104 : List (List Vertex) := [[5, 1, 7, 2, 0, 4, 3, 6], [6, 5, 2, 1, 0, 3]]
def added104 : List (List Vertex) := [[3, 5]]
def attachments104 : Fin tails104.length → Fin 3 := ![0, 1]
theorem accepted104 : CheapOriginalAccepted (decode 104) 0 1
    tails104 added104 attachments104 := by decide

def tails106 : List (List Vertex) := [[5, 0, 2, 1, 7, 6, 3, 4], [7, 2, 5, 3, 0, 4]]
def added106 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments106 : Fin tails106.length → Fin 3 := ![0, 2]
theorem accepted106 : CheapOriginalAccepted (decode 106) 2 1
    tails106 added106 attachments106 := by decide

def tails107 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 5, 2, 0, 3, 6]]
def added107 : List (List Vertex) := [[4, 0, 1, 7]]
def attachments107 : Fin tails107.length → Fin 3 := ![1, 2]
theorem accepted107 : CheapOriginalAccepted (decode 107) 2 0
    tails107 added107 attachments107 := by decide

def tails109 : List (List Vertex) := [[6, 0, 1, 7, 2, 5, 3, 4], [5, 6, 1, 2, 0, 4]]
def added109 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments109 : Fin tails109.length → Fin 3 := ![1, 0]
theorem accepted109 : CheapOriginalAccepted (decode 109) 1 0
    tails109 added109 attachments109 := by decide

def tails110 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 5, 3, 0, 4]]
def added110 : List (List Vertex) := [[5, 2, 0, 1, 7]]
def attachments110 : Fin tails110.length → Fin 3 := ![0, 2]
theorem accepted110 : CheapOriginalAccepted (decode 110) 0 2
    tails110 added110 attachments110 := by decide

def tails111 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 3, 4], [7, 6, 3, 0, 4]]
def added111 : List (List Vertex) := [[6, 1, 0, 2, 7]]
def attachments111 : Fin tails111.length → Fin 3 := ![1, 2]
theorem accepted111 : CheapOriginalAccepted (decode 111) 1 2
    tails111 added111 attachments111 := by decide

def tails116 : List (List Vertex) := [[6, 7, 2, 1, 0, 4, 3, 5], [5, 1, 6, 2, 0, 3]]
def added116 : List (List Vertex) := [[3, 6]]
def attachments116 : Fin tails116.length → Fin 3 := ![1, 0]
theorem accepted116 : CheapOriginalAccepted (decode 116) 1 2
    tails116 added116 attachments116 := by decide

def tails117 : List (List Vertex) := [[6, 0, 1, 2, 7, 5, 3, 4], [5, 1, 6, 3, 0, 4]]
def added117 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments117 : Fin tails117.length → Fin 3 := ![1, 0]
theorem accepted117 : CheapOriginalAccepted (decode 117) 0 2
    tails117 added117 attachments117 := by decide

def tails118 : List (List Vertex) := [[5, 3, 4, 0, 1, 6, 2, 7], [7, 0, 2, 1, 5, 6, 3]]
def added118 : List (List Vertex) := [[3, 0, 5]]
def attachments118 : Fin tails118.length → Fin 3 := ![0, 2]
theorem accepted118 : CheapOriginalAccepted (decode 118) 0 1
    tails118 added118 attachments118 := by decide

def tails121 : List (List Vertex) := [[5, 0, 1, 7, 2, 6, 3, 4], [6, 5, 1, 2, 0, 4]]
def added121 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments121 : Fin tails121.length → Fin 3 := ![0, 1]
theorem accepted121 : CheapOriginalAccepted (decode 121) 0 1
    tails121 added121 attachments121 := by decide

def tails122 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 3, 4], [7, 5, 3, 0, 4]]
def added122 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments122 : Fin tails122.length → Fin 3 := ![0, 2]
theorem accepted122 : CheapOriginalAccepted (decode 122) 0 2
    tails122 added122 attachments122 := by decide

def tails123 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 6, 3, 0, 4]]
def added123 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments123 : Fin tails123.length → Fin 3 := ![1, 2]
theorem accepted123 : CheapOriginalAccepted (decode 123) 1 2
    tails123 added123 attachments123 := by decide

def tails124 : List (List Vertex) := [[6, 1, 7, 2, 0, 4, 3, 5], [5, 6, 2, 1, 0, 3]]
def added124 : List (List Vertex) := [[3, 6]]
def attachments124 : Fin tails124.length → Fin 3 := ![1, 0]
theorem accepted124 : CheapOriginalAccepted (decode 124) 1 0
    tails124 added124 attachments124 := by decide

def tails126 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 3, 4], [7, 6, 2, 0, 3, 5]]
def added126 : List (List Vertex) := [[4, 0, 1, 7]]
def attachments126 : Fin tails126.length → Fin 3 := ![0, 2]
theorem accepted126 : CheapOriginalAccepted (decode 126) 2 1
    tails126 added126 attachments126 := by decide

def tails127 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 3, 4], [7, 2, 6, 3, 0, 4]]
def added127 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments127 : Fin tails127.length → Fin 3 := ![1, 2]
theorem accepted127 : CheapOriginalAccepted (decode 127) 2 0
    tails127 added127 attachments127 := by decide

def tails148 : List (List Vertex) := [[5, 1, 6, 2, 0, 4, 3, 7], [7, 5, 2, 1, 0, 3]]
def added148 : List (List Vertex) := [[3, 5]]
def attachments148 : Fin tails148.length → Fin 3 := ![0, 2]
theorem accepted148 : CheapOriginalAccepted (decode 148) 0 2
    tails148 added148 attachments148 := by decide

def tails149 : List (List Vertex) := [[5, 0, 2, 1, 6, 7, 3, 4], [6, 2, 5, 3, 0, 4]]
def added149 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments149 : Fin tails149.length → Fin 3 := ![0, 1]
theorem accepted149 : CheapOriginalAccepted (decode 149) 1 2
    tails149 added149 attachments149 := by decide

def tails151 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 5, 2, 0, 3, 7]]
def added151 : List (List Vertex) := [[4, 0, 1, 6]]
def attachments151 : Fin tails151.length → Fin 3 := ![2, 1]
theorem accepted151 : CheapOriginalAccepted (decode 151) 1 0
    tails151 added151 attachments151 := by decide

def tails152 : List (List Vertex) := [[5, 6, 2, 1, 0, 4, 3, 7], [7, 1, 5, 2, 0, 3]]
def added152 : List (List Vertex) := [[3, 5]]
def attachments152 : Fin tails152.length → Fin 3 := ![0, 2]
theorem accepted152 : CheapOriginalAccepted (decode 152) 0 1
    tails152 added152 attachments152 := by decide

def tails154 : List (List Vertex) := [[5, 0, 1, 2, 6, 7, 3, 4], [7, 1, 5, 3, 0, 4]]
def added154 : List (List Vertex) := [[5, 2, 0, 7]]
def attachments154 : Fin tails154.length → Fin 3 := ![0, 2]
theorem accepted154 : CheapOriginalAccepted (decode 154) 2 1
    tails154 added154 attachments154 := by decide

def tails155 : List (List Vertex) := [[7, 3, 4, 0, 1, 5, 2, 6], [6, 0, 2, 1, 7, 5, 3]]
def added155 : List (List Vertex) := [[3, 0, 7]]
def attachments155 : Fin tails155.length → Fin 3 := ![2, 1]
theorem accepted155 : CheapOriginalAccepted (decode 155) 2 0
    tails155 added155 attachments155 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
