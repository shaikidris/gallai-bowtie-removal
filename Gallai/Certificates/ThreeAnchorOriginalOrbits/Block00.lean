/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail84 : List Vertex := [5, 2, 1, 0, 3, 4]
def added84 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 5]]
theorem accepted84 : OriginalAccepted (decode 84) 0 1 0
    tail84 added84 := by decide

def tail86 : List Vertex := [5, 2, 1, 0, 3, 4]
def added86 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 7, 0, 5]]
theorem accepted86 : OriginalAccepted (decode 86) 2 1 0
    tail86 added86 := by decide

def tail87 : List Vertex := [6, 2, 1, 0, 3, 4]
def added87 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 1], [1, 5, 7, 0, 6]]
theorem accepted87 : OriginalAccepted (decode 87) 2 0 1
    tail87 added87 := by decide

def tail88 : List Vertex := [5, 1, 2, 0, 3, 4]
def added88 : List (List Vertex) := [[4, 0, 1, 7, 5, 3, 6, 2], [2, 5]]
theorem accepted88 : OriginalAccepted (decode 88) 0 2 0
    tail88 added88 := by decide

def tail89 : List Vertex := [5, 1, 2, 0, 3, 4]
def added89 : List (List Vertex) := [[4, 0, 1, 7, 6, 3, 5, 2], [2, 6, 0, 5]]
theorem accepted89 : OriginalAccepted (decode 89) 1 2 0
    tail89 added89 := by decide

def tail91 : List Vertex := [7, 1, 2, 0, 3, 4]
def added91 : List (List Vertex) := [[4, 0, 1, 5, 3, 6, 2], [2, 5, 6, 0, 7]]
theorem accepted91 : OriginalAccepted (decode 91) 1 0 2
    tail91 added91 := by decide

def tail92 : List Vertex := [6, 1, 2, 0, 3, 4]
def added92 : List (List Vertex) := [[4, 0, 1, 7, 6, 3, 5, 2], [2, 6]]
theorem accepted92 : OriginalAccepted (decode 92) 1 2 1
    tail92 added92 := by decide

def tail93 : List Vertex := [6, 1, 2, 0, 3, 4]
def added93 : List (List Vertex) := [[4, 0, 1, 7, 5, 3, 6, 2], [2, 5, 0, 6]]
theorem accepted93 : OriginalAccepted (decode 93) 0 2 1
    tail93 added93 := by decide

def tail94 : List Vertex := [7, 1, 2, 0, 3, 4]
def added94 : List (List Vertex) := [[4, 0, 1, 6, 3, 5, 2], [2, 6, 5, 0, 7]]
theorem accepted94 : OriginalAccepted (decode 94) 0 1 2
    tail94 added94 := by decide

def tail100 : List Vertex := [5, 2, 1, 0, 3, 4]
def added100 : List (List Vertex) := [[4, 0, 2, 7, 5, 3, 6, 1], [1, 5]]
theorem accepted100 : OriginalAccepted (decode 100) 0 2 0
    tail100 added100 := by decide

def tail101 : List Vertex := [5, 2, 1, 0, 3, 4]
def added101 : List (List Vertex) := [[4, 0, 2, 7, 6, 3, 5, 1], [1, 6, 0, 5]]
theorem accepted101 : OriginalAccepted (decode 101) 1 2 0
    tail101 added101 := by decide

def tail103 : List Vertex := [7, 2, 1, 0, 3, 4]
def added103 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 1], [1, 5, 6, 0, 7]]
theorem accepted103 : OriginalAccepted (decode 103) 1 0 2
    tail103 added103 := by decide

def tail104 : List Vertex := [5, 2, 1, 0, 3, 4]
def added104 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 3, 6], [5, 6]]
theorem accepted104 : OriginalAccepted (decode 104) 0 1 0
    tail104 added104 := by decide

def tail106 : List Vertex := [5, 2, 1, 0, 3, 4]
def added106 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 3, 6], [5, 0, 7, 6]]
theorem accepted106 : OriginalAccepted (decode 106) 2 1 0
    tail106 added106 := by decide

def tail107 : List Vertex := [7, 2, 1, 0, 3, 4]
def added107 : List (List Vertex) := [[4, 0, 6, 3, 5, 7, 1], [1, 5, 2, 0, 7]]
theorem accepted107 : OriginalAccepted (decode 107) 2 0 2
    tail107 added107 := by decide

def tail109 : List Vertex := [5, 2, 1, 0, 3, 4]
def added109 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 5, 3], [3, 6, 0, 5]]
theorem accepted109 : OriginalAccepted (decode 109) 1 0 0
    tail109 added109 := by decide

def tail110 : List Vertex := [7, 1, 2, 0, 3, 4]
def added110 : List (List Vertex) := [[4, 0, 1, 6, 3, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted110 : OriginalAccepted (decode 110) 0 2 2
    tail110 added110 := by decide

def tail111 : List Vertex := [7, 2, 1, 0, 3, 4]
def added111 : List (List Vertex) := [[4, 0, 2, 5, 3, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted111 : OriginalAccepted (decode 111) 1 2 2
    tail111 added111 := by decide

def tail116 : List Vertex := [6, 2, 1, 0, 3, 4]
def added116 : List (List Vertex) := [[4, 0, 2, 7, 6, 3, 5, 1], [1, 6]]
theorem accepted116 : OriginalAccepted (decode 116) 1 2 1
    tail116 added116 := by decide

def tail117 : List Vertex := [6, 2, 1, 0, 3, 4]
def added117 : List (List Vertex) := [[4, 0, 2, 7, 5, 3, 6, 1], [1, 5, 0, 6]]
theorem accepted117 : OriginalAccepted (decode 117) 0 2 1
    tail117 added117 := by decide

def tail118 : List Vertex := [7, 2, 1, 0, 3, 4]
def added118 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 1], [1, 6, 5, 0, 7]]
theorem accepted118 : OriginalAccepted (decode 118) 0 1 2
    tail118 added118 := by decide

def tail121 : List Vertex := [6, 2, 1, 0, 3, 4]
def added121 : List (List Vertex) := [[4, 0, 2, 7, 1, 5, 6, 3], [3, 5, 0, 6]]
theorem accepted121 : OriginalAccepted (decode 121) 0 1 1
    tail121 added121 := by decide

def tail122 : List Vertex := [7, 2, 1, 0, 3, 4]
def added122 : List (List Vertex) := [[4, 0, 2, 6, 3, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted122 : OriginalAccepted (decode 122) 0 2 2
    tail122 added122 := by decide

def tail123 : List Vertex := [7, 1, 2, 0, 3, 4]
def added123 : List (List Vertex) := [[4, 0, 1, 5, 3, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted123 : OriginalAccepted (decode 123) 1 2 2
    tail123 added123 := by decide

def tail124 : List Vertex := [6, 2, 1, 0, 3, 4]
def added124 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 3, 5], [6, 5]]
theorem accepted124 : OriginalAccepted (decode 124) 1 0 1
    tail124 added124 := by decide

def tail126 : List Vertex := [7, 2, 1, 0, 3, 4]
def added126 : List (List Vertex) := [[4, 0, 5, 3, 6, 7, 1], [1, 6, 2, 0, 7]]
theorem accepted126 : OriginalAccepted (decode 126) 2 1 2
    tail126 added126 := by decide

def tail127 : List Vertex := [6, 2, 1, 0, 3, 4]
def added127 : List (List Vertex) := [[4, 0, 2, 7, 1, 6, 3, 5], [6, 0, 7, 5]]
theorem accepted127 : OriginalAccepted (decode 127) 2 0 1
    tail127 added127 := by decide

def tail148 : List Vertex := [5, 2, 1, 0, 3, 4]
def added148 : List (List Vertex) := [[4, 0, 2, 6, 1, 5, 3, 7], [5, 7]]
theorem accepted148 : OriginalAccepted (decode 148) 0 2 0
    tail148 added148 := by decide

def tail149 : List Vertex := [5, 2, 1, 0, 3, 4]
def added149 : List (List Vertex) := [[4, 0, 2, 6, 1, 5, 3, 7], [5, 0, 6, 7]]
theorem accepted149 : OriginalAccepted (decode 149) 1 2 0
    tail149 added149 := by decide

def tail151 : List Vertex := [6, 2, 1, 0, 3, 4]
def added151 : List (List Vertex) := [[4, 0, 7, 3, 5, 6, 1], [1, 5, 2, 0, 6]]
theorem accepted151 : OriginalAccepted (decode 151) 1 0 1
    tail151 added151 := by decide

def tail152 : List Vertex := [5, 2, 1, 0, 3, 4]
def added152 : List (List Vertex) := [[4, 0, 2, 6, 5, 3, 7, 1], [1, 5]]
theorem accepted152 : OriginalAccepted (decode 152) 0 1 0
    tail152 added152 := by decide

def tail154 : List Vertex := [5, 2, 1, 0, 3, 4]
def added154 : List (List Vertex) := [[4, 0, 2, 6, 7, 3, 5, 1], [1, 7, 0, 5]]
theorem accepted154 : OriginalAccepted (decode 154) 2 1 0
    tail154 added154 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
