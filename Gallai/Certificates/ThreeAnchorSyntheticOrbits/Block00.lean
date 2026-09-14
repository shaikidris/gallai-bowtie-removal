/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector84 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added84 : List (List Vertex) := [[3, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted84 : SyntheticAccepted (decode 84) 0 1
    connector84 added84 := by decide

def connector86 : List Vertex := [7, 0, 4, 3, 6]
def added86 : List (List Vertex) := [[3, 5, 1, 0, 2, 6], [3, 0, 5, 2, 1, 6]]
theorem accepted86 : SyntheticAccepted (decode 86) 2 1
    connector86 added86 := by decide

def connector87 : List Vertex := [7, 0, 4, 3, 5]
def added87 : List (List Vertex) := [[3, 6, 1, 0, 2, 5], [3, 0, 6, 2, 1, 5]]
theorem accepted87 : SyntheticAccepted (decode 87) 2 0
    connector87 added87 := by decide

def connector88 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added88 : List (List Vertex) := [[3, 6, 2, 5, 1, 0], [3, 0]]
theorem accepted88 : SyntheticAccepted (decode 88) 0 2
    connector88 added88 := by decide

def connector89 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added89 : List (List Vertex) := [[3, 5, 2, 6, 0, 1], [3, 0, 5, 1]]
theorem accepted89 : SyntheticAccepted (decode 89) 1 2
    connector89 added89 := by decide

def connector91 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added91 : List (List Vertex) := [[3, 5, 2, 6, 0, 1, 7], [3, 0, 7]]
theorem accepted91 : SyntheticAccepted (decode 91) 1 0
    connector91 added91 := by decide

def connector92 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added92 : List (List Vertex) := [[3, 5, 2, 6, 1, 0], [3, 0]]
theorem accepted92 : SyntheticAccepted (decode 92) 1 2
    connector92 added92 := by decide

def connector93 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added93 : List (List Vertex) := [[3, 6, 2, 5, 0, 1], [3, 0, 6, 1]]
theorem accepted93 : SyntheticAccepted (decode 93) 0 2
    connector93 added93 := by decide

def connector94 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added94 : List (List Vertex) := [[3, 6, 2, 5, 0, 1, 7], [3, 0, 7]]
theorem accepted94 : SyntheticAccepted (decode 94) 0 1
    connector94 added94 := by decide

def connector100 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added100 : List (List Vertex) := [[3, 6, 1, 5, 2, 0], [3, 0]]
theorem accepted100 : SyntheticAccepted (decode 100) 0 2
    connector100 added100 := by decide

def connector101 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added101 : List (List Vertex) := [[3, 5, 1, 6, 0, 2], [3, 0, 5, 2]]
theorem accepted101 : SyntheticAccepted (decode 101) 1 2
    connector101 added101 := by decide

def connector103 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added103 : List (List Vertex) := [[3, 5, 1, 6, 0, 2, 7], [3, 0, 7]]
theorem accepted103 : SyntheticAccepted (decode 103) 1 0
    connector103 added103 := by decide

def connector104 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added104 : List (List Vertex) := [[3, 5, 2, 7, 1, 0], [3, 0]]
theorem accepted104 : SyntheticAccepted (decode 104) 0 1
    connector104 added104 := by decide

def connector106 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added106 : List (List Vertex) := [[3, 5, 1, 0, 7, 2], [3, 0, 5, 2]]
theorem accepted106 : SyntheticAccepted (decode 106) 2 1
    connector106 added106 := by decide

def connector107 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added107 : List (List Vertex) := [[3, 6, 0, 1, 5, 2, 7], [3, 0, 7]]
theorem accepted107 : SyntheticAccepted (decode 107) 2 0
    connector107 added107 := by decide

def connector109 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added109 : List (List Vertex) := [[3, 5, 0, 2, 7, 1, 6], [3, 0, 6]]
theorem accepted109 : SyntheticAccepted (decode 109) 1 0
    connector109 added109 := by decide

def connector110 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added110 : List (List Vertex) := [[3, 6, 1, 0, 5, 2, 7], [3, 0, 7]]
theorem accepted110 : SyntheticAccepted (decode 110) 0 2
    connector110 added110 := by decide

def connector111 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added111 : List (List Vertex) := [[3, 5, 2, 0, 6, 1, 7], [3, 0, 7]]
theorem accepted111 : SyntheticAccepted (decode 111) 1 2
    connector111 added111 := by decide

def connector116 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added116 : List (List Vertex) := [[3, 5, 1, 6, 2, 0], [3, 0]]
theorem accepted116 : SyntheticAccepted (decode 116) 1 2
    connector116 added116 := by decide

def connector117 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added117 : List (List Vertex) := [[3, 6, 1, 5, 0, 2], [3, 0, 6, 2]]
theorem accepted117 : SyntheticAccepted (decode 117) 0 2
    connector117 added117 := by decide

def connector118 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added118 : List (List Vertex) := [[3, 6, 1, 5, 0, 2, 7], [3, 0, 7]]
theorem accepted118 : SyntheticAccepted (decode 118) 0 1
    connector118 added118 := by decide

def connector121 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added121 : List (List Vertex) := [[3, 6, 0, 2, 7, 1, 5], [3, 0, 5]]
theorem accepted121 : SyntheticAccepted (decode 121) 0 1
    connector121 added121 := by decide

def connector122 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added122 : List (List Vertex) := [[3, 6, 2, 0, 5, 1, 7], [3, 0, 7]]
theorem accepted122 : SyntheticAccepted (decode 122) 0 2
    connector122 added122 := by decide

def connector123 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added123 : List (List Vertex) := [[3, 5, 1, 0, 6, 2, 7], [3, 0, 7]]
theorem accepted123 : SyntheticAccepted (decode 123) 1 2
    connector123 added123 := by decide

def connector124 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added124 : List (List Vertex) := [[3, 6, 2, 7, 1, 0], [3, 0]]
theorem accepted124 : SyntheticAccepted (decode 124) 1 0
    connector124 added124 := by decide

def connector126 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added126 : List (List Vertex) := [[3, 5, 0, 1, 6, 2, 7], [3, 0, 7]]
theorem accepted126 : SyntheticAccepted (decode 126) 2 1
    connector126 added126 := by decide

def connector127 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added127 : List (List Vertex) := [[3, 6, 1, 0, 7, 2], [3, 0, 6, 2]]
theorem accepted127 : SyntheticAccepted (decode 127) 2 0
    connector127 added127 := by decide

def connector148 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added148 : List (List Vertex) := [[3, 5, 2, 6, 1, 0], [3, 0]]
theorem accepted148 : SyntheticAccepted (decode 148) 0 2
    connector148 added148 := by decide

def connector149 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added149 : List (List Vertex) := [[3, 5, 1, 0, 6, 2], [3, 0, 5, 2]]
theorem accepted149 : SyntheticAccepted (decode 149) 1 2
    connector149 added149 := by decide

def connector151 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added151 : List (List Vertex) := [[3, 7, 0, 1, 5, 2, 6], [3, 0, 6]]
theorem accepted151 : SyntheticAccepted (decode 151) 1 0
    connector151 added151 := by decide

def connector152 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added152 : List (List Vertex) := [[3, 7, 1, 5, 2, 0], [3, 0]]
theorem accepted152 : SyntheticAccepted (decode 152) 0 1
    connector152 added152 := by decide

def connector154 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added154 : List (List Vertex) := [[3, 5, 1, 7, 0, 2], [3, 0, 5, 2]]
theorem accepted154 : SyntheticAccepted (decode 154) 2 1
    connector154 added154 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
