/- Generated literal data; source SHA-256: 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda -/
import Gallai.Certificates.ThreeAnchorSynthetic

namespace Gallai.Certificate.ThreeAnchor.Catalogue

set_option maxRecDepth 4096
set_option maxHeartbeats 800000

def state00 : State := ![0, 0, 1, 1, 1]
def connector00 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added00 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted00 : SyntheticAccepted state00 0 1 connector00 added00 := by decide

def state01 : State := ![0, 0, 1, 1, 2]
def connector01 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added01 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted01 : SyntheticAccepted state01 0 2 connector01 added01 := by decide

def state02 : State := ![0, 0, 1, 2, 2]
def connector02 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added02 : List (List Vertex) := [[2, 5, 4, 7, 3, 0], [2, 0]]
theorem accepted02 : SyntheticAccepted state02 0 1 connector02 added02 := by decide

def state03 : State := ![0, 1, 1, 1, 2]
def connector03 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added03 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [1, 5, 3]]
theorem accepted03 : SyntheticAccepted state03 1 2 connector03 added03 := by decide

def state04 : State := ![0, 1, 1, 2, 3]
def connector04 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added04 : List (List Vertex) := [[1, 6, 2, 5, 3, 7, 4, 0], [1, 0]]
theorem accepted04 : SyntheticAccepted state04 0 1 connector04 added04 := by decide

def state05 : State := ![0, 1, 2, 1, 3]
def connector05 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added05 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 4, 0], [1, 0]]
theorem accepted05 : SyntheticAccepted state05 0 1 connector05 added05 := by decide

def state06 : State := ![1, 0, 1, 1, 2]
def connector06 : List Vertex := [6, 2, 1, 0, 3, 4, 7]
def added06 : List (List Vertex) := [[2, 5, 3, 6, 0, 4], [2, 0, 5, 4]]
theorem accepted06 : SyntheticAccepted state06 1 2 connector06 added06 := by decide

def state07 : State := ![1, 0, 1, 2, 3]
def connector07 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added07 : List (List Vertex) := [[2, 6, 0, 4, 7, 3, 5], [2, 0, 5]]
theorem accepted07 : SyntheticAccepted state07 0 1 connector07 added07 := by decide

def state08 : State := ![1, 0, 2, 1, 1]
def connector08 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added08 : List (List Vertex) := [[2, 5, 3, 0, 6, 4], [2, 0, 5, 4]]
theorem accepted08 : SyntheticAccepted state08 1 2 connector08 added08 := by decide

def state09 : State := ![1, 0, 2, 1, 3]
def connector09 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added09 : List (List Vertex) := [[2, 7, 4, 0, 5, 3, 6], [2, 0, 6]]
theorem accepted09 : SyntheticAccepted state09 0 1 connector09 added09 := by decide

def state10 : State := ![1, 0, 2, 2, 2]
def connector10 : List Vertex := [6, 0, 1, 2, 7]
def added10 : List (List Vertex) := [[2, 5, 3, 0, 4, 7], [2, 0, 5, 4, 3, 7]]
theorem accepted10 : SyntheticAccepted state10 1 2 connector10 added10 := by decide

def state11 : State := ![1, 0, 2, 2, 3]
def connector11 : List Vertex := [5, 2, 1, 0, 3, 4, 7]
def added11 : List (List Vertex) := [[2, 7, 3, 5, 0, 4, 6], [2, 0, 6]]
theorem accepted11 : SyntheticAccepted state11 0 2 connector11 added11 := by decide

def state12 : State := ![1, 0, 2, 3, 3]
def connector12 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added12 : List (List Vertex) := [[2, 5, 0, 3, 7, 4, 6], [2, 0, 6]]
theorem accepted12 : SyntheticAccepted state12 1 2 connector12 added12 := by decide

def state13 : State := ![1, 1, 2, 2, 3]
def connector13 : List Vertex := [6, 1, 2, 0, 3, 4, 7]
def added13 : List (List Vertex) := [[2, 7, 3, 5, 1, 0, 4, 6], [2, 5, 0, 6]]
theorem accepted13 : SyntheticAccepted state13 1 2 connector13 added13 := by decide

def state14 : State := ![1, 1, 2, 3, 3]
def connector14 : List Vertex := [5, 1, 2, 0, 3, 4, 7]
def added14 : List (List Vertex) := [[1, 6, 3, 7, 2, 5, 0, 4], [1, 0, 6, 4]]
theorem accepted14 : SyntheticAccepted state14 0 2 connector14 added14 := by decide

def state15 : State := ![1, 2, 2, 3, 3]
def connector15 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added15 : List (List Vertex) := [[1, 7, 2, 5, 0, 6, 3], [1, 0, 4, 7, 3]]
theorem accepted15 : SyntheticAccepted state15 0 1 connector15 added15 := by decide

def state16 : State := ![1, 2, 3, 2, 3]
def connector16 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added16 : List (List Vertex) := [[1, 7, 2, 6, 0, 5, 3], [1, 0, 4, 7, 3]]
theorem accepted16 : SyntheticAccepted state16 0 1 connector16 added16 := by decide

end Gallai.Certificate.ThreeAnchor.Catalogue
