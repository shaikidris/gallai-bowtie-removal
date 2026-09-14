/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail428 : List Vertex := [5, 4, 3, 0, 1, 2]
def added428 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 4, 0], [5, 7, 2, 0]]
theorem accepted428 : OriginalAccepted (decode 428) 2 0 0
    tail428 added428 := by decide

def tail429 : List Vertex := [6, 1, 2, 0, 3, 4]
def added429 : List (List Vertex) := [[3, 5, 2, 7, 1, 0, 4, 6], [4, 5, 0, 6, 7, 3]]
theorem accepted429 : OriginalAccepted (decode 429) 1 2 1
    tail429 added429 := by decide

def tail431 : List Vertex := [6, 4, 3, 0, 2, 1]
def added431 : List (List Vertex) := [[2, 7, 3, 5, 4, 0, 1, 6], [1, 7, 0, 6, 5, 2]]
theorem accepted431 : OriginalAccepted (decode 431) 1 0 1
    tail431 added431 := by decide

def tail433 : List Vertex := [5, 3, 4, 0, 2, 1]
def added433 : List (List Vertex) := [[1, 0, 3, 7, 2, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted433 : OriginalAccepted (decode 433) 1 0 0
    tail433 added433 := by decide

def tail434 : List Vertex := [5, 4, 3, 0, 2, 1]
def added434 : List (List Vertex) := [[1, 0, 4, 6, 2, 7, 5, 3], [3, 7, 0, 5]]
theorem accepted434 : OriginalAccepted (decode 434) 2 0 0
    tail434 added434 := by decide

def tail435 : List Vertex := [6, 4, 3, 0, 2, 1]
def added435 : List (List Vertex) := [[1, 0, 4, 5, 3, 7, 6, 2], [2, 7, 0, 6]]
theorem accepted435 : OriginalAccepted (decode 435) 2 1 1
    tail435 added435 := by decide

def tail436 : List Vertex := [5, 3, 4, 0, 2, 1]
def added436 : List (List Vertex) := [[1, 5, 4, 6, 2, 7, 3, 0], [5, 6, 1, 0]]
theorem accepted436 : OriginalAccepted (decode 436) 1 0 0
    tail436 added436 := by decide

def tail438 : List Vertex := [7, 2, 1, 0, 4, 3]
def added438 : List (List Vertex) := [[4, 5, 1, 6, 2, 0, 3, 7], [3, 5, 0, 7, 6, 4]]
theorem accepted438 : OriginalAccepted (decode 438) 2 1 2
    tail438 added438 := by decide

def tail439 : List Vertex := [7, 3, 4, 0, 1, 2]
def added439 : List (List Vertex) := [[1, 6, 4, 5, 3, 0, 2, 7], [2, 6, 0, 7, 5, 1]]
theorem accepted439 : OriginalAccepted (decode 439) 2 0 2
    tail439 added439 := by decide

def tail440 : List Vertex := [5, 4, 3, 0, 2, 1]
def added440 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 4, 0], [5, 7, 1, 0]]
theorem accepted440 : OriginalAccepted (decode 440) 2 0 0
    tail440 added440 := by decide

def tail441 : List Vertex := [6, 2, 1, 0, 3, 4]
def added441 : List (List Vertex) := [[3, 5, 1, 7, 2, 0, 4, 6], [4, 5, 0, 6, 7, 3]]
theorem accepted441 : OriginalAccepted (decode 441) 1 2 1
    tail441 added441 := by decide

def tail443 : List Vertex := [6, 4, 3, 0, 1, 2]
def added443 : List (List Vertex) := [[1, 7, 3, 5, 4, 0, 2, 6], [2, 7, 0, 6, 5, 1]]
theorem accepted443 : OriginalAccepted (decode 443) 1 0 1
    tail443 added443 := by decide

def tail444 : List Vertex := [6, 4, 3, 0, 2, 1]
def added444 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 4, 0], [6, 7, 1, 0]]
theorem accepted444 : OriginalAccepted (decode 444) 2 1 1
    tail444 added444 := by decide

def tail445 : List Vertex := [6, 2, 1, 0, 3, 4]
def added445 : List (List Vertex) := [[4, 5, 3, 7, 1, 6, 0, 2], [2, 7, 5, 0, 4, 6]]
theorem accepted445 : OriginalAccepted (decode 445) 0 2 1
    tail445 added445 := by decide

def tail446 : List Vertex := [7, 2, 1, 0, 4, 3]
def added446 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 0, 2], [2, 6, 5, 0, 3, 7]]
theorem accepted446 : OriginalAccepted (decode 446) 0 1 2
    tail446 added446 := by decide

def tail452 : List Vertex := [6, 3, 4, 0, 1, 2]
def added452 : List (List Vertex) := [[2, 0, 3, 7, 6, 1, 5, 4], [4, 6]]
theorem accepted452 : OriginalAccepted (decode 452) 1 2 1
    tail452 added452 := by decide

def tail453 : List Vertex := [6, 3, 4, 0, 1, 2]
def added453 : List (List Vertex) := [[2, 0, 3, 7, 5, 1, 6, 4], [4, 5, 0, 6]]
theorem accepted453 : OriginalAccepted (decode 453) 0 2 1
    tail453 added453 := by decide

def tail454 : List Vertex := [7, 3, 4, 0, 1, 2]
def added454 : List (List Vertex) := [[2, 0, 3, 6, 1, 5, 4], [4, 6, 5, 0, 7]]
theorem accepted454 : OriginalAccepted (decode 454) 0 1 2
    tail454 added454 := by decide

def tail457 : List Vertex := [6, 3, 4, 0, 1, 2]
def added457 : List (List Vertex) := [[2, 0, 3, 7, 1, 5, 6, 4], [4, 5, 0, 6]]
theorem accepted457 : OriginalAccepted (decode 457) 0 1 1
    tail457 added457 := by decide

def tail458 : List Vertex := [5, 4, 3, 0, 1, 2]
def added458 : List (List Vertex) := [[2, 0, 4, 6, 3, 7, 5, 1], [1, 7, 0, 5]]
theorem accepted458 : OriginalAccepted (decode 458) 2 0 0
    tail458 added458 := by decide

def tail459 : List Vertex := [6, 4, 3, 0, 1, 2]
def added459 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 6, 3], [3, 7, 0, 6]]
theorem accepted459 : OriginalAccepted (decode 459) 2 1 1
    tail459 added459 := by decide

def tail460 : List Vertex := [6, 4, 3, 0, 1, 2]
def added460 : List (List Vertex) := [[2, 0, 4, 5, 6, 1, 7, 3], [3, 6]]
theorem accepted460 : OriginalAccepted (decode 460) 1 0 1
    tail460 added460 := by decide

def tail462 : List Vertex := [5, 4, 3, 0, 1, 2]
def added462 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 3], [3, 6, 7, 0, 5]]
theorem accepted462 : OriginalAccepted (decode 462) 2 1 0
    tail462 added462 := by decide

def tail463 : List Vertex := [6, 4, 3, 0, 1, 2]
def added463 : List (List Vertex) := [[2, 0, 4, 5, 7, 1, 6, 3], [3, 7, 0, 6]]
theorem accepted463 : OriginalAccepted (decode 463) 2 0 1
    tail463 added463 := by decide

def tail464 : List Vertex := [6, 3, 4, 0, 2, 1]
def added464 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6]]
theorem accepted464 : OriginalAccepted (decode 464) 1 2 1
    tail464 added464 := by decide

def tail465 : List Vertex := [6, 3, 4, 0, 2, 1]
def added465 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5, 0, 6]]
theorem accepted465 : OriginalAccepted (decode 465) 0 2 1
    tail465 added465 := by decide

def tail466 : List Vertex := [7, 3, 4, 0, 2, 1]
def added466 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 4], [4, 6, 5, 0, 7]]
theorem accepted466 : OriginalAccepted (decode 466) 0 1 2
    tail466 added466 := by decide

def tail468 : List Vertex := [6, 3, 4, 0, 2, 1]
def added468 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5, 1, 6]]
theorem accepted468 : OriginalAccepted (decode 468) 0 2 1
    tail468 added468 := by decide

def tail472 : List Vertex := [6, 3, 4, 0, 1, 2]
def added472 : List (List Vertex) := [[2, 6, 4, 5, 1, 7, 3, 0], [6, 5, 2, 0]]
theorem accepted472 : OriginalAccepted (decode 472) 0 1 1
    tail472 added472 := by decide

def tail474 : List Vertex := [7, 3, 4, 0, 2, 1]
def added474 : List (List Vertex) := [[2, 5, 4, 6, 3, 0, 1, 7], [1, 5, 0, 7, 6, 2]]
theorem accepted474 : OriginalAccepted (decode 474) 2 1 2
    tail474 added474 := by decide

def tail475 : List Vertex := [7, 1, 2, 0, 4, 3]
def added475 : List (List Vertex) := [[4, 6, 2, 5, 1, 0, 3, 7], [3, 6, 0, 7, 5, 4]]
theorem accepted475 : OriginalAccepted (decode 475) 2 0 2
    tail475 added475 := by decide

def tail478 : List Vertex := [5, 4, 3, 0, 2, 1]
def added478 : List (List Vertex) := [[1, 7, 3, 6, 2, 5, 0, 4], [4, 6, 1, 0, 7, 5]]
theorem accepted478 : OriginalAccepted (decode 478) 2 0 0
    tail478 added478 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
