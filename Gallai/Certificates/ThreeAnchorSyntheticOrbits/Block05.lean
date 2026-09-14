/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector428 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added428 : List (List Vertex) := [[2, 5, 3, 7, 1, 6, 4, 0], [2, 0]]
theorem accepted428 : SyntheticAccepted (decode 428) 2 0
    connector428 added428 := by decide

def connector429 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added429 : List (List Vertex) := [[3, 7, 2, 5, 4, 0, 1, 6], [3, 5, 0, 6]]
theorem accepted429 : SyntheticAccepted (decode 429) 1 2
    connector429 added429 := by decide

def connector431 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added431 : List (List Vertex) := [[2, 5, 3, 7, 1, 0, 4, 6], [2, 7, 0, 6]]
theorem accepted431 : SyntheticAccepted (decode 431) 1 0
    connector431 added431 := by decide

def connector433 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added433 : List (List Vertex) := [[2, 7, 3, 0, 6, 4, 5], [2, 0, 5]]
theorem accepted433 : SyntheticAccepted (decode 433) 1 0
    connector433 added433 := by decide

def connector434 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added434 : List (List Vertex) := [[2, 6, 4, 0, 7, 3, 5], [2, 0, 5]]
theorem accepted434 : SyntheticAccepted (decode 434) 2 0
    connector434 added434 := by decide

def connector435 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added435 : List (List Vertex) := [[2, 6, 0, 4, 5, 3, 7], [2, 0, 7]]
theorem accepted435 : SyntheticAccepted (decode 435) 2 1
    connector435 added435 := by decide

def connector436 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added436 : List (List Vertex) := [[1, 5, 4, 6, 2, 7, 3, 0], [1, 0]]
theorem accepted436 : SyntheticAccepted (decode 436) 1 0
    connector436 added436 := by decide

def connector438 : List Vertex := [7, 3, 4, 0, 1, 2, 6]
def added438 : List (List Vertex) := [[4, 6, 1, 5, 3, 0, 2, 7], [4, 5, 0, 7]]
theorem accepted438 : SyntheticAccepted (decode 438) 2 1
    connector438 added438 := by decide

def connector439 : List Vertex := [7, 2, 1, 0, 4, 3, 5]
def added439 : List (List Vertex) := [[1, 5, 4, 6, 2, 0, 3, 7], [1, 6, 0, 7]]
theorem accepted439 : SyntheticAccepted (decode 439) 2 0
    connector439 added439 := by decide

def connector440 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added440 : List (List Vertex) := [[1, 5, 3, 7, 2, 6, 4, 0], [1, 0]]
theorem accepted440 : SyntheticAccepted (decode 440) 2 0
    connector440 added440 := by decide

def connector441 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added441 : List (List Vertex) := [[3, 7, 1, 5, 4, 0, 2, 6], [3, 5, 0, 6]]
theorem accepted441 : SyntheticAccepted (decode 441) 1 2
    connector441 added441 := by decide

def connector443 : List Vertex := [6, 2, 1, 0, 3, 4, 5]
def added443 : List (List Vertex) := [[1, 5, 3, 7, 2, 0, 4, 6], [1, 7, 0, 6]]
theorem accepted443 : SyntheticAccepted (decode 443) 1 0
    connector443 added443 := by decide

def connector444 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added444 : List (List Vertex) := [[1, 6, 2, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted444 : SyntheticAccepted (decode 444) 2 1
    connector444 added444 := by decide

def connector445 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added445 : List (List Vertex) := [[4, 6, 1, 7, 3, 5, 0, 2], [4, 0, 6, 2]]
theorem accepted445 : SyntheticAccepted (decode 445) 0 2
    connector445 added445 := by decide

def connector446 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added446 : List (List Vertex) := [[3, 7, 1, 6, 4, 5, 0, 2], [3, 0, 7, 2]]
theorem accepted446 : SyntheticAccepted (decode 446) 0 1
    connector446 added446 := by decide

def connector452 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added452 : List (List Vertex) := [[1, 5, 4, 6, 3, 0], [1, 0]]
theorem accepted452 : SyntheticAccepted (decode 452) 1 2
    connector452 added452 := by decide

def connector453 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added453 : List (List Vertex) := [[1, 6, 4, 5, 0, 3], [1, 0, 6, 3]]
theorem accepted453 : SyntheticAccepted (decode 453) 0 2
    connector453 added453 := by decide

def connector454 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added454 : List (List Vertex) := [[1, 6, 4, 5, 0, 3, 7], [1, 0, 7]]
theorem accepted454 : SyntheticAccepted (decode 454) 0 1
    connector454 added454 := by decide

def connector457 : List Vertex := [5, 1, 2, 0, 4, 3, 6]
def added457 : List (List Vertex) := [[1, 7, 3, 0, 5, 4, 6], [1, 0, 6]]
theorem accepted457 : SyntheticAccepted (decode 457) 0 1
    connector457 added457 := by decide

def connector458 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added458 : List (List Vertex) := [[1, 5, 0, 4, 6, 3, 7], [1, 0, 7]]
theorem accepted458 : SyntheticAccepted (decode 458) 2 0
    connector458 added458 := by decide

def connector459 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added459 : List (List Vertex) := [[1, 5, 4, 0, 7, 3, 6], [1, 0, 6]]
theorem accepted459 : SyntheticAccepted (decode 459) 2 1
    connector459 added459 := by decide

def connector460 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added460 : List (List Vertex) := [[1, 7, 3, 6, 4, 0], [1, 0]]
theorem accepted460 : SyntheticAccepted (decode 460) 1 0
    connector460 added460 := by decide

def connector462 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added462 : List (List Vertex) := [[1, 6, 3, 7, 0, 4, 5], [1, 0, 5]]
theorem accepted462 : SyntheticAccepted (decode 462) 2 1
    connector462 added462 := by decide

def connector463 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added463 : List (List Vertex) := [[1, 6, 3, 7, 0, 4], [1, 0, 6, 4]]
theorem accepted463 : SyntheticAccepted (decode 463) 2 0
    connector463 added463 := by decide

def connector464 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added464 : List (List Vertex) := [[2, 5, 4, 6, 3, 0], [2, 0]]
theorem accepted464 : SyntheticAccepted (decode 464) 1 2
    connector464 added464 := by decide

def connector465 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added465 : List (List Vertex) := [[2, 6, 4, 5, 0, 3], [2, 0, 6, 3]]
theorem accepted465 : SyntheticAccepted (decode 465) 0 2
    connector465 added465 := by decide

def connector466 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added466 : List (List Vertex) := [[2, 6, 4, 5, 0, 3, 7], [2, 0, 7]]
theorem accepted466 : SyntheticAccepted (decode 466) 0 1
    connector466 added466 := by decide

def connector468 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added468 : List (List Vertex) := [[1, 0, 3, 6, 2, 5, 4], [1, 6, 4]]
theorem accepted468 : SyntheticAccepted (decode 468) 0 2
    connector468 added468 := by decide

def connector472 : List Vertex := [5, 2, 1, 0, 4, 3, 6]
def added472 : List (List Vertex) := [[2, 6, 4, 5, 1, 7, 3, 0], [2, 0]]
theorem accepted472 : SyntheticAccepted (decode 472) 0 1
    connector472 added472 := by decide

def connector474 : List Vertex := [7, 1, 2, 0, 4, 3, 6]
def added474 : List (List Vertex) := [[2, 6, 4, 5, 1, 0, 3, 7], [2, 5, 0, 7]]
theorem accepted474 : SyntheticAccepted (decode 474) 2 1
    connector474 added474 := by decide

def connector475 : List Vertex := [7, 3, 4, 0, 2, 1, 5]
def added475 : List (List Vertex) := [[4, 5, 2, 6, 3, 0, 1, 7], [4, 6, 0, 7]]
theorem accepted475 : SyntheticAccepted (decode 475) 2 0
    connector475 added475 := by decide

def connector478 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added478 : List (List Vertex) := [[1, 6, 2, 5, 0, 7, 3], [1, 0, 4, 6, 3]]
theorem accepted478 : SyntheticAccepted (decode 478) 2 0
    connector478 added478 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
