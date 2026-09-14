/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails436 : List (List Vertex) := [[6, 5, 4, 0, 3, 7, 2, 1], [5, 3, 4, 6, 2, 0, 1]]
def added436 : List (List Vertex) := [[6, 1, 5]]
def attachments436 : Fin tails436.length → Fin 3 := ![1, 0]
theorem accepted436 : CheapOriginalAccepted (decode 436) 1 0
    tails436 added436 attachments436 := by decide

def tails438 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 6, 2, 0, 4, 5, 3]]
def added438 : List (List Vertex) := [[5, 1, 0, 3, 7]]
def attachments438 : Fin tails438.length → Fin 3 := ![0, 2]
theorem accepted438 : CheapOriginalAccepted (decode 438) 2 1
    tails438 added438 attachments438 := by decide

def tails439 : List (List Vertex) := [[6, 0, 7, 3, 4, 5, 1, 2], [7, 5, 3, 0, 1, 6, 2]]
def added439 : List (List Vertex) := [[6, 4, 0, 2, 7]]
def attachments439 : Fin tails439.length → Fin 3 := ![1, 2]
theorem accepted439 : CheapOriginalAccepted (decode 439) 2 0
    tails439 added439 attachments439 := by decide

def tails440 : List (List Vertex) := [[7, 5, 3, 0, 4, 6, 2, 1], [5, 4, 3, 7, 2, 0, 1]]
def added440 : List (List Vertex) := [[7, 1, 5]]
def attachments440 : Fin tails440.length → Fin 3 := ![2, 0]
theorem accepted440 : CheapOriginalAccepted (decode 440) 2 0
    tails440 added440 attachments440 := by decide

def tails441 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 7, 2, 0, 3, 5, 4]]
def added441 : List (List Vertex) := [[5, 1, 0, 4, 6]]
def attachments441 : Fin tails441.length → Fin 3 := ![0, 1]
theorem accepted441 : CheapOriginalAccepted (decode 441) 1 2
    tails441 added441 attachments441 := by decide

def tails443 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 5, 4, 0, 1, 7, 2]]
def added443 : List (List Vertex) := [[7, 3, 0, 2, 6]]
def attachments443 : Fin tails443.length → Fin 3 := ![2, 1]
theorem accepted443 : CheapOriginalAccepted (decode 443) 1 0
    tails443 added443 attachments443 := by decide

def tails444 : List (List Vertex) := [[7, 6, 4, 5, 3, 0, 2, 1], [6, 2, 7, 3, 4, 0, 1]]
def added444 : List (List Vertex) := [[7, 1, 6]]
def attachments444 : Fin tails444.length → Fin 3 := ![2, 1]
theorem accepted444 : CheapOriginalAccepted (decode 444) 2 1
    tails444 added444 attachments444 := by decide

def tails445 : List (List Vertex) := [[5, 0, 6, 2, 1, 7, 3, 4], [6, 1, 0, 2, 7, 5, 4]]
def added445 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments445 : Fin tails445.length → Fin 3 := ![0, 1]
theorem accepted445 : CheapOriginalAccepted (decode 445) 0 2
    tails445 added445 attachments445 := by decide

def tails446 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 1, 0, 2, 6, 5, 3]]
def added446 : List (List Vertex) := [[5, 4, 0, 3, 7]]
def attachments446 : Fin tails446.length → Fin 3 := ![0, 2]
theorem accepted446 : CheapOriginalAccepted (decode 446) 0 1
    tails446 added446 attachments446 := by decide

def tails452 : List (List Vertex) := [[6, 7, 3, 4, 0, 2, 1, 5], [5, 4, 6, 3, 0, 1]]
def added452 : List (List Vertex) := [[1, 6]]
def attachments452 : Fin tails452.length → Fin 3 := ![1, 0]
theorem accepted452 : CheapOriginalAccepted (decode 452) 1 2
    tails452 added452 attachments452 := by decide

def tails453 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 1, 2], [5, 4, 6, 1, 0, 2]]
def added453 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments453 : Fin tails453.length → Fin 3 := ![1, 0]
theorem accepted453 : CheapOriginalAccepted (decode 453) 0 2
    tails453 added453 attachments453 := by decide

def tails454 : List (List Vertex) := [[5, 1, 2, 0, 4, 6, 3, 7], [7, 0, 3, 4, 5, 6, 1]]
def added454 : List (List Vertex) := [[1, 0, 5]]
def attachments454 : Fin tails454.length → Fin 3 := ![0, 2]
theorem accepted454 : CheapOriginalAccepted (decode 454) 0 1
    tails454 added454 attachments454 := by decide

def tails457 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 5, 1, 0, 2]]
def added457 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments457 : Fin tails457.length → Fin 3 := ![0, 1]
theorem accepted457 : CheapOriginalAccepted (decode 457) 0 1
    tails457 added457 attachments457 := by decide

def tails458 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 1, 2], [5, 7, 3, 4, 0, 2]]
def added458 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments458 : Fin tails458.length → Fin 3 := ![2, 0]
theorem accepted458 : CheapOriginalAccepted (decode 458) 2 0
    tails458 added458 attachments458 := by decide

def tails459 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 1, 2], [6, 7, 1, 0, 2]]
def added459 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments459 : Fin tails459.length → Fin 3 := ![2, 1]
theorem accepted459 : CheapOriginalAccepted (decode 459) 2 1
    tails459 added459 attachments459 := by decide

def tails460 : List (List Vertex) := [[6, 5, 4, 3, 0, 2, 1, 7], [7, 3, 6, 4, 0, 1]]
def added460 : List (List Vertex) := [[1, 6]]
def attachments460 : Fin tails460.length → Fin 3 := ![1, 2]
theorem accepted460 : CheapOriginalAccepted (decode 460) 1 0
    tails460 added460 attachments460 := by decide

def tails462 : List (List Vertex) := [[7, 1, 2, 0, 3, 6, 4, 5], [5, 0, 4, 3, 7, 6, 1]]
def added462 : List (List Vertex) := [[1, 0, 7]]
def attachments462 : Fin tails462.length → Fin 3 := ![2, 0]
theorem accepted462 : CheapOriginalAccepted (decode 462) 2 1
    tails462 added462 attachments462 := by decide

def tails463 : List (List Vertex) := [[6, 0, 3, 4, 5, 7, 1, 2], [7, 3, 6, 1, 0, 2]]
def added463 : List (List Vertex) := [[6, 4, 0, 7]]
def attachments463 : Fin tails463.length → Fin 3 := ![1, 2]
theorem accepted463 : CheapOriginalAccepted (decode 463) 2 0
    tails463 added463 attachments463 := by decide

def tails464 : List (List Vertex) := [[6, 7, 3, 4, 0, 1, 2, 5], [5, 4, 6, 3, 0, 2]]
def added464 : List (List Vertex) := [[2, 6]]
def attachments464 : Fin tails464.length → Fin 3 := ![1, 0]
theorem accepted464 : CheapOriginalAccepted (decode 464) 1 2
    tails464 added464 attachments464 := by decide

def tails465 : List (List Vertex) := [[6, 0, 4, 3, 7, 5, 2, 1], [5, 4, 6, 2, 0, 1]]
def added465 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments465 : Fin tails465.length → Fin 3 := ![1, 0]
theorem accepted465 : CheapOriginalAccepted (decode 465) 0 2
    tails465 added465 attachments465 := by decide

def tails466 : List (List Vertex) := [[5, 2, 1, 0, 4, 6, 3, 7], [7, 0, 3, 4, 5, 6, 2]]
def added466 : List (List Vertex) := [[2, 0, 5]]
def attachments466 : Fin tails466.length → Fin 3 := ![0, 2]
theorem accepted466 : CheapOriginalAccepted (decode 466) 0 1
    tails466 added466 attachments466 := by decide

def tails468 : List (List Vertex) := [[6, 4, 0, 3, 7, 5, 2, 1], [5, 4, 3, 6, 2, 0, 1]]
def added468 : List (List Vertex) := [[6, 1, 5]]
def attachments468 : Fin tails468.length → Fin 3 := ![1, 0]
theorem accepted468 : CheapOriginalAccepted (decode 468) 0 2
    tails468 added468 attachments468 := by decide

def tails472 : List (List Vertex) := [[5, 6, 4, 0, 3, 7, 1, 2], [6, 3, 4, 5, 1, 0, 2]]
def added472 : List (List Vertex) := [[5, 2, 6]]
def attachments472 : Fin tails472.length → Fin 3 := ![0, 1]
theorem accepted472 : CheapOriginalAccepted (decode 472) 0 1
    tails472 added472 attachments472 := by decide

def tails474 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 2, 1], [7, 6, 3, 0, 2, 5, 1]]
def added474 : List (List Vertex) := [[5, 4, 0, 1, 7]]
def attachments474 : Fin tails474.length → Fin 3 := ![0, 2]
theorem accepted474 : CheapOriginalAccepted (decode 474) 2 1
    tails474 added474 attachments474 := by decide

def tails475 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 4, 3], [7, 5, 1, 0, 4, 6, 3]]
def added475 : List (List Vertex) := [[6, 2, 0, 3, 7]]
def attachments475 : Fin tails475.length → Fin 3 := ![1, 2]
theorem accepted475 : CheapOriginalAccepted (decode 475) 2 0
    tails475 added475 attachments475 := by decide

def tails478 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 2, 1], [5, 7, 3, 4, 0, 2, 6, 1]]
def added478 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments478 : Fin tails478.length → Fin 3 := ![2, 0]
theorem accepted478 : CheapOriginalAccepted (decode 478) 2 0
    tails478 added478 attachments478 := by decide

def tails481 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 2, 1], [6, 5, 2, 0, 1]]
def added481 : List (List Vertex) := [[5, 4, 0, 3, 6]]
def attachments481 : Fin tails481.length → Fin 3 := ![0, 1]
theorem accepted481 : CheapOriginalAccepted (decode 481) 0 1
    tails481 added481 attachments481 := by decide

def tails482 : List (List Vertex) := [[7, 0, 3, 6, 4, 5, 2, 1], [5, 7, 3, 4, 0, 1]]
def added482 : List (List Vertex) := [[7, 2, 0, 5]]
def attachments482 : Fin tails482.length → Fin 3 := ![2, 0]
theorem accepted482 : CheapOriginalAccepted (decode 482) 2 0
    tails482 added482 attachments482 := by decide

def tails483 : List (List Vertex) := [[7, 0, 6, 3, 4, 5, 2, 1], [6, 7, 2, 0, 1]]
def added483 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments483 : Fin tails483.length → Fin 3 := ![2, 1]
theorem accepted483 : CheapOriginalAccepted (decode 483) 2 1
    tails483 added483 attachments483 := by decide

def tails484 : List (List Vertex) := [[5, 6, 4, 0, 3, 7, 2, 1], [6, 3, 4, 5, 2, 0, 1]]
def added484 : List (List Vertex) := [[5, 1, 6]]
def attachments484 : Fin tails484.length → Fin 3 := ![0, 1]
theorem accepted484 : CheapOriginalAccepted (decode 484) 0 1
    tails484 added484 attachments484 := by decide

def tails486 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 1, 2], [7, 6, 3, 0, 1, 5, 2]]
def added486 : List (List Vertex) := [[5, 4, 0, 2, 7]]
def attachments486 : Fin tails486.length → Fin 3 := ![0, 2]
theorem accepted486 : CheapOriginalAccepted (decode 486) 2 1
    tails486 added486 attachments486 := by decide

def tails487 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 5, 2, 0, 4, 6, 3]]
def added487 : List (List Vertex) := [[6, 1, 0, 3, 7]]
def attachments487 : Fin tails487.length → Fin 3 := ![1, 2]
theorem accepted487 : CheapOriginalAccepted (decode 487) 2 0
    tails487 added487 attachments487 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
