/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails309 : List (List Vertex) := [[6, 0, 1, 2, 7, 5, 4, 3], [5, 1, 6, 4, 0, 3]]
def added309 : List (List Vertex) := [[6, 2, 0, 5]]
def attachments309 : Fin tails309.length → Fin 3 := ![1, 0]
theorem accepted309 : CheapOriginalAccepted (decode 309) 0 2
    tails309 added309 attachments309 := by decide

def tails310 : List (List Vertex) := [[5, 4, 3, 0, 1, 6, 2, 7], [7, 0, 2, 1, 5, 6, 4]]
def added310 : List (List Vertex) := [[4, 0, 5]]
def attachments310 : Fin tails310.length → Fin 3 := ![0, 2]
theorem accepted310 : CheapOriginalAccepted (decode 310) 0 1
    tails310 added310 attachments310 := by decide

def tails313 : List (List Vertex) := [[5, 0, 1, 7, 2, 6, 4, 3], [6, 5, 1, 2, 0, 3]]
def added313 : List (List Vertex) := [[5, 4, 0, 6]]
def attachments313 : Fin tails313.length → Fin 3 := ![0, 1]
theorem accepted313 : CheapOriginalAccepted (decode 313) 0 1
    tails313 added313 attachments313 := by decide

def tails314 : List (List Vertex) := [[5, 0, 7, 1, 2, 6, 4, 3], [7, 5, 4, 0, 3]]
def added314 : List (List Vertex) := [[5, 1, 0, 2, 7]]
def attachments314 : Fin tails314.length → Fin 3 := ![0, 2]
theorem accepted314 : CheapOriginalAccepted (decode 314) 0 2
    tails314 added314 attachments314 := by decide

def tails315 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 4, 3], [7, 6, 4, 0, 3]]
def added315 : List (List Vertex) := [[6, 2, 0, 1, 7]]
def attachments315 : Fin tails315.length → Fin 3 := ![1, 2]
theorem accepted315 : CheapOriginalAccepted (decode 315) 1 2
    tails315 added315 attachments315 := by decide

def tails316 : List (List Vertex) := [[6, 1, 7, 2, 0, 3, 4, 5], [5, 6, 2, 1, 0, 4]]
def added316 : List (List Vertex) := [[4, 6]]
def attachments316 : Fin tails316.length → Fin 3 := ![1, 0]
theorem accepted316 : CheapOriginalAccepted (decode 316) 1 0
    tails316 added316 attachments316 := by decide

def tails318 : List (List Vertex) := [[5, 0, 7, 2, 1, 6, 4, 3], [7, 6, 2, 0, 4, 5]]
def added318 : List (List Vertex) := [[3, 0, 1, 7]]
def attachments318 : Fin tails318.length → Fin 3 := ![0, 2]
theorem accepted318 : CheapOriginalAccepted (decode 318) 2 1
    tails318 added318 attachments318 := by decide

def tails319 : List (List Vertex) := [[6, 0, 2, 1, 7, 5, 4, 3], [7, 2, 6, 4, 0, 3]]
def added319 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments319 : Fin tails319.length → Fin 3 := ![1, 2]
theorem accepted319 : CheapOriginalAccepted (decode 319) 2 0
    tails319 added319 attachments319 := by decide

def tails326 : List (List Vertex) := [[5, 1, 2, 0, 3, 4, 6, 7], [7, 0, 4, 5, 3, 6, 1]]
def added326 : List (List Vertex) := [[1, 0, 5]]
def attachments326 : Fin tails326.length → Fin 3 := ![0, 2]
theorem accepted326 : CheapOriginalAccepted (decode 326) 2 1
    tails326 added326 attachments326 := by decide

def tails327 : List (List Vertex) := [[6, 1, 2, 0, 3, 4, 5, 7], [7, 0, 4, 6, 3, 5, 1]]
def added327 : List (List Vertex) := [[1, 0, 6]]
def attachments327 : Fin tails327.length → Fin 3 := ![1, 2]
theorem accepted327 : CheapOriginalAccepted (decode 327) 2 0
    tails327 added327 attachments327 := by decide

def tails328 : List (List Vertex) := [[5, 3, 6, 4, 0, 2, 1, 7], [7, 5, 4, 3, 0, 1]]
def added328 : List (List Vertex) := [[1, 5]]
def attachments328 : Fin tails328.length → Fin 3 := ![0, 2]
theorem accepted328 : CheapOriginalAccepted (decode 328) 0 2
    tails328 added328 attachments328 := by decide

def tails329 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 1, 2], [6, 4, 5, 1, 0, 2]]
def added329 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments329 : Fin tails329.length → Fin 3 := ![0, 1]
theorem accepted329 : CheapOriginalAccepted (decode 329) 1 2
    tails329 added329 attachments329 := by decide

def tails331 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 5, 4, 0, 1, 7]]
def added331 : List (List Vertex) := [[2, 0, 3, 6]]
def attachments331 : Fin tails331.length → Fin 3 := ![2, 1]
theorem accepted331 : CheapOriginalAccepted (decode 331) 1 0
    tails331 added331 attachments331 := by decide

def tails332 : List (List Vertex) := [[6, 3, 5, 4, 0, 2, 1, 7], [7, 6, 4, 3, 0, 1]]
def added332 : List (List Vertex) := [[1, 6]]
def attachments332 : Fin tails332.length → Fin 3 := ![1, 2]
theorem accepted332 : CheapOriginalAccepted (decode 332) 1 2
    tails332 added332 attachments332 := by decide

def tails333 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 1, 2], [5, 4, 6, 1, 0, 2]]
def added333 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments333 : Fin tails333.length → Fin 3 := ![1, 0]
theorem accepted333 : CheapOriginalAccepted (decode 333) 0 2
    tails333 added333 attachments333 := by decide

def tails334 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 6, 4, 0, 1, 7]]
def added334 : List (List Vertex) := [[2, 0, 3, 5]]
def attachments334 : Fin tails334.length → Fin 3 := ![2, 0]
theorem accepted334 : CheapOriginalAccepted (decode 334) 0 1
    tails334 added334 attachments334 := by decide

def tails338 : List (List Vertex) := [[5, 2, 1, 0, 3, 4, 6, 7], [7, 0, 4, 5, 3, 6, 2]]
def added338 : List (List Vertex) := [[2, 0, 5]]
def attachments338 : Fin tails338.length → Fin 3 := ![0, 2]
theorem accepted338 : CheapOriginalAccepted (decode 338) 2 1
    tails338 added338 attachments338 := by decide

def tails339 : List (List Vertex) := [[6, 2, 1, 0, 3, 4, 5, 7], [7, 0, 4, 6, 3, 5, 2]]
def added339 : List (List Vertex) := [[2, 0, 6]]
def attachments339 : Fin tails339.length → Fin 3 := ![1, 2]
theorem accepted339 : CheapOriginalAccepted (decode 339) 2 0
    tails339 added339 attachments339 := by decide

def tails344 : List (List Vertex) := [[5, 2, 0, 1, 7, 6, 4, 3], [6, 2, 1, 5, 4, 0, 3]]
def added344 : List (List Vertex) := [[5, 3, 6]]
def attachments344 : Fin tails344.length → Fin 3 := ![0, 1]
theorem accepted344 : CheapOriginalAccepted (decode 344) 1 2
    tails344 added344 attachments344 := by decide

def tails348 : List (List Vertex) := [[6, 2, 0, 1, 7, 5, 4, 3], [5, 2, 1, 6, 4, 0, 3]]
def added348 : List (List Vertex) := [[6, 3, 5]]
def attachments348 : Fin tails348.length → Fin 3 := ![1, 0]
theorem accepted348 : CheapOriginalAccepted (decode 348) 0 2
    tails348 added348 attachments348 := by decide

def tails352 : List (List Vertex) := [[5, 3, 6, 4, 0, 1, 2, 7], [7, 5, 4, 3, 0, 2]]
def added352 : List (List Vertex) := [[2, 5]]
def attachments352 : Fin tails352.length → Fin 3 := ![0, 2]
theorem accepted352 : CheapOriginalAccepted (decode 352) 0 2
    tails352 added352 attachments352 := by decide

def tails353 : List (List Vertex) := [[5, 0, 4, 3, 6, 7, 2, 1], [6, 4, 5, 2, 0, 1]]
def added353 : List (List Vertex) := [[5, 3, 0, 6]]
def attachments353 : Fin tails353.length → Fin 3 := ![0, 1]
theorem accepted353 : CheapOriginalAccepted (decode 353) 1 2
    tails353 added353 attachments353 := by decide

def tails355 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 5, 4, 0, 2, 7]]
def added355 : List (List Vertex) := [[1, 0, 3, 6]]
def attachments355 : Fin tails355.length → Fin 3 := ![2, 1]
theorem accepted355 : CheapOriginalAccepted (decode 355) 1 0
    tails355 added355 attachments355 := by decide

def tails356 : List (List Vertex) := [[5, 1, 0, 2, 7, 6, 4, 3], [6, 1, 2, 5, 4, 0, 3]]
def added356 : List (List Vertex) := [[5, 3, 6]]
def attachments356 : Fin tails356.length → Fin 3 := ![0, 1]
theorem accepted356 : CheapOriginalAccepted (decode 356) 1 2
    tails356 added356 attachments356 := by decide

def tails363 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 7, 2, 0, 4, 5, 1]]
def added363 : List (List Vertex) := [[7, 1, 0, 3, 6]]
def attachments363 : Fin tails363.length → Fin 3 := ![2, 1]
theorem accepted363 : CheapOriginalAccepted (decode 363) 2 1
    tails363 added363 attachments363 := by decide

def tails364 : List (List Vertex) := [[6, 5, 2, 7, 1, 0, 4, 3], [5, 4, 6, 1, 2, 0, 3]]
def added364 : List (List Vertex) := [[6, 3, 5]]
def attachments364 : Fin tails364.length → Fin 3 := ![1, 0]
theorem accepted364 : CheapOriginalAccepted (decode 364) 1 0
    tails364 added364 attachments364 := by decide

def tails366 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 1, 2], [5, 3, 0, 4, 6, 7, 2]]
def added366 : List (List Vertex) := [[7, 1, 0, 2, 5]]
def attachments366 : Fin tails366.length → Fin 3 := ![2, 0]
theorem accepted366 : CheapOriginalAccepted (decode 366) 2 1
    tails366 added366 attachments366 := by decide

def tails367 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 3, 0, 4, 5, 7, 1]]
def added367 : List (List Vertex) := [[7, 2, 0, 1, 6]]
def attachments367 : Fin tails367.length → Fin 3 := ![2, 1]
theorem accepted367 : CheapOriginalAccepted (decode 367) 2 0
    tails367 added367 attachments367 := by decide

def tails368 : List (List Vertex) := [[6, 3, 5, 4, 0, 1, 2, 7], [7, 6, 4, 3, 0, 2]]
def added368 : List (List Vertex) := [[2, 6]]
def attachments368 : Fin tails368.length → Fin 3 := ![1, 2]
theorem accepted368 : CheapOriginalAccepted (decode 368) 1 2
    tails368 added368 attachments368 := by decide

def tails369 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 2, 1], [5, 4, 6, 2, 0, 1]]
def added369 : List (List Vertex) := [[6, 3, 0, 5]]
def attachments369 : Fin tails369.length → Fin 3 := ![1, 0]
theorem accepted369 : CheapOriginalAccepted (decode 369) 0 2
    tails369 added369 attachments369 := by decide

def tails370 : List (List Vertex) := [[7, 0, 5, 4, 3, 6, 2, 1], [5, 6, 4, 0, 2, 7]]
def added370 : List (List Vertex) := [[1, 0, 3, 5]]
def attachments370 : Fin tails370.length → Fin 3 := ![2, 0]
theorem accepted370 : CheapOriginalAccepted (decode 370) 0 1
    tails370 added370 attachments370 := by decide

def tails372 : List (List Vertex) := [[6, 1, 0, 2, 7, 5, 4, 3], [5, 1, 2, 6, 4, 0, 3]]
def added372 : List (List Vertex) := [[6, 3, 5]]
def attachments372 : Fin tails372.length → Fin 3 := ![1, 0]
theorem accepted372 : CheapOriginalAccepted (decode 372) 0 2
    tails372 added372 attachments372 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
