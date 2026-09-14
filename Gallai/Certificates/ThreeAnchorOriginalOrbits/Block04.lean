/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail366 : List Vertex := [5, 4, 3, 0, 1, 2]
def added366 : List (List Vertex) := [[2, 7, 1, 6, 3, 5, 0, 4], [4, 6, 7, 0, 2, 5]]
theorem accepted366 : OriginalAccepted (decode 366) 2 1 0
    tail366 added366 := by decide

def tail367 : List Vertex := [6, 4, 3, 0, 2, 1]
def added367 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 0, 4], [4, 5, 7, 0, 1, 6]]
theorem accepted367 : OriginalAccepted (decode 367) 2 0 1
    tail367 added367 := by decide

def tail368 : List Vertex := [6, 4, 3, 0, 2, 1]
def added368 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 2, 7], [6, 7]]
theorem accepted368 : OriginalAccepted (decode 368) 1 2 1
    tail368 added368 := by decide

def tail369 : List Vertex := [6, 4, 3, 0, 2, 1]
def added369 : List (List Vertex) := [[1, 0, 4, 5, 3, 6, 2, 7], [6, 0, 5, 7]]
theorem accepted369 : OriginalAccepted (decode 369) 0 2 1
    tail369 added369 := by decide

def tail370 : List Vertex := [5, 4, 3, 0, 2, 1]
def added370 : List (List Vertex) := [[1, 0, 7, 2, 6, 5, 3], [3, 6, 4, 0, 5]]
theorem accepted370 : OriginalAccepted (decode 370) 0 1 0
    tail370 added370 := by decide

def tail372 : List Vertex := [6, 2, 1, 0, 4, 3]
def added372 : List (List Vertex) := [[3, 0, 2, 7, 5, 4, 6, 1], [1, 5, 3, 6]]
theorem accepted372 : OriginalAccepted (decode 372) 0 2 1
    tail372 added372 := by decide

def tail376 : List Vertex := [6, 2, 1, 0, 4, 3]
def added376 : List (List Vertex) := [[3, 6, 4, 5, 1, 7, 2, 0], [6, 5, 3, 0]]
theorem accepted376 : OriginalAccepted (decode 376) 0 1 1
    tail376 added376 := by decide

def tail378 : List Vertex := [5, 4, 3, 0, 2, 1]
def added378 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 0, 4], [4, 6, 7, 0, 1, 5]]
theorem accepted378 : OriginalAccepted (decode 378) 2 1 0
    tail378 added378 := by decide

def tail379 : List Vertex := [6, 4, 3, 0, 1, 2]
def added379 : List (List Vertex) := [[2, 7, 1, 5, 3, 6, 0, 4], [4, 5, 7, 0, 2, 6]]
theorem accepted379 : OriginalAccepted (decode 379) 2 0 1
    tail379 added379 := by decide

def tail382 : List Vertex := [5, 4, 3, 0, 2, 1]
def added382 : List (List Vertex) := [[1, 7, 2, 6, 3, 5, 0, 4], [4, 6, 1, 0, 7, 5]]
theorem accepted382 : OriginalAccepted (decode 382) 2 0 0
    tail382 added382 := by decide

def tail388 : List Vertex := [5, 3, 4, 0, 1, 2]
def added388 : List (List Vertex) := [[2, 0, 3, 7, 5, 1, 6, 4], [4, 5]]
theorem accepted388 : OriginalAccepted (decode 388) 0 2 0
    tail388 added388 := by decide

def tail389 : List Vertex := [5, 3, 4, 0, 1, 2]
def added389 : List (List Vertex) := [[2, 0, 3, 7, 6, 1, 5, 4], [4, 6, 0, 5]]
theorem accepted389 : OriginalAccepted (decode 389) 1 2 0
    tail389 added389 := by decide

def tail391 : List Vertex := [7, 3, 4, 0, 1, 2]
def added391 : List (List Vertex) := [[2, 0, 3, 5, 1, 6, 4], [4, 5, 6, 0, 7]]
theorem accepted391 : OriginalAccepted (decode 391) 1 0 2
    tail391 added391 := by decide

def tail392 : List Vertex := [5, 4, 3, 0, 1, 2]
def added392 : List (List Vertex) := [[2, 0, 4, 6, 5, 1, 7, 3], [3, 5]]
theorem accepted392 : OriginalAccepted (decode 392) 0 1 0
    tail392 added392 := by decide

def tail394 : List Vertex := [5, 4, 3, 0, 1, 2]
def added394 : List (List Vertex) := [[2, 0, 4, 6, 7, 1, 5, 3], [3, 7, 0, 5]]
theorem accepted394 : OriginalAccepted (decode 394) 2 1 0
    tail394 added394 := by decide

def tail395 : List Vertex := [6, 4, 3, 0, 1, 2]
def added395 : List (List Vertex) := [[2, 0, 4, 5, 1, 7, 3], [3, 5, 7, 0, 6]]
theorem accepted395 : OriginalAccepted (decode 395) 2 0 1
    tail395 added395 := by decide

def tail397 : List Vertex := [5, 3, 4, 0, 1, 2]
def added397 : List (List Vertex) := [[2, 0, 3, 7, 1, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted397 : OriginalAccepted (decode 397) 1 0 0
    tail397 added397 := by decide

def tail398 : List Vertex := [5, 4, 3, 0, 1, 2]
def added398 : List (List Vertex) := [[2, 0, 4, 6, 1, 7, 5, 3], [3, 7, 0, 5]]
theorem accepted398 : OriginalAccepted (decode 398) 2 0 0
    tail398 added398 := by decide

def tail399 : List Vertex := [6, 4, 3, 0, 1, 2]
def added399 : List (List Vertex) := [[2, 0, 4, 5, 3, 7, 6, 1], [1, 7, 0, 6]]
theorem accepted399 : OriginalAccepted (decode 399) 2 1 1
    tail399 added399 := by decide

def tail400 : List Vertex := [5, 3, 4, 0, 2, 1]
def added400 : List (List Vertex) := [[1, 0, 3, 7, 5, 2, 6, 4], [4, 5]]
theorem accepted400 : OriginalAccepted (decode 400) 0 2 0
    tail400 added400 := by decide

def tail401 : List Vertex := [5, 3, 4, 0, 2, 1]
def added401 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6, 0, 5]]
theorem accepted401 : OriginalAccepted (decode 401) 1 2 0
    tail401 added401 := by decide

def tail403 : List Vertex := [7, 3, 4, 0, 2, 1]
def added403 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 4], [4, 5, 6, 0, 7]]
theorem accepted403 : OriginalAccepted (decode 403) 1 0 2
    tail403 added403 := by decide

def tail404 : List Vertex := [5, 3, 4, 0, 2, 1]
def added404 : List (List Vertex) := [[1, 0, 3, 7, 6, 2, 5, 4], [4, 6, 1, 5]]
theorem accepted404 : OriginalAccepted (decode 404) 1 2 0
    tail404 added404 := by decide

def tail411 : List Vertex := [6, 4, 3, 0, 2, 1]
def added411 : List (List Vertex) := [[1, 7, 3, 5, 2, 6, 0, 4], [4, 5, 1, 0, 7, 6]]
theorem accepted411 : OriginalAccepted (decode 411) 2 1 1
    tail411 added411 := by decide

def tail412 : List Vertex := [5, 3, 4, 0, 1, 2]
def added412 : List (List Vertex) := [[2, 5, 4, 6, 1, 7, 3, 0], [5, 6, 2, 0]]
theorem accepted412 : OriginalAccepted (decode 412) 1 0 0
    tail412 added412 := by decide

def tail414 : List Vertex := [7, 1, 2, 0, 4, 3]
def added414 : List (List Vertex) := [[4, 5, 2, 6, 1, 0, 3, 7], [3, 5, 0, 7, 6, 4]]
theorem accepted414 : OriginalAccepted (decode 414) 2 1 2
    tail414 added414 := by decide

def tail415 : List Vertex := [7, 3, 4, 0, 2, 1]
def added415 : List (List Vertex) := [[2, 6, 4, 5, 3, 0, 1, 7], [1, 6, 0, 7, 5, 2]]
theorem accepted415 : OriginalAccepted (decode 415) 2 0 2
    tail415 added415 := by decide

def tail416 : List Vertex := [5, 4, 3, 0, 2, 1]
def added416 : List (List Vertex) := [[1, 0, 4, 6, 5, 2, 7, 3], [3, 5]]
theorem accepted416 : OriginalAccepted (decode 416) 0 1 0
    tail416 added416 := by decide

def tail418 : List Vertex := [5, 4, 3, 0, 2, 1]
def added418 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7, 0, 5]]
theorem accepted418 : OriginalAccepted (decode 418) 2 1 0
    tail418 added418 := by decide

def tail419 : List Vertex := [6, 4, 3, 0, 2, 1]
def added419 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [3, 5, 7, 0, 6]]
theorem accepted419 : OriginalAccepted (decode 419) 2 0 1
    tail419 added419 := by decide

def tail423 : List Vertex := [7, 3, 4, 0, 2, 1]
def added423 : List (List Vertex) := [[1, 6, 4, 5, 2, 7, 0, 3], [3, 5, 1, 0, 6, 7]]
theorem accepted423 : OriginalAccepted (decode 423) 1 2 2
    tail423 added423 := by decide

def tail424 : List Vertex := [5, 4, 3, 0, 2, 1]
def added424 : List (List Vertex) := [[1, 0, 4, 6, 7, 2, 5, 3], [3, 7, 1, 5]]
theorem accepted424 : OriginalAccepted (decode 424) 2 1 0
    tail424 added424 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
