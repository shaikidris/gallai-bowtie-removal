/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector366 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added366 : List (List Vertex) := [[2, 5, 3, 6, 1, 7, 0, 4], [2, 0, 5, 4]]
theorem accepted366 : SyntheticAccepted (decode 366) 2 1
    connector366 added366 := by decide

def connector367 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added367 : List (List Vertex) := [[1, 6, 3, 5, 2, 7, 0, 4], [1, 0, 6, 4]]
theorem accepted367 : SyntheticAccepted (decode 367) 2 0
    connector367 added367 := by decide

def connector368 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added368 : List (List Vertex) := [[2, 6, 4, 5, 3, 0], [2, 0]]
theorem accepted368 : SyntheticAccepted (decode 368) 1 2
    connector368 added368 := by decide

def connector369 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added369 : List (List Vertex) := [[2, 6, 3, 0, 5, 4], [2, 0, 6, 4]]
theorem accepted369 : SyntheticAccepted (decode 369) 0 2
    connector369 added369 := by decide

def connector370 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added370 : List (List Vertex) := [[2, 7, 0, 3, 6, 4, 5], [2, 0, 5]]
theorem accepted370 : SyntheticAccepted (decode 370) 0 1
    connector370 added370 := by decide

def connector372 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added372 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [3, 6, 1]]
theorem accepted372 : SyntheticAccepted (decode 372) 0 2
    connector372 added372 := by decide

def connector376 : List Vertex := [5, 3, 4, 0, 1, 2, 6]
def added376 : List (List Vertex) := [[3, 6, 4, 5, 1, 7, 2, 0], [3, 0]]
theorem accepted376 : SyntheticAccepted (decode 376) 0 1
    connector376 added376 := by decide

def connector378 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added378 : List (List Vertex) := [[1, 5, 3, 6, 2, 7, 0, 4], [1, 0, 5, 4]]
theorem accepted378 : SyntheticAccepted (decode 378) 2 1
    connector378 added378 := by decide

def connector379 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added379 : List (List Vertex) := [[2, 6, 3, 5, 1, 7, 0, 4], [2, 0, 6, 4]]
theorem accepted379 : SyntheticAccepted (decode 379) 2 0
    connector379 added379 := by decide

def connector382 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added382 : List (List Vertex) := [[1, 6, 2, 7, 0, 5, 3], [1, 0, 4, 6, 3]]
theorem accepted382 : SyntheticAccepted (decode 382) 2 0
    connector382 added382 := by decide

def connector388 : List Vertex := [5, 1, 2, 0, 4, 3, 7]
def added388 : List (List Vertex) := [[1, 6, 4, 5, 3, 0], [1, 0]]
theorem accepted388 : SyntheticAccepted (decode 388) 0 2
    connector388 added388 := by decide

def connector389 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added389 : List (List Vertex) := [[1, 5, 4, 6, 0, 3], [1, 0, 5, 3]]
theorem accepted389 : SyntheticAccepted (decode 389) 1 2
    connector389 added389 := by decide

def connector391 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added391 : List (List Vertex) := [[1, 5, 4, 6, 0, 3, 7], [1, 0, 7]]
theorem accepted391 : SyntheticAccepted (decode 391) 1 0
    connector391 added391 := by decide

def connector392 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added392 : List (List Vertex) := [[1, 7, 3, 5, 4, 0], [1, 0]]
theorem accepted392 : SyntheticAccepted (decode 392) 0 1
    connector392 added392 := by decide

def connector394 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added394 : List (List Vertex) := [[1, 5, 3, 7, 0, 4], [1, 0, 5, 4]]
theorem accepted394 : SyntheticAccepted (decode 394) 2 1
    connector394 added394 := by decide

def connector395 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added395 : List (List Vertex) := [[1, 5, 3, 7, 0, 4, 6], [1, 0, 6]]
theorem accepted395 : SyntheticAccepted (decode 395) 2 0
    connector395 added395 := by decide

def connector397 : List Vertex := [6, 1, 2, 0, 4, 3, 5]
def added397 : List (List Vertex) := [[1, 7, 3, 0, 6, 4, 5], [1, 0, 5]]
theorem accepted397 : SyntheticAccepted (decode 397) 1 0
    connector397 added397 := by decide

def connector398 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added398 : List (List Vertex) := [[1, 6, 4, 0, 7, 3, 5], [1, 0, 5]]
theorem accepted398 : SyntheticAccepted (decode 398) 2 0
    connector398 added398 := by decide

def connector399 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added399 : List (List Vertex) := [[1, 6, 0, 4, 5, 3, 7], [1, 0, 7]]
theorem accepted399 : SyntheticAccepted (decode 399) 2 1
    connector399 added399 := by decide

def connector400 : List Vertex := [5, 2, 1, 0, 4, 3, 7]
def added400 : List (List Vertex) := [[2, 6, 4, 5, 3, 0], [2, 0]]
theorem accepted400 : SyntheticAccepted (decode 400) 0 2
    connector400 added400 := by decide

def connector401 : List Vertex := [6, 2, 1, 0, 4, 3, 7]
def added401 : List (List Vertex) := [[2, 5, 4, 6, 0, 3], [2, 0, 5, 3]]
theorem accepted401 : SyntheticAccepted (decode 401) 1 2
    connector401 added401 := by decide

def connector403 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added403 : List (List Vertex) := [[2, 5, 4, 6, 0, 3, 7], [2, 0, 7]]
theorem accepted403 : SyntheticAccepted (decode 403) 1 0
    connector403 added403 := by decide

def connector404 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added404 : List (List Vertex) := [[1, 0, 3, 5, 2, 6, 4], [1, 5, 4]]
theorem accepted404 : SyntheticAccepted (decode 404) 1 2
    connector404 added404 := by decide

def connector411 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added411 : List (List Vertex) := [[1, 5, 2, 6, 0, 7, 3], [1, 0, 4, 5, 3]]
theorem accepted411 : SyntheticAccepted (decode 411) 2 1
    connector411 added411 := by decide

def connector412 : List Vertex := [6, 2, 1, 0, 4, 3, 5]
def added412 : List (List Vertex) := [[2, 5, 4, 6, 1, 7, 3, 0], [2, 0]]
theorem accepted412 : SyntheticAccepted (decode 412) 1 0
    connector412 added412 := by decide

def connector414 : List Vertex := [7, 3, 4, 0, 2, 1, 6]
def added414 : List (List Vertex) := [[4, 6, 2, 5, 3, 0, 1, 7], [4, 5, 0, 7]]
theorem accepted414 : SyntheticAccepted (decode 414) 2 1
    connector414 added414 := by decide

def connector415 : List Vertex := [7, 1, 2, 0, 4, 3, 5]
def added415 : List (List Vertex) := [[2, 5, 4, 6, 1, 0, 3, 7], [2, 6, 0, 7]]
theorem accepted415 : SyntheticAccepted (decode 415) 2 0
    connector415 added415 := by decide

def connector416 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added416 : List (List Vertex) := [[2, 7, 3, 5, 4, 0], [2, 0]]
theorem accepted416 : SyntheticAccepted (decode 416) 0 1
    connector416 added416 := by decide

def connector418 : List Vertex := [7, 2, 1, 0, 3, 4, 6]
def added418 : List (List Vertex) := [[2, 5, 3, 7, 0, 4], [2, 0, 5, 4]]
theorem accepted418 : SyntheticAccepted (decode 418) 2 1
    connector418 added418 := by decide

def connector419 : List Vertex := [7, 2, 1, 0, 3, 4, 5]
def added419 : List (List Vertex) := [[2, 5, 3, 7, 0, 4, 6], [2, 0, 6]]
theorem accepted419 : SyntheticAccepted (decode 419) 2 0
    connector419 added419 := by decide

def connector423 : List Vertex := [6, 1, 2, 0, 4, 3, 7]
def added423 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 4], [1, 0, 3, 5, 4]]
theorem accepted423 : SyntheticAccepted (decode 423) 1 2
    connector423 added423 := by decide

def connector424 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added424 : List (List Vertex) := [[1, 0, 4, 5, 2, 7, 3], [1, 5, 3]]
theorem accepted424 : SyntheticAccepted (decode 424) 2 1
    connector424 added424 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
