/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tail301 : List Vertex := [5, 2, 1, 0, 4, 3]
def added301 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 5, 4], [4, 6, 0, 5]]
theorem accepted301 : OriginalAccepted (decode 301) 1 0 0
    tail301 added301 := by decide

def tail302 : List Vertex := [7, 1, 2, 0, 4, 3]
def added302 : List (List Vertex) := [[3, 0, 1, 6, 4, 5, 7, 2], [2, 5, 0, 7]]
theorem accepted302 : OriginalAccepted (decode 302) 0 2 2
    tail302 added302 := by decide

def tail303 : List Vertex := [7, 2, 1, 0, 4, 3]
def added303 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 7, 1], [1, 6, 0, 7]]
theorem accepted303 : OriginalAccepted (decode 303) 1 2 2
    tail303 added303 := by decide

def tail308 : List Vertex := [6, 2, 1, 0, 4, 3]
def added308 : List (List Vertex) := [[3, 0, 2, 7, 6, 4, 5, 1], [1, 6]]
theorem accepted308 : OriginalAccepted (decode 308) 1 2 1
    tail308 added308 := by decide

def tail309 : List Vertex := [6, 2, 1, 0, 4, 3]
def added309 : List (List Vertex) := [[3, 0, 2, 7, 5, 4, 6, 1], [1, 5, 0, 6]]
theorem accepted309 : OriginalAccepted (decode 309) 0 2 1
    tail309 added309 := by decide

def tail310 : List Vertex := [7, 2, 1, 0, 4, 3]
def added310 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 1], [1, 6, 5, 0, 7]]
theorem accepted310 : OriginalAccepted (decode 310) 0 1 2
    tail310 added310 := by decide

def tail313 : List Vertex := [6, 2, 1, 0, 4, 3]
def added313 : List (List Vertex) := [[3, 0, 2, 7, 1, 5, 6, 4], [4, 5, 0, 6]]
theorem accepted313 : OriginalAccepted (decode 313) 0 1 1
    tail313 added313 := by decide

def tail314 : List Vertex := [7, 2, 1, 0, 4, 3]
def added314 : List (List Vertex) := [[3, 0, 2, 6, 4, 5, 7, 1], [1, 5, 0, 7]]
theorem accepted314 : OriginalAccepted (decode 314) 0 2 2
    tail314 added314 := by decide

def tail315 : List Vertex := [7, 1, 2, 0, 4, 3]
def added315 : List (List Vertex) := [[3, 0, 1, 5, 4, 6, 7, 2], [2, 6, 0, 7]]
theorem accepted315 : OriginalAccepted (decode 315) 1 2 2
    tail315 added315 := by decide

def tail316 : List Vertex := [6, 2, 1, 0, 4, 3]
def added316 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 4, 5], [6, 5]]
theorem accepted316 : OriginalAccepted (decode 316) 1 0 1
    tail316 added316 := by decide

def tail318 : List Vertex := [7, 2, 1, 0, 4, 3]
def added318 : List (List Vertex) := [[3, 0, 5, 4, 6, 7, 1], [1, 6, 2, 0, 7]]
theorem accepted318 : OriginalAccepted (decode 318) 2 1 2
    tail318 added318 := by decide

def tail319 : List Vertex := [6, 2, 1, 0, 4, 3]
def added319 : List (List Vertex) := [[3, 0, 2, 7, 1, 6, 4, 5], [6, 0, 7, 5]]
theorem accepted319 : OriginalAccepted (decode 319) 2 0 1
    tail319 added319 := by decide

def tail324 : List Vertex := [5, 4, 3, 0, 1, 2]
def added324 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 5]]
theorem accepted324 : OriginalAccepted (decode 324) 0 1 0
    tail324 added324 := by decide

def tail326 : List Vertex := [5, 4, 3, 0, 1, 2]
def added326 : List (List Vertex) := [[2, 0, 4, 6, 1, 5, 3], [3, 6, 7, 0, 5]]
theorem accepted326 : OriginalAccepted (decode 326) 2 1 0
    tail326 added326 := by decide

def tail327 : List Vertex := [6, 4, 3, 0, 1, 2]
def added327 : List (List Vertex) := [[2, 0, 4, 5, 1, 6, 3], [3, 5, 7, 0, 6]]
theorem accepted327 : OriginalAccepted (decode 327) 2 0 1
    tail327 added327 := by decide

def tail328 : List Vertex := [5, 4, 3, 0, 1, 2]
def added328 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 1, 7], [5, 7]]
theorem accepted328 : OriginalAccepted (decode 328) 0 2 0
    tail328 added328 := by decide

def tail329 : List Vertex := [5, 4, 3, 0, 1, 2]
def added329 : List (List Vertex) := [[2, 0, 4, 6, 3, 5, 1, 7], [5, 0, 6, 7]]
theorem accepted329 : OriginalAccepted (decode 329) 1 2 0
    tail329 added329 := by decide

def tail331 : List Vertex := [6, 4, 3, 0, 1, 2]
def added331 : List (List Vertex) := [[2, 0, 7, 1, 5, 6, 3], [3, 5, 4, 0, 6]]
theorem accepted331 : OriginalAccepted (decode 331) 1 0 1
    tail331 added331 := by decide

def tail332 : List Vertex := [6, 4, 3, 0, 1, 2]
def added332 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 1, 7], [6, 7]]
theorem accepted332 : OriginalAccepted (decode 332) 1 2 1
    tail332 added332 := by decide

def tail333 : List Vertex := [6, 4, 3, 0, 1, 2]
def added333 : List (List Vertex) := [[2, 0, 4, 5, 3, 6, 1, 7], [6, 0, 5, 7]]
theorem accepted333 : OriginalAccepted (decode 333) 0 2 1
    tail333 added333 := by decide

def tail334 : List Vertex := [5, 4, 3, 0, 1, 2]
def added334 : List (List Vertex) := [[2, 0, 7, 1, 6, 5, 3], [3, 6, 4, 0, 5]]
theorem accepted334 : OriginalAccepted (decode 334) 0 1 0
    tail334 added334 := by decide

def tail336 : List Vertex := [5, 4, 3, 0, 2, 1]
def added336 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 5]]
theorem accepted336 : OriginalAccepted (decode 336) 0 1 0
    tail336 added336 := by decide

def tail338 : List Vertex := [5, 4, 3, 0, 2, 1]
def added338 : List (List Vertex) := [[1, 0, 4, 6, 2, 5, 3], [3, 6, 7, 0, 5]]
theorem accepted338 : OriginalAccepted (decode 338) 2 1 0
    tail338 added338 := by decide

def tail339 : List Vertex := [6, 4, 3, 0, 2, 1]
def added339 : List (List Vertex) := [[1, 0, 4, 5, 2, 6, 3], [3, 5, 7, 0, 6]]
theorem accepted339 : OriginalAccepted (decode 339) 2 0 1
    tail339 added339 := by decide

def tail344 : List Vertex := [5, 1, 2, 0, 4, 3]
def added344 : List (List Vertex) := [[3, 0, 1, 7, 6, 4, 5, 2], [2, 6, 3, 5]]
theorem accepted344 : OriginalAccepted (decode 344) 1 2 0
    tail344 added344 := by decide

def tail348 : List Vertex := [6, 1, 2, 0, 4, 3]
def added348 : List (List Vertex) := [[3, 0, 1, 7, 5, 4, 6, 2], [2, 5, 3, 6]]
theorem accepted348 : OriginalAccepted (decode 348) 0 2 1
    tail348 added348 := by decide

def tail352 : List Vertex := [5, 4, 3, 0, 2, 1]
def added352 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 2, 7], [5, 7]]
theorem accepted352 : OriginalAccepted (decode 352) 0 2 0
    tail352 added352 := by decide

def tail353 : List Vertex := [5, 4, 3, 0, 2, 1]
def added353 : List (List Vertex) := [[1, 0, 4, 6, 3, 5, 2, 7], [5, 0, 6, 7]]
theorem accepted353 : OriginalAccepted (decode 353) 1 2 0
    tail353 added353 := by decide

def tail355 : List Vertex := [6, 4, 3, 0, 2, 1]
def added355 : List (List Vertex) := [[1, 0, 7, 2, 5, 6, 3], [3, 5, 4, 0, 6]]
theorem accepted355 : OriginalAccepted (decode 355) 1 0 1
    tail355 added355 := by decide

def tail356 : List Vertex := [5, 2, 1, 0, 4, 3]
def added356 : List (List Vertex) := [[3, 0, 2, 7, 6, 4, 5, 1], [1, 6, 3, 5]]
theorem accepted356 : OriginalAccepted (decode 356) 1 2 0
    tail356 added356 := by decide

def tail363 : List Vertex := [6, 4, 3, 0, 2, 1]
def added363 : List (List Vertex) := [[1, 7, 2, 5, 3, 6, 0, 4], [4, 5, 1, 0, 7, 6]]
theorem accepted363 : OriginalAccepted (decode 363) 2 1 1
    tail363 added363 := by decide

def tail364 : List Vertex := [5, 2, 1, 0, 4, 3]
def added364 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 2, 0], [5, 6, 3, 0]]
theorem accepted364 : OriginalAccepted (decode 364) 1 0 0
    tail364 added364 := by decide

end Gallai.Certificate.ThreeAnchor.OriginalOrbits
