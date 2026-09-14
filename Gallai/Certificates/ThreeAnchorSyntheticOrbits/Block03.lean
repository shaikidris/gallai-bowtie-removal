/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSynthetic
import Gallai.Certificates.ThreeAnchorSyntheticOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def connector301 : List Vertex := [6, 4, 3, 0, 1, 2, 5]
def added301 : List (List Vertex) := [[4, 5, 0, 2, 7, 1, 6], [4, 0, 6]]
theorem accepted301 : SyntheticAccepted (decode 301) 1 0
    connector301 added301 := by decide

def connector302 : List Vertex := [5, 4, 3, 0, 2, 1, 7]
def added302 : List (List Vertex) := [[4, 6, 1, 0, 5, 2, 7], [4, 0, 7]]
theorem accepted302 : SyntheticAccepted (decode 302) 0 2
    connector302 added302 := by decide

def connector303 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added303 : List (List Vertex) := [[4, 5, 2, 0, 6, 1, 7], [4, 0, 7]]
theorem accepted303 : SyntheticAccepted (decode 303) 1 2
    connector303 added303 := by decide

def connector308 : List Vertex := [6, 4, 3, 0, 1, 2, 7]
def added308 : List (List Vertex) := [[4, 5, 1, 6, 2, 0], [4, 0]]
theorem accepted308 : SyntheticAccepted (decode 308) 1 2
    connector308 added308 := by decide

def connector309 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added309 : List (List Vertex) := [[4, 6, 1, 5, 0, 2], [4, 0, 6, 2]]
theorem accepted309 : SyntheticAccepted (decode 309) 0 2
    connector309 added309 := by decide

def connector310 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added310 : List (List Vertex) := [[4, 6, 1, 5, 0, 2, 7], [4, 0, 7]]
theorem accepted310 : SyntheticAccepted (decode 310) 0 1
    connector310 added310 := by decide

def connector313 : List Vertex := [5, 4, 3, 0, 1, 2, 6]
def added313 : List (List Vertex) := [[4, 6, 0, 2, 7, 1, 5], [4, 0, 5]]
theorem accepted313 : SyntheticAccepted (decode 313) 0 1
    connector313 added313 := by decide

def connector314 : List Vertex := [5, 4, 3, 0, 1, 2, 7]
def added314 : List (List Vertex) := [[4, 6, 2, 0, 5, 1, 7], [4, 0, 7]]
theorem accepted314 : SyntheticAccepted (decode 314) 0 2
    connector314 added314 := by decide

def connector315 : List Vertex := [6, 4, 3, 0, 2, 1, 7]
def added315 : List (List Vertex) := [[4, 5, 1, 0, 6, 2, 7], [4, 0, 7]]
theorem accepted315 : SyntheticAccepted (decode 315) 1 2
    connector315 added315 := by decide

def connector316 : List Vertex := [6, 1, 2, 0, 3, 4, 5]
def added316 : List (List Vertex) := [[4, 6, 2, 7, 1, 0], [4, 0]]
theorem accepted316 : SyntheticAccepted (decode 316) 1 0
    connector316 added316 := by decide

def connector318 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added318 : List (List Vertex) := [[4, 5, 0, 1, 6, 2, 7], [4, 0, 7]]
theorem accepted318 : SyntheticAccepted (decode 318) 2 1
    connector318 added318 := by decide

def connector319 : List Vertex := [7, 1, 2, 0, 3, 4, 5]
def added319 : List (List Vertex) := [[4, 6, 1, 0, 7, 2], [4, 0, 6, 2]]
theorem accepted319 : SyntheticAccepted (decode 319) 2 0
    connector319 added319 := by decide

def connector324 : List Vertex := [5, 1, 2, 0, 3, 4, 6]
def added324 : List (List Vertex) := [[1, 6, 3, 5, 4, 0], [1, 0]]
theorem accepted324 : SyntheticAccepted (decode 324) 0 1
    connector324 added324 := by decide

def connector326 : List Vertex := [7, 0, 2, 1, 6]
def added326 : List (List Vertex) := [[1, 5, 3, 0, 4, 6], [1, 0, 5, 4, 3, 6]]
theorem accepted326 : SyntheticAccepted (decode 326) 2 1
    connector326 added326 := by decide

def connector327 : List Vertex := [7, 0, 2, 1, 5]
def added327 : List (List Vertex) := [[1, 6, 3, 0, 4, 5], [1, 0, 6, 4, 3, 5]]
theorem accepted327 : SyntheticAccepted (decode 327) 2 0
    connector327 added327 := by decide

def connector328 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added328 : List (List Vertex) := [[1, 5, 4, 6, 3, 0], [1, 0]]
theorem accepted328 : SyntheticAccepted (decode 328) 0 2
    connector328 added328 := by decide

def connector329 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added329 : List (List Vertex) := [[1, 5, 3, 0, 6, 4], [1, 0, 5, 4]]
theorem accepted329 : SyntheticAccepted (decode 329) 1 2
    connector329 added329 := by decide

def connector331 : List Vertex := [6, 3, 4, 0, 2, 1, 5]
def added331 : List (List Vertex) := [[1, 7, 0, 3, 5, 4, 6], [1, 0, 6]]
theorem accepted331 : SyntheticAccepted (decode 331) 1 0
    connector331 added331 := by decide

def connector332 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added332 : List (List Vertex) := [[1, 6, 4, 5, 3, 0], [1, 0]]
theorem accepted332 : SyntheticAccepted (decode 332) 1 2
    connector332 added332 := by decide

def connector333 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added333 : List (List Vertex) := [[1, 6, 3, 0, 5, 4], [1, 0, 6, 4]]
theorem accepted333 : SyntheticAccepted (decode 333) 0 2
    connector333 added333 := by decide

def connector334 : List Vertex := [5, 3, 4, 0, 2, 1, 6]
def added334 : List (List Vertex) := [[1, 7, 0, 3, 6, 4, 5], [1, 0, 5]]
theorem accepted334 : SyntheticAccepted (decode 334) 0 1
    connector334 added334 := by decide

def connector336 : List Vertex := [5, 2, 1, 0, 3, 4, 6]
def added336 : List (List Vertex) := [[2, 6, 3, 5, 4, 0], [2, 0]]
theorem accepted336 : SyntheticAccepted (decode 336) 0 1
    connector336 added336 := by decide

def connector338 : List Vertex := [7, 0, 1, 2, 6]
def added338 : List (List Vertex) := [[2, 5, 3, 0, 4, 6], [2, 0, 5, 4, 3, 6]]
theorem accepted338 : SyntheticAccepted (decode 338) 2 1
    connector338 added338 := by decide

def connector339 : List Vertex := [7, 0, 1, 2, 5]
def added339 : List (List Vertex) := [[2, 6, 3, 0, 4, 5], [2, 0, 6, 4, 3, 5]]
theorem accepted339 : SyntheticAccepted (decode 339) 2 0
    connector339 added339 := by decide

def connector344 : List Vertex := [6, 3, 4, 0, 2, 1, 7]
def added344 : List (List Vertex) := [[3, 0, 1, 5, 4, 6, 2], [3, 5, 2]]
theorem accepted344 : SyntheticAccepted (decode 344) 1 2
    connector344 added344 := by decide

def connector348 : List Vertex := [5, 3, 4, 0, 2, 1, 7]
def added348 : List (List Vertex) := [[3, 0, 1, 6, 4, 5, 2], [3, 6, 2]]
theorem accepted348 : SyntheticAccepted (decode 348) 0 2
    connector348 added348 := by decide

def connector352 : List Vertex := [5, 3, 4, 0, 1, 2, 7]
def added352 : List (List Vertex) := [[2, 5, 4, 6, 3, 0], [2, 0]]
theorem accepted352 : SyntheticAccepted (decode 352) 0 2
    connector352 added352 := by decide

def connector353 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added353 : List (List Vertex) := [[2, 5, 3, 0, 6, 4], [2, 0, 5, 4]]
theorem accepted353 : SyntheticAccepted (decode 353) 1 2
    connector353 added353 := by decide

def connector355 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added355 : List (List Vertex) := [[2, 7, 0, 3, 5, 4, 6], [2, 0, 6]]
theorem accepted355 : SyntheticAccepted (decode 355) 1 0
    connector355 added355 := by decide

def connector356 : List Vertex := [6, 3, 4, 0, 1, 2, 7]
def added356 : List (List Vertex) := [[3, 0, 2, 5, 4, 6, 1], [3, 5, 1]]
theorem accepted356 : SyntheticAccepted (decode 356) 1 2
    connector356 added356 := by decide

def connector363 : List Vertex := [7, 1, 2, 0, 3, 4, 6]
def added363 : List (List Vertex) := [[1, 5, 2, 7, 0, 6, 3], [1, 0, 4, 5, 3]]
theorem accepted363 : SyntheticAccepted (decode 363) 2 1
    connector363 added363 := by decide

def connector364 : List Vertex := [6, 3, 4, 0, 1, 2, 5]
def added364 : List (List Vertex) := [[3, 5, 4, 6, 1, 7, 2, 0], [3, 0]]
theorem accepted364 : SyntheticAccepted (decode 364) 1 0
    connector364 added364 := by decide

end Gallai.Certificate.ThreeAnchor.Orbits
