/-
Copyright (c) 2026 Idris Ali Shaik.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Idris Ali Shaik (with Codex assistance)
-/
import Gallai.Certificates.CompletedStarCatalogue.Orbit000
import Gallai.Certificates.CompletedStarCatalogue.Orbit001
import Gallai.Certificates.CompletedStarCatalogue.Orbit002
import Gallai.Certificates.CompletedStarCatalogue.Orbit003
import Gallai.Certificates.CompletedStarCatalogue.Orbit004
import Gallai.Certificates.CompletedStarCatalogue.Orbit005
import Gallai.Certificates.CompletedStarCatalogue.Orbit006
import Gallai.Certificates.CompletedStarCatalogue.Orbit007
import Gallai.Certificates.CompletedStarCatalogue.Orbit008
import Gallai.Certificates.CompletedStarCatalogue.Orbit009
import Gallai.Certificates.CompletedStarCatalogue.Orbit010
import Gallai.Certificates.CompletedStarCatalogue.Orbit011
import Gallai.Certificates.CompletedStarCatalogue.Orbit012
import Gallai.Certificates.CompletedStarCatalogue.Orbit013
import Gallai.Certificates.CompletedStarCatalogue.Orbit014
import Gallai.Certificates.CompletedStarCatalogue.Orbit015
import Gallai.Certificates.CompletedStarCatalogue.Orbit016
import Gallai.Certificates.CompletedStarCatalogue.Orbit017
import Gallai.Certificates.CompletedStarCatalogue.Orbit018
import Gallai.Certificates.CompletedStarCatalogue.Orbit019
import Gallai.Certificates.CompletedStarCatalogue.Orbit020
import Gallai.Certificates.CompletedStarCatalogue.Orbit021
import Gallai.Certificates.CompletedStarCatalogue.Orbit022
import Gallai.Certificates.CompletedStarCatalogue.Orbit023
import Gallai.Certificates.CompletedStarCatalogue.Orbit024
import Gallai.Certificates.CompletedStarCatalogue.Orbit025
import Gallai.Certificates.CompletedStarCatalogue.Orbit026
import Gallai.Certificates.CompletedStarCatalogue.Orbit027
import Gallai.Certificates.CompletedStarCatalogue.Orbit028
import Gallai.Certificates.CompletedStarCatalogue.Orbit029
import Gallai.Certificates.CompletedStarCatalogue.Orbit030
import Gallai.Certificates.CompletedStarCatalogue.Orbit031
import Gallai.Certificates.CompletedStarCatalogue.Orbit032
import Gallai.Certificates.CompletedStarCatalogue.Orbit033
import Gallai.Certificates.CompletedStarCatalogue.Orbit034
import Gallai.Certificates.CompletedStarCatalogue.Orbit035
import Gallai.Certificates.CompletedStarCatalogue.Orbit036
import Gallai.Certificates.CompletedStarCatalogue.Orbit037
import Gallai.Certificates.CompletedStarCatalogue.Orbit038
import Gallai.Certificates.CompletedStarCatalogue.Orbit039
import Gallai.Certificates.CompletedStarCatalogue.Orbit040
import Gallai.Certificates.CompletedStarCatalogue.Orbit041
import Gallai.Certificates.CompletedStarCatalogue.Orbit042
import Gallai.Certificates.CompletedStarCatalogue.Orbit043
import Gallai.Certificates.CompletedStarCatalogue.Orbit044
import Gallai.Certificates.CompletedStarCatalogue.Orbit045
import Gallai.Certificates.CompletedStarCatalogue.Orbit046
import Gallai.Certificates.CompletedStarCatalogue.Orbit047
import Gallai.Certificates.CompletedStarCatalogue.Orbit048
import Gallai.Certificates.CompletedStarCatalogue.Orbit049
import Gallai.Certificates.CompletedStarCatalogue.Orbit050
import Gallai.Certificates.CompletedStarCatalogue.Orbit051
import Gallai.Certificates.CompletedStarCatalogue.Orbit052
import Gallai.Certificates.CompletedStarCatalogue.Orbit053
import Gallai.Certificates.CompletedStarCatalogue.Orbit054
import Gallai.Certificates.CompletedStarCatalogue.Orbit055
import Gallai.Certificates.CompletedStarCatalogue.Orbit056
import Gallai.Certificates.CompletedStarCatalogue.Orbit057
import Gallai.Certificates.CompletedStarCatalogue.Orbit058
import Gallai.Certificates.CompletedStarCatalogue.Orbit059
import Gallai.Certificates.CompletedStarCatalogue.Orbit060
import Gallai.Certificates.CompletedStarCatalogue.Orbit061
import Gallai.Certificates.CompletedStarCatalogue.Orbit062
import Gallai.Certificates.CompletedStarCatalogue.Orbit063
import Gallai.Certificates.CompletedStarCatalogue.Orbit064
import Gallai.Certificates.CompletedStarCatalogue.Orbit065
import Gallai.Certificates.CompletedStarCatalogue.Orbit066
import Gallai.Certificates.CompletedStarUniverse

/-! # Accepted completed-star representative records

Generated from certificate SHA256
4dbb85f7bef9f06a6b4701c7bd611c60507ecedfcf83c46b2c6b1a44828f513d.
Every one of the 67 stored states has an accepted record at every interface.
Coverage of arbitrary labelled states up to symmetry is a separate obligation.
-/

namespace Gallai.Certificate.CompletedStar.Catalogue

/-- The stored representatives, in lexicographic row order. -/
def state : Fin 67 → State :=
  ![Orbit000.state,
    Orbit001.state,
    Orbit002.state,
    Orbit003.state,
    Orbit004.state,
    Orbit005.state,
    Orbit006.state,
    Orbit007.state,
    Orbit008.state,
    Orbit009.state,
    Orbit010.state,
    Orbit011.state,
    Orbit012.state,
    Orbit013.state,
    Orbit014.state,
    Orbit015.state,
    Orbit016.state,
    Orbit017.state,
    Orbit018.state,
    Orbit019.state,
    Orbit020.state,
    Orbit021.state,
    Orbit022.state,
    Orbit023.state,
    Orbit024.state,
    Orbit025.state,
    Orbit026.state,
    Orbit027.state,
    Orbit028.state,
    Orbit029.state,
    Orbit030.state,
    Orbit031.state,
    Orbit032.state,
    Orbit033.state,
    Orbit034.state,
    Orbit035.state,
    Orbit036.state,
    Orbit037.state,
    Orbit038.state,
    Orbit039.state,
    Orbit040.state,
    Orbit041.state,
    Orbit042.state,
    Orbit043.state,
    Orbit044.state,
    Orbit045.state,
    Orbit046.state,
    Orbit047.state,
    Orbit048.state,
    Orbit049.state,
    Orbit050.state,
    Orbit051.state,
    Orbit052.state,
    Orbit053.state,
    Orbit054.state,
    Orbit055.state,
    Orbit056.state,
    Orbit057.state,
    Orbit058.state,
    Orbit059.state,
    Orbit060.state,
    Orbit061.state,
    Orbit062.state,
    Orbit063.state,
    Orbit064.state,
    Orbit065.state,
    Orbit066.state]

/-- Replacement words selected by representative and interface. -/
def replacements : Fin 67 → Fin 10 → List (List Star.Vertex) :=
  ![Orbit000.replacements,
    Orbit001.replacements,
    Orbit002.replacements,
    Orbit003.replacements,
    Orbit004.replacements,
    Orbit005.replacements,
    Orbit006.replacements,
    Orbit007.replacements,
    Orbit008.replacements,
    Orbit009.replacements,
    Orbit010.replacements,
    Orbit011.replacements,
    Orbit012.replacements,
    Orbit013.replacements,
    Orbit014.replacements,
    Orbit015.replacements,
    Orbit016.replacements,
    Orbit017.replacements,
    Orbit018.replacements,
    Orbit019.replacements,
    Orbit020.replacements,
    Orbit021.replacements,
    Orbit022.replacements,
    Orbit023.replacements,
    Orbit024.replacements,
    Orbit025.replacements,
    Orbit026.replacements,
    Orbit027.replacements,
    Orbit028.replacements,
    Orbit029.replacements,
    Orbit030.replacements,
    Orbit031.replacements,
    Orbit032.replacements,
    Orbit033.replacements,
    Orbit034.replacements,
    Orbit035.replacements,
    Orbit036.replacements,
    Orbit037.replacements,
    Orbit038.replacements,
    Orbit039.replacements,
    Orbit040.replacements,
    Orbit041.replacements,
    Orbit042.replacements,
    Orbit043.replacements,
    Orbit044.replacements,
    Orbit045.replacements,
    Orbit046.replacements,
    Orbit047.replacements,
    Orbit048.replacements,
    Orbit049.replacements,
    Orbit050.replacements,
    Orbit051.replacements,
    Orbit052.replacements,
    Orbit053.replacements,
    Orbit054.replacements,
    Orbit055.replacements,
    Orbit056.replacements,
    Orbit057.replacements,
    Orbit058.replacements,
    Orbit059.replacements,
    Orbit060.replacements,
    Orbit061.replacements,
    Orbit062.replacements,
    Orbit063.replacements,
    Orbit064.replacements,
    Orbit065.replacements,
    Orbit066.replacements]

/-- Additional words selected by representative and interface. -/
def added : Fin 67 → Fin 10 → List (List Star.Vertex) :=
  ![Orbit000.added,
    Orbit001.added,
    Orbit002.added,
    Orbit003.added,
    Orbit004.added,
    Orbit005.added,
    Orbit006.added,
    Orbit007.added,
    Orbit008.added,
    Orbit009.added,
    Orbit010.added,
    Orbit011.added,
    Orbit012.added,
    Orbit013.added,
    Orbit014.added,
    Orbit015.added,
    Orbit016.added,
    Orbit017.added,
    Orbit018.added,
    Orbit019.added,
    Orbit020.added,
    Orbit021.added,
    Orbit022.added,
    Orbit023.added,
    Orbit024.added,
    Orbit025.added,
    Orbit026.added,
    Orbit027.added,
    Orbit028.added,
    Orbit029.added,
    Orbit030.added,
    Orbit031.added,
    Orbit032.added,
    Orbit033.added,
    Orbit034.added,
    Orbit035.added,
    Orbit036.added,
    Orbit037.added,
    Orbit038.added,
    Orbit039.added,
    Orbit040.added,
    Orbit041.added,
    Orbit042.added,
    Orbit043.added,
    Orbit044.added,
    Orbit045.added,
    Orbit046.added,
    Orbit047.added,
    Orbit048.added,
    Orbit049.added,
    Orbit050.added,
    Orbit051.added,
    Orbit052.added,
    Orbit053.added,
    Orbit054.added,
    Orbit055.added,
    Orbit056.added,
    Orbit057.added,
    Orbit058.added,
    Orbit059.added,
    Orbit060.added,
    Orbit061.added,
    Orbit062.added,
    Orbit063.added,
    Orbit064.added,
    Orbit065.added,
    Orbit066.added]

/-- All 670 records satisfy the actual reconstruction contract. -/
theorem accepted (o : Fin 67) (i : Fin 10) :
    AcceptedRecord (state o) i (replacements o i) (added o i) := by
  fin_cases o
  · exact Orbit000.accepted i
  · exact Orbit001.accepted i
  · exact Orbit002.accepted i
  · exact Orbit003.accepted i
  · exact Orbit004.accepted i
  · exact Orbit005.accepted i
  · exact Orbit006.accepted i
  · exact Orbit007.accepted i
  · exact Orbit008.accepted i
  · exact Orbit009.accepted i
  · exact Orbit010.accepted i
  · exact Orbit011.accepted i
  · exact Orbit012.accepted i
  · exact Orbit013.accepted i
  · exact Orbit014.accepted i
  · exact Orbit015.accepted i
  · exact Orbit016.accepted i
  · exact Orbit017.accepted i
  · exact Orbit018.accepted i
  · exact Orbit019.accepted i
  · exact Orbit020.accepted i
  · exact Orbit021.accepted i
  · exact Orbit022.accepted i
  · exact Orbit023.accepted i
  · exact Orbit024.accepted i
  · exact Orbit025.accepted i
  · exact Orbit026.accepted i
  · exact Orbit027.accepted i
  · exact Orbit028.accepted i
  · exact Orbit029.accepted i
  · exact Orbit030.accepted i
  · exact Orbit031.accepted i
  · exact Orbit032.accepted i
  · exact Orbit033.accepted i
  · exact Orbit034.accepted i
  · exact Orbit035.accepted i
  · exact Orbit036.accepted i
  · exact Orbit037.accepted i
  · exact Orbit038.accepted i
  · exact Orbit039.accepted i
  · exact Orbit040.accepted i
  · exact Orbit041.accepted i
  · exact Orbit042.accepted i
  · exact Orbit043.accepted i
  · exact Orbit044.accepted i
  · exact Orbit045.accepted i
  · exact Orbit046.accepted i
  · exact Orbit047.accepted i
  · exact Orbit048.accepted i
  · exact Orbit049.accepted i
  · exact Orbit050.accepted i
  · exact Orbit051.accepted i
  · exact Orbit052.accepted i
  · exact Orbit053.accepted i
  · exact Orbit054.accepted i
  · exact Orbit055.accepted i
  · exact Orbit056.accepted i
  · exact Orbit057.accepted i
  · exact Orbit058.accepted i
  · exact Orbit059.accepted i
  · exact Orbit060.accepted i
  · exact Orbit061.accepted i
  · exact Orbit062.accepted i
  · exact Orbit063.accepted i
  · exact Orbit064.accepted i
  · exact Orbit065.accepted i
  · exact Orbit066.accepted i

set_option maxRecDepth 100000 in
set_option maxHeartbeats 0 in
/-- Every representative belongs to the independently defined full-syndrome domain. -/
theorem state_full (o : Fin 67) : FullState (state o) := by
  revert o
  decide

end Gallai.Certificate.CompletedStar.Catalogue
