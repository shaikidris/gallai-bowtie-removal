/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorOriginalOrbits

namespace Gallai.Certificate.ThreeAnchor.OriginalOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def codes0 : List (Fin 1024) := [84, 86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109]
theorem witness0 (n : Fin 1024) (hn : n ∈ codes0) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes0, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 0, tail84, added84, accepted84⟩
  · exact ⟨2, 1, 0, tail86, added86, accepted86⟩
  · exact ⟨2, 0, 1, tail87, added87, accepted87⟩
  · exact ⟨0, 2, 0, tail88, added88, accepted88⟩
  · exact ⟨1, 2, 0, tail89, added89, accepted89⟩
  · exact ⟨1, 0, 2, tail91, added91, accepted91⟩
  · exact ⟨1, 2, 1, tail92, added92, accepted92⟩
  · exact ⟨0, 2, 1, tail93, added93, accepted93⟩
  · exact ⟨0, 1, 2, tail94, added94, accepted94⟩
  · exact ⟨0, 2, 0, tail100, added100, accepted100⟩
  · exact ⟨1, 2, 0, tail101, added101, accepted101⟩
  · exact ⟨1, 0, 2, tail103, added103, accepted103⟩
  · exact ⟨0, 1, 0, tail104, added104, accepted104⟩
  · exact ⟨2, 1, 0, tail106, added106, accepted106⟩
  · exact ⟨2, 0, 2, tail107, added107, accepted107⟩
  · exact ⟨1, 0, 0, tail109, added109, accepted109⟩
def codes1 : List (Fin 1024) := [110, 111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154]
theorem witness1 (n : Fin 1024) (hn : n ∈ codes1) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes1, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, 2, tail110, added110, accepted110⟩
  · exact ⟨1, 2, 2, tail111, added111, accepted111⟩
  · exact ⟨1, 2, 1, tail116, added116, accepted116⟩
  · exact ⟨0, 2, 1, tail117, added117, accepted117⟩
  · exact ⟨0, 1, 2, tail118, added118, accepted118⟩
  · exact ⟨0, 1, 1, tail121, added121, accepted121⟩
  · exact ⟨0, 2, 2, tail122, added122, accepted122⟩
  · exact ⟨1, 2, 2, tail123, added123, accepted123⟩
  · exact ⟨1, 0, 1, tail124, added124, accepted124⟩
  · exact ⟨2, 1, 2, tail126, added126, accepted126⟩
  · exact ⟨2, 0, 1, tail127, added127, accepted127⟩
  · exact ⟨0, 2, 0, tail148, added148, accepted148⟩
  · exact ⟨1, 2, 0, tail149, added149, accepted149⟩
  · exact ⟨1, 0, 1, tail151, added151, accepted151⟩
  · exact ⟨0, 1, 0, tail152, added152, accepted152⟩
  · exact ⟨2, 1, 0, tail154, added154, accepted154⟩
def codes2 : List (Fin 1024) := [155, 157, 158, 159, 164, 166, 167, 168, 169, 171, 172, 173, 174, 181, 182, 183]
theorem witness2 (n : Fin 1024) (hn : n ∈ codes2) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes2, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, 1, tail155, added155, accepted155⟩
  · exact ⟨0, 1, 1, tail157, added157, accepted157⟩
  · exact ⟨2, 0, 0, tail158, added158, accepted158⟩
  · exact ⟨2, 1, 1, tail159, added159, accepted159⟩
  · exact ⟨0, 1, 0, tail164, added164, accepted164⟩
  · exact ⟨2, 1, 0, tail166, added166, accepted166⟩
  · exact ⟨2, 0, 1, tail167, added167, accepted167⟩
  · exact ⟨0, 2, 0, tail168, added168, accepted168⟩
  · exact ⟨1, 2, 0, tail169, added169, accepted169⟩
  · exact ⟨1, 0, 2, tail171, added171, accepted171⟩
  · exact ⟨2, 1, 2, tail172, added172, accepted172⟩
  · exact ⟨0, 2, 1, tail173, added173, accepted173⟩
  · exact ⟨0, 1, 2, tail174, added174, accepted174⟩
  · exact ⟨0, 1, 1, tail181, added181, accepted181⟩
  · exact ⟨0, 2, 2, tail182, added182, accepted182⟩
  · exact ⟨2, 1, 1, tail183, added183, accepted183⟩
def codes3 : List (Fin 1024) := [184, 185, 186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229]
theorem witness3 (n : Fin 1024) (hn : n ∈ codes3) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, 2, tail184, added184, accepted184⟩
  · exact ⟨0, 2, 1, tail185, added185, accepted185⟩
  · exact ⟨0, 1, 2, tail186, added186, accepted186⟩
  · exact ⟨2, 0, 2, tail188, added188, accepted188⟩
  · exact ⟨1, 2, 1, tail189, added189, accepted189⟩
  · exact ⟨1, 0, 2, tail191, added191, accepted191⟩
  · exact ⟨1, 2, 1, tail212, added212, accepted212⟩
  · exact ⟨0, 2, 1, tail213, added213, accepted213⟩
  · exact ⟨0, 1, 0, tail214, added214, accepted214⟩
  · exact ⟨1, 0, 0, tail217, added217, accepted217⟩
  · exact ⟨2, 0, 0, tail218, added218, accepted218⟩
  · exact ⟨2, 1, 1, tail219, added219, accepted219⟩
  · exact ⟨1, 0, 1, tail220, added220, accepted220⟩
  · exact ⟨2, 1, 0, tail222, added222, accepted222⟩
  · exact ⟨2, 0, 1, tail223, added223, accepted223⟩
  · exact ⟨1, 0, 0, tail229, added229, accepted229⟩
def codes4 : List (Fin 1024) := [230, 231, 232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 252, 253]
theorem witness4 (n : Fin 1024) (hn : n ∈ codes4) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, 0, tail230, added230, accepted230⟩
  · exact ⟨1, 2, 2, tail231, added231, accepted231⟩
  · exact ⟨2, 1, 2, tail232, added232, accepted232⟩
  · exact ⟨0, 2, 0, tail233, added233, accepted233⟩
  · exact ⟨0, 1, 2, tail234, added234, accepted234⟩
  · exact ⟨2, 0, 2, tail236, added236, accepted236⟩
  · exact ⟨1, 2, 0, tail237, added237, accepted237⟩
  · exact ⟨1, 0, 2, tail239, added239, accepted239⟩
  · exact ⟨1, 0, 1, tail244, added244, accepted244⟩
  · exact ⟨2, 1, 0, tail246, added246, accepted246⟩
  · exact ⟨2, 0, 1, tail247, added247, accepted247⟩
  · exact ⟨2, 0, 2, tail248, added248, accepted248⟩
  · exact ⟨1, 2, 0, tail249, added249, accepted249⟩
  · exact ⟨1, 0, 2, tail251, added251, accepted251⟩
  · exact ⟨1, 2, 1, tail252, added252, accepted252⟩
  · exact ⟨0, 2, 1, tail253, added253, accepted253⟩
def codes5 : List (Fin 1024) := [254, 276, 278, 279, 280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299]
theorem witness5 (n : Fin 1024) (hn : n ∈ codes5) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes5, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 2, tail254, added254, accepted254⟩
  · exact ⟨0, 1, 0, tail276, added276, accepted276⟩
  · exact ⟨2, 1, 0, tail278, added278, accepted278⟩
  · exact ⟨2, 0, 1, tail279, added279, accepted279⟩
  · exact ⟨0, 2, 0, tail280, added280, accepted280⟩
  · exact ⟨1, 2, 0, tail281, added281, accepted281⟩
  · exact ⟨1, 0, 2, tail283, added283, accepted283⟩
  · exact ⟨1, 2, 1, tail284, added284, accepted284⟩
  · exact ⟨0, 2, 1, tail285, added285, accepted285⟩
  · exact ⟨0, 1, 2, tail286, added286, accepted286⟩
  · exact ⟨0, 2, 0, tail292, added292, accepted292⟩
  · exact ⟨1, 2, 0, tail293, added293, accepted293⟩
  · exact ⟨1, 0, 2, tail295, added295, accepted295⟩
  · exact ⟨0, 1, 0, tail296, added296, accepted296⟩
  · exact ⟨2, 1, 0, tail298, added298, accepted298⟩
  · exact ⟨2, 0, 2, tail299, added299, accepted299⟩
def codes6 : List (Fin 1024) := [301, 302, 303, 308, 309, 310, 313, 314, 315, 316, 318, 319, 324, 326, 327, 328]
theorem witness6 (n : Fin 1024) (hn : n ∈ codes6) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes6, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, tail301, added301, accepted301⟩
  · exact ⟨0, 2, 2, tail302, added302, accepted302⟩
  · exact ⟨1, 2, 2, tail303, added303, accepted303⟩
  · exact ⟨1, 2, 1, tail308, added308, accepted308⟩
  · exact ⟨0, 2, 1, tail309, added309, accepted309⟩
  · exact ⟨0, 1, 2, tail310, added310, accepted310⟩
  · exact ⟨0, 1, 1, tail313, added313, accepted313⟩
  · exact ⟨0, 2, 2, tail314, added314, accepted314⟩
  · exact ⟨1, 2, 2, tail315, added315, accepted315⟩
  · exact ⟨1, 0, 1, tail316, added316, accepted316⟩
  · exact ⟨2, 1, 2, tail318, added318, accepted318⟩
  · exact ⟨2, 0, 1, tail319, added319, accepted319⟩
  · exact ⟨0, 1, 0, tail324, added324, accepted324⟩
  · exact ⟨2, 1, 0, tail326, added326, accepted326⟩
  · exact ⟨2, 0, 1, tail327, added327, accepted327⟩
  · exact ⟨0, 2, 0, tail328, added328, accepted328⟩
def codes7 : List (Fin 1024) := [329, 331, 332, 333, 334, 336, 338, 339, 344, 348, 352, 353, 355, 356, 363, 364]
theorem witness7 (n : Fin 1024) (hn : n ∈ codes7) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes7, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 0, tail329, added329, accepted329⟩
  · exact ⟨1, 0, 1, tail331, added331, accepted331⟩
  · exact ⟨1, 2, 1, tail332, added332, accepted332⟩
  · exact ⟨0, 2, 1, tail333, added333, accepted333⟩
  · exact ⟨0, 1, 0, tail334, added334, accepted334⟩
  · exact ⟨0, 1, 0, tail336, added336, accepted336⟩
  · exact ⟨2, 1, 0, tail338, added338, accepted338⟩
  · exact ⟨2, 0, 1, tail339, added339, accepted339⟩
  · exact ⟨1, 2, 0, tail344, added344, accepted344⟩
  · exact ⟨0, 2, 1, tail348, added348, accepted348⟩
  · exact ⟨0, 2, 0, tail352, added352, accepted352⟩
  · exact ⟨1, 2, 0, tail353, added353, accepted353⟩
  · exact ⟨1, 0, 1, tail355, added355, accepted355⟩
  · exact ⟨1, 2, 0, tail356, added356, accepted356⟩
  · exact ⟨2, 1, 1, tail363, added363, accepted363⟩
  · exact ⟨1, 0, 0, tail364, added364, accepted364⟩
def codes8 : List (Fin 1024) := [366, 367, 368, 369, 370, 372, 376, 378, 379, 382, 388, 389, 391, 392, 394, 395]
theorem witness8 (n : Fin 1024) (hn : n ∈ codes8) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes8, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, 0, tail366, added366, accepted366⟩
  · exact ⟨2, 0, 1, tail367, added367, accepted367⟩
  · exact ⟨1, 2, 1, tail368, added368, accepted368⟩
  · exact ⟨0, 2, 1, tail369, added369, accepted369⟩
  · exact ⟨0, 1, 0, tail370, added370, accepted370⟩
  · exact ⟨0, 2, 1, tail372, added372, accepted372⟩
  · exact ⟨0, 1, 1, tail376, added376, accepted376⟩
  · exact ⟨2, 1, 0, tail378, added378, accepted378⟩
  · exact ⟨2, 0, 1, tail379, added379, accepted379⟩
  · exact ⟨2, 0, 0, tail382, added382, accepted382⟩
  · exact ⟨0, 2, 0, tail388, added388, accepted388⟩
  · exact ⟨1, 2, 0, tail389, added389, accepted389⟩
  · exact ⟨1, 0, 2, tail391, added391, accepted391⟩
  · exact ⟨0, 1, 0, tail392, added392, accepted392⟩
  · exact ⟨2, 1, 0, tail394, added394, accepted394⟩
  · exact ⟨2, 0, 1, tail395, added395, accepted395⟩
def codes9 : List (Fin 1024) := [397, 398, 399, 400, 401, 403, 404, 411, 412, 414, 415, 416, 418, 419, 423, 424]
theorem witness9 (n : Fin 1024) (hn : n ∈ codes9) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes9, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, tail397, added397, accepted397⟩
  · exact ⟨2, 0, 0, tail398, added398, accepted398⟩
  · exact ⟨2, 1, 1, tail399, added399, accepted399⟩
  · exact ⟨0, 2, 0, tail400, added400, accepted400⟩
  · exact ⟨1, 2, 0, tail401, added401, accepted401⟩
  · exact ⟨1, 0, 2, tail403, added403, accepted403⟩
  · exact ⟨1, 2, 0, tail404, added404, accepted404⟩
  · exact ⟨2, 1, 1, tail411, added411, accepted411⟩
  · exact ⟨1, 0, 0, tail412, added412, accepted412⟩
  · exact ⟨2, 1, 2, tail414, added414, accepted414⟩
  · exact ⟨2, 0, 2, tail415, added415, accepted415⟩
  · exact ⟨0, 1, 0, tail416, added416, accepted416⟩
  · exact ⟨2, 1, 0, tail418, added418, accepted418⟩
  · exact ⟨2, 0, 1, tail419, added419, accepted419⟩
  · exact ⟨1, 2, 2, tail423, added423, accepted423⟩
  · exact ⟨2, 1, 0, tail424, added424, accepted424⟩
def codes10 : List (Fin 1024) := [428, 429, 431, 433, 434, 435, 436, 438, 439, 440, 441, 443, 444, 445, 446, 452]
theorem witness10 (n : Fin 1024) (hn : n ∈ codes10) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes10, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, 0, tail428, added428, accepted428⟩
  · exact ⟨1, 2, 1, tail429, added429, accepted429⟩
  · exact ⟨1, 0, 1, tail431, added431, accepted431⟩
  · exact ⟨1, 0, 0, tail433, added433, accepted433⟩
  · exact ⟨2, 0, 0, tail434, added434, accepted434⟩
  · exact ⟨2, 1, 1, tail435, added435, accepted435⟩
  · exact ⟨1, 0, 0, tail436, added436, accepted436⟩
  · exact ⟨2, 1, 2, tail438, added438, accepted438⟩
  · exact ⟨2, 0, 2, tail439, added439, accepted439⟩
  · exact ⟨2, 0, 0, tail440, added440, accepted440⟩
  · exact ⟨1, 2, 1, tail441, added441, accepted441⟩
  · exact ⟨1, 0, 1, tail443, added443, accepted443⟩
  · exact ⟨2, 1, 1, tail444, added444, accepted444⟩
  · exact ⟨0, 2, 1, tail445, added445, accepted445⟩
  · exact ⟨0, 1, 2, tail446, added446, accepted446⟩
  · exact ⟨1, 2, 1, tail452, added452, accepted452⟩
def codes11 : List (Fin 1024) := [453, 454, 457, 458, 459, 460, 462, 463, 464, 465, 466, 468, 472, 474, 475, 478]
theorem witness11 (n : Fin 1024) (hn : n ∈ codes11) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes11, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, 1, tail453, added453, accepted453⟩
  · exact ⟨0, 1, 2, tail454, added454, accepted454⟩
  · exact ⟨0, 1, 1, tail457, added457, accepted457⟩
  · exact ⟨2, 0, 0, tail458, added458, accepted458⟩
  · exact ⟨2, 1, 1, tail459, added459, accepted459⟩
  · exact ⟨1, 0, 1, tail460, added460, accepted460⟩
  · exact ⟨2, 1, 0, tail462, added462, accepted462⟩
  · exact ⟨2, 0, 1, tail463, added463, accepted463⟩
  · exact ⟨1, 2, 1, tail464, added464, accepted464⟩
  · exact ⟨0, 2, 1, tail465, added465, accepted465⟩
  · exact ⟨0, 1, 2, tail466, added466, accepted466⟩
  · exact ⟨0, 2, 1, tail468, added468, accepted468⟩
  · exact ⟨0, 1, 1, tail472, added472, accepted472⟩
  · exact ⟨2, 1, 2, tail474, added474, accepted474⟩
  · exact ⟨2, 0, 2, tail475, added475, accepted475⟩
  · exact ⟨2, 0, 0, tail478, added478, accepted478⟩
def codes12 : List (Fin 1024) := [481, 482, 483, 484, 486, 487, 488, 489, 491, 492, 493, 494, 496, 498, 499, 502]
theorem witness12 (n : Fin 1024) (hn : n ∈ codes12) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes12, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 1, tail481, added481, accepted481⟩
  · exact ⟨2, 0, 0, tail482, added482, accepted482⟩
  · exact ⟨2, 1, 1, tail483, added483, accepted483⟩
  · exact ⟨0, 1, 1, tail484, added484, accepted484⟩
  · exact ⟨2, 1, 2, tail486, added486, accepted486⟩
  · exact ⟨2, 0, 2, tail487, added487, accepted487⟩
  · exact ⟨2, 0, 0, tail488, added488, accepted488⟩
  · exact ⟨1, 2, 0, tail489, added489, accepted489⟩
  · exact ⟨1, 0, 2, tail491, added491, accepted491⟩
  · exact ⟨2, 1, 1, tail492, added492, accepted492⟩
  · exact ⟨0, 2, 0, tail493, added493, accepted493⟩
  · exact ⟨0, 1, 0, tail494, added494, accepted494⟩
  · exact ⟨1, 0, 1, tail496, added496, accepted496⟩
  · exact ⟨2, 1, 0, tail498, added498, accepted498⟩
  · exact ⟨2, 0, 1, tail499, added499, accepted499⟩
  · exact ⟨0, 2, 2, tail502, added502, accepted502⟩
def codes13 : List (Fin 1024) := [504, 505, 506, 508, 532, 533, 535, 536, 538, 539, 541, 542, 543, 548, 550, 551]
theorem witness13 (n : Fin 1024) (hn : n ∈ codes13) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, 1, tail504, added504, accepted504⟩
  · exact ⟨0, 2, 0, tail505, added505, accepted505⟩
  · exact ⟨0, 1, 0, tail506, added506, accepted506⟩
  · exact ⟨2, 0, 1, tail508, added508, accepted508⟩
  · exact ⟨0, 2, 0, tail532, added532, accepted532⟩
  · exact ⟨1, 2, 0, tail533, added533, accepted533⟩
  · exact ⟨1, 0, 1, tail535, added535, accepted535⟩
  · exact ⟨0, 1, 0, tail536, added536, accepted536⟩
  · exact ⟨2, 1, 0, tail538, added538, accepted538⟩
  · exact ⟨2, 0, 1, tail539, added539, accepted539⟩
  · exact ⟨0, 1, 1, tail541, added541, accepted541⟩
  · exact ⟨2, 0, 0, tail542, added542, accepted542⟩
  · exact ⟨2, 1, 1, tail543, added543, accepted543⟩
  · exact ⟨0, 1, 0, tail548, added548, accepted548⟩
  · exact ⟨2, 1, 0, tail550, added550, accepted550⟩
  · exact ⟨2, 0, 1, tail551, added551, accepted551⟩
def codes14 : List (Fin 1024) := [552, 553, 555, 556, 557, 558, 565, 566, 567, 568, 569, 570, 572, 573, 575, 580]
theorem witness14 (n : Fin 1024) (hn : n ∈ codes14) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes14, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, 0, tail552, added552, accepted552⟩
  · exact ⟨1, 2, 0, tail553, added553, accepted553⟩
  · exact ⟨1, 0, 2, tail555, added555, accepted555⟩
  · exact ⟨2, 1, 2, tail556, added556, accepted556⟩
  · exact ⟨0, 2, 1, tail557, added557, accepted557⟩
  · exact ⟨0, 1, 2, tail558, added558, accepted558⟩
  · exact ⟨0, 1, 1, tail565, added565, accepted565⟩
  · exact ⟨0, 2, 2, tail566, added566, accepted566⟩
  · exact ⟨2, 1, 1, tail567, added567, accepted567⟩
  · exact ⟨2, 1, 2, tail568, added568, accepted568⟩
  · exact ⟨0, 2, 1, tail569, added569, accepted569⟩
  · exact ⟨0, 1, 2, tail570, added570, accepted570⟩
  · exact ⟨2, 0, 2, tail572, added572, accepted572⟩
  · exact ⟨1, 2, 1, tail573, added573, accepted573⟩
  · exact ⟨1, 0, 2, tail575, added575, accepted575⟩
  · exact ⟨0, 2, 0, tail580, added580, accepted580⟩
def codes15 : List (Fin 1024) := [581, 583, 584, 586, 587, 589, 590, 591, 592, 593, 595, 596, 603, 604, 606, 607]
theorem witness15 (n : Fin 1024) (hn : n ∈ codes15) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes15, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 0, tail581, added581, accepted581⟩
  · exact ⟨1, 0, 2, tail583, added583, accepted583⟩
  · exact ⟨0, 1, 0, tail584, added584, accepted584⟩
  · exact ⟨2, 1, 0, tail586, added586, accepted586⟩
  · exact ⟨2, 0, 1, tail587, added587, accepted587⟩
  · exact ⟨1, 0, 0, tail589, added589, accepted589⟩
  · exact ⟨2, 0, 0, tail590, added590, accepted590⟩
  · exact ⟨1, 2, 2, tail591, added591, accepted591⟩
  · exact ⟨0, 2, 0, tail592, added592, accepted592⟩
  · exact ⟨1, 2, 0, tail593, added593, accepted593⟩
  · exact ⟨1, 0, 2, tail595, added595, accepted595⟩
  · exact ⟨1, 2, 0, tail596, added596, accepted596⟩
  · exact ⟨2, 1, 1, tail603, added603, accepted603⟩
  · exact ⟨1, 0, 0, tail604, added604, accepted604⟩
  · exact ⟨2, 1, 2, tail606, added606, accepted606⟩
  · exact ⟨2, 0, 2, tail607, added607, accepted607⟩
def codes16 : List (Fin 1024) := [608, 610, 611, 615, 616, 620, 621, 623, 625, 626, 627, 628, 630, 631, 632, 633]
theorem witness16 (n : Fin 1024) (hn : n ∈ codes16) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes16, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 0, tail608, added608, accepted608⟩
  · exact ⟨2, 1, 0, tail610, added610, accepted610⟩
  · exact ⟨2, 0, 1, tail611, added611, accepted611⟩
  · exact ⟨1, 2, 2, tail615, added615, accepted615⟩
  · exact ⟨2, 1, 0, tail616, added616, accepted616⟩
  · exact ⟨2, 0, 0, tail620, added620, accepted620⟩
  · exact ⟨1, 2, 1, tail621, added621, accepted621⟩
  · exact ⟨1, 0, 1, tail623, added623, accepted623⟩
  · exact ⟨1, 0, 0, tail625, added625, accepted625⟩
  · exact ⟨2, 0, 0, tail626, added626, accepted626⟩
  · exact ⟨1, 2, 2, tail627, added627, accepted627⟩
  · exact ⟨1, 0, 0, tail628, added628, accepted628⟩
  · exact ⟨2, 1, 2, tail630, added630, accepted630⟩
  · exact ⟨2, 0, 2, tail631, added631, accepted631⟩
  · exact ⟨2, 0, 0, tail632, added632, accepted632⟩
  · exact ⟨1, 2, 1, tail633, added633, accepted633⟩
def codes17 : List (Fin 1024) := [635, 636, 637, 638, 644, 646, 647, 648, 649, 651, 652, 653, 654, 656, 658, 659]
theorem witness17 (n : Fin 1024) (hn : n ∈ codes17) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes17, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 1, tail635, added635, accepted635⟩
  · exact ⟨1, 2, 2, tail636, added636, accepted636⟩
  · exact ⟨0, 2, 1, tail637, added637, accepted637⟩
  · exact ⟨0, 1, 2, tail638, added638, accepted638⟩
  · exact ⟨0, 1, 0, tail644, added644, accepted644⟩
  · exact ⟨2, 1, 0, tail646, added646, accepted646⟩
  · exact ⟨2, 0, 2, tail647, added647, accepted647⟩
  · exact ⟨0, 2, 0, tail648, added648, accepted648⟩
  · exact ⟨1, 2, 0, tail649, added649, accepted649⟩
  · exact ⟨1, 0, 2, tail651, added651, accepted651⟩
  · exact ⟨2, 1, 2, tail652, added652, accepted652⟩
  · exact ⟨0, 2, 0, tail653, added653, accepted653⟩
  · exact ⟨0, 1, 2, tail654, added654, accepted654⟩
  · exact ⟨0, 1, 0, tail656, added656, accepted656⟩
  · exact ⟨2, 1, 0, tail658, added658, accepted658⟩
  · exact ⟨2, 0, 2, tail659, added659, accepted659⟩
def codes18 : List (Fin 1024) := [663, 664, 668, 669, 671, 672, 673, 675, 676, 684, 688, 689, 690, 692, 693, 695]
theorem witness18 (n : Fin 1024) (hn : n ∈ codes18) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes18, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 2, tail663, added663, accepted663⟩
  · exact ⟨2, 1, 0, tail664, added664, accepted664⟩
  · exact ⟨2, 0, 0, tail668, added668, accepted668⟩
  · exact ⟨1, 2, 0, tail669, added669, accepted669⟩
  · exact ⟨1, 0, 2, tail671, added671, accepted671⟩
  · exact ⟨0, 2, 0, tail672, added672, accepted672⟩
  · exact ⟨1, 2, 0, tail673, added673, accepted673⟩
  · exact ⟨1, 0, 2, tail675, added675, accepted675⟩
  · exact ⟨2, 1, 0, tail676, added676, accepted676⟩
  · exact ⟨0, 1, 2, tail684, added684, accepted684⟩
  · exact ⟨2, 1, 2, tail688, added688, accepted688⟩
  · exact ⟨0, 2, 0, tail689, added689, accepted689⟩
  · exact ⟨0, 1, 2, tail690, added690, accepted690⟩
  · exact ⟨0, 2, 2, tail692, added692, accepted692⟩
  · exact ⟨1, 2, 0, tail693, added693, accepted693⟩
  · exact ⟨1, 0, 2, tail695, added695, accepted695⟩
def codes19 : List (Fin 1024) := [696, 701, 709, 710, 711, 712, 713, 714, 716, 717, 719, 721, 722, 723, 724, 726]
theorem witness19 (n : Fin 1024) (hn : n ∈ codes19) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes19, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 2, tail696, added696, accepted696⟩
  · exact ⟨1, 0, 0, tail701, added701, accepted701⟩
  · exact ⟨1, 0, 0, tail709, added709, accepted709⟩
  · exact ⟨0, 2, 2, tail710, added710, accepted710⟩
  · exact ⟨1, 2, 2, tail711, added711, accepted711⟩
  · exact ⟨2, 1, 2, tail712, added712, accepted712⟩
  · exact ⟨0, 2, 1, tail713, added713, accepted713⟩
  · exact ⟨0, 1, 2, tail714, added714, accepted714⟩
  · exact ⟨2, 0, 2, tail716, added716, accepted716⟩
  · exact ⟨1, 2, 0, tail717, added717, accepted717⟩
  · exact ⟨1, 0, 2, tail719, added719, accepted719⟩
  · exact ⟨1, 0, 0, tail721, added721, accepted721⟩
  · exact ⟨0, 2, 2, tail722, added722, accepted722⟩
  · exact ⟨1, 2, 2, tail723, added723, accepted723⟩
  · exact ⟨1, 0, 0, tail724, added724, accepted724⟩
  · exact ⟨2, 1, 0, tail726, added726, accepted726⟩
def codes20 : List (Fin 1024) := [727, 728, 729, 731, 732, 733, 734, 736, 737, 738, 740, 741, 743, 744, 749, 752]
theorem witness20 (n : Fin 1024) (hn : n ∈ codes20) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes20, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, 1, tail727, added727, accepted727⟩
  · exact ⟨0, 2, 2, tail728, added728, accepted728⟩
  · exact ⟨1, 2, 1, tail729, added729, accepted729⟩
  · exact ⟨1, 0, 1, tail731, added731, accepted731⟩
  · exact ⟨1, 2, 2, tail732, added732, accepted732⟩
  · exact ⟨0, 2, 0, tail733, added733, accepted733⟩
  · exact ⟨0, 1, 0, tail734, added734, accepted734⟩
  · exact ⟨2, 1, 2, tail736, added736, accepted736⟩
  · exact ⟨0, 2, 1, tail737, added737, accepted737⟩
  · exact ⟨0, 1, 2, tail738, added738, accepted738⟩
  · exact ⟨0, 2, 2, tail740, added740, accepted740⟩
  · exact ⟨1, 2, 1, tail741, added741, accepted741⟩
  · exact ⟨1, 0, 1, tail743, added743, accepted743⟩
  · exact ⟨0, 1, 2, tail744, added744, accepted744⟩
  · exact ⟨1, 0, 0, tail749, added749, accepted749⟩
  · exact ⟨2, 0, 2, tail752, added752, accepted752⟩
def codes21 : List (Fin 1024) := [753, 755, 756, 757, 758, 761, 764, 788, 789, 790, 793, 794, 795, 796, 798, 799]
theorem witness21 (n : Fin 1024) (hn : n ∈ codes21) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes21, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 0, tail753, added753, accepted753⟩
  · exact ⟨1, 0, 2, tail755, added755, accepted755⟩
  · exact ⟨1, 2, 2, tail756, added756, accepted756⟩
  · exact ⟨0, 2, 0, tail757, added757, accepted757⟩
  · exact ⟨0, 1, 0, tail758, added758, accepted758⟩
  · exact ⟨0, 1, 1, tail761, added761, accepted761⟩
  · exact ⟨1, 0, 2, tail764, added764, accepted764⟩
  · exact ⟨1, 2, 1, tail788, added788, accepted788⟩
  · exact ⟨0, 2, 1, tail789, added789, accepted789⟩
  · exact ⟨0, 1, 0, tail790, added790, accepted790⟩
  · exact ⟨1, 0, 0, tail793, added793, accepted793⟩
  · exact ⟨2, 0, 0, tail794, added794, accepted794⟩
  · exact ⟨2, 1, 1, tail795, added795, accepted795⟩
  · exact ⟨1, 0, 1, tail796, added796, accepted796⟩
  · exact ⟨2, 1, 0, tail798, added798, accepted798⟩
  · exact ⟨2, 0, 1, tail799, added799, accepted799⟩
def codes22 : List (Fin 1024) := [805, 806, 807, 808, 809, 810, 812, 813, 815, 820, 822, 823, 824, 825, 827, 828]
theorem witness22 (n : Fin 1024) (hn : n ∈ codes22) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes22, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, 0, tail805, added805, accepted805⟩
  · exact ⟨2, 0, 0, tail806, added806, accepted806⟩
  · exact ⟨1, 2, 2, tail807, added807, accepted807⟩
  · exact ⟨2, 1, 2, tail808, added808, accepted808⟩
  · exact ⟨0, 2, 0, tail809, added809, accepted809⟩
  · exact ⟨0, 1, 2, tail810, added810, accepted810⟩
  · exact ⟨2, 0, 2, tail812, added812, accepted812⟩
  · exact ⟨1, 2, 0, tail813, added813, accepted813⟩
  · exact ⟨1, 0, 2, tail815, added815, accepted815⟩
  · exact ⟨1, 0, 1, tail820, added820, accepted820⟩
  · exact ⟨2, 1, 0, tail822, added822, accepted822⟩
  · exact ⟨2, 0, 1, tail823, added823, accepted823⟩
  · exact ⟨2, 0, 2, tail824, added824, accepted824⟩
  · exact ⟨1, 2, 0, tail825, added825, accepted825⟩
  · exact ⟨1, 0, 2, tail827, added827, accepted827⟩
  · exact ⟨1, 2, 1, tail828, added828, accepted828⟩
def codes23 : List (Fin 1024) := [829, 830, 836, 837, 838, 841, 842, 843, 844, 846, 847, 848, 849, 850, 852, 856]
theorem witness23 (n : Fin 1024) (hn : n ∈ codes23) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes23, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, 1, tail829, added829, accepted829⟩
  · exact ⟨0, 1, 2, tail830, added830, accepted830⟩
  · exact ⟨1, 2, 1, tail836, added836, accepted836⟩
  · exact ⟨0, 2, 1, tail837, added837, accepted837⟩
  · exact ⟨0, 1, 2, tail838, added838, accepted838⟩
  · exact ⟨0, 1, 1, tail841, added841, accepted841⟩
  · exact ⟨0, 2, 2, tail842, added842, accepted842⟩
  · exact ⟨2, 1, 1, tail843, added843, accepted843⟩
  · exact ⟨1, 0, 1, tail844, added844, accepted844⟩
  · exact ⟨2, 1, 0, tail846, added846, accepted846⟩
  · exact ⟨2, 0, 1, tail847, added847, accepted847⟩
  · exact ⟨1, 2, 1, tail848, added848, accepted848⟩
  · exact ⟨0, 2, 1, tail849, added849, accepted849⟩
  · exact ⟨0, 1, 2, tail850, added850, accepted850⟩
  · exact ⟨0, 2, 1, tail852, added852, accepted852⟩
  · exact ⟨0, 1, 1, tail856, added856, accepted856⟩
def codes24 : List (Fin 1024) := [858, 859, 862, 865, 866, 867, 868, 870, 871, 872, 873, 875, 876, 877, 878, 880]
theorem witness24 (n : Fin 1024) (hn : n ∈ codes24) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes24, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, 2, tail858, added858, accepted858⟩
  · exact ⟨2, 0, 2, tail859, added859, accepted859⟩
  · exact ⟨2, 0, 0, tail862, added862, accepted862⟩
  · exact ⟨0, 1, 1, tail865, added865, accepted865⟩
  · exact ⟨0, 2, 2, tail866, added866, accepted866⟩
  · exact ⟨2, 1, 1, tail867, added867, accepted867⟩
  · exact ⟨0, 1, 1, tail868, added868, accepted868⟩
  · exact ⟨2, 1, 2, tail870, added870, accepted870⟩
  · exact ⟨2, 0, 2, tail871, added871, accepted871⟩
  · exact ⟨0, 2, 2, tail872, added872, accepted872⟩
  · exact ⟨1, 2, 0, tail873, added873, accepted873⟩
  · exact ⟨1, 0, 2, tail875, added875, accepted875⟩
  · exact ⟨2, 1, 1, tail876, added876, accepted876⟩
  · exact ⟨0, 2, 0, tail877, added877, accepted877⟩
  · exact ⟨0, 1, 0, tail878, added878, accepted878⟩
  · exact ⟨1, 0, 1, tail880, added880, accepted880⟩
def codes25 : List (Fin 1024) := [882, 883, 886, 888, 889, 890, 892, 901, 902, 903, 904, 905, 906, 908, 909, 911]
theorem witness25 (n : Fin 1024) (hn : n ∈ codes25) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes25, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, 0, tail882, added882, accepted882⟩
  · exact ⟨2, 0, 1, tail883, added883, accepted883⟩
  · exact ⟨0, 2, 2, tail886, added886, accepted886⟩
  · exact ⟨2, 1, 1, tail888, added888, accepted888⟩
  · exact ⟨0, 2, 0, tail889, added889, accepted889⟩
  · exact ⟨0, 1, 0, tail890, added890, accepted890⟩
  · exact ⟨2, 0, 1, tail892, added892, accepted892⟩
  · exact ⟨0, 1, 1, tail901, added901, accepted901⟩
  · exact ⟨0, 2, 2, tail902, added902, accepted902⟩
  · exact ⟨1, 2, 2, tail903, added903, accepted903⟩
  · exact ⟨2, 1, 2, tail904, added904, accepted904⟩
  · exact ⟨0, 2, 1, tail905, added905, accepted905⟩
  · exact ⟨0, 1, 2, tail906, added906, accepted906⟩
  · exact ⟨2, 0, 2, tail908, added908, accepted908⟩
  · exact ⟨1, 2, 0, tail909, added909, accepted909⟩
  · exact ⟨1, 0, 2, tail911, added911, accepted911⟩
def codes26 : List (Fin 1024) := [913, 914, 915, 916, 918, 919, 920, 921, 923, 924, 925, 926, 928, 929, 930, 932]
theorem witness26 (n : Fin 1024) (hn : n ∈ codes26) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes26, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, 1, tail913, added913, accepted913⟩
  · exact ⟨0, 2, 2, tail914, added914, accepted914⟩
  · exact ⟨1, 2, 2, tail915, added915, accepted915⟩
  · exact ⟨0, 1, 1, tail916, added916, accepted916⟩
  · exact ⟨2, 1, 0, tail918, added918, accepted918⟩
  · exact ⟨2, 0, 1, tail919, added919, accepted919⟩
  · exact ⟨0, 2, 2, tail920, added920, accepted920⟩
  · exact ⟨1, 2, 1, tail921, added921, accepted921⟩
  · exact ⟨1, 0, 1, tail923, added923, accepted923⟩
  · exact ⟨1, 2, 2, tail924, added924, accepted924⟩
  · exact ⟨0, 2, 0, tail925, added925, accepted925⟩
  · exact ⟨0, 1, 0, tail926, added926, accepted926⟩
  · exact ⟨2, 1, 2, tail928, added928, accepted928⟩
  · exact ⟨0, 2, 1, tail929, added929, accepted929⟩
  · exact ⟨0, 1, 2, tail930, added930, accepted930⟩
  · exact ⟨0, 2, 2, tail932, added932, accepted932⟩
def codes27 : List (Fin 1024) := [933, 935, 936, 941, 944, 945, 947, 948, 949, 950, 953, 956, 964, 966, 967, 968]
theorem witness27 (n : Fin 1024) (hn : n ∈ codes27) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes27, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 1, tail933, added933, accepted933⟩
  · exact ⟨1, 0, 1, tail935, added935, accepted935⟩
  · exact ⟨0, 1, 2, tail936, added936, accepted936⟩
  · exact ⟨1, 0, 0, tail941, added941, accepted941⟩
  · exact ⟨2, 0, 2, tail944, added944, accepted944⟩
  · exact ⟨1, 2, 0, tail945, added945, accepted945⟩
  · exact ⟨1, 0, 2, tail947, added947, accepted947⟩
  · exact ⟨1, 2, 2, tail948, added948, accepted948⟩
  · exact ⟨0, 2, 0, tail949, added949, accepted949⟩
  · exact ⟨0, 1, 0, tail950, added950, accepted950⟩
  · exact ⟨0, 1, 1, tail953, added953, accepted953⟩
  · exact ⟨1, 0, 2, tail956, added956, accepted956⟩
  · exact ⟨1, 0, 1, tail964, added964, accepted964⟩
  · exact ⟨2, 1, 2, tail966, added966, accepted966⟩
  · exact ⟨2, 0, 1, tail967, added967, accepted967⟩
  · exact ⟨2, 0, 2, tail968, added968, accepted968⟩
def codes28 : List (Fin 1024) := [969, 971, 972, 973, 974, 976, 978, 979, 982, 984, 985, 986, 988, 992, 993, 995]
theorem witness28 (n : Fin 1024) (hn : n ∈ codes28) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes28, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 1, tail969, added969, accepted969⟩
  · exact ⟨1, 0, 2, tail971, added971, accepted971⟩
  · exact ⟨1, 2, 1, tail972, added972, accepted972⟩
  · exact ⟨0, 2, 1, tail973, added973, accepted973⟩
  · exact ⟨0, 1, 2, tail974, added974, accepted974⟩
  · exact ⟨1, 0, 1, tail976, added976, accepted976⟩
  · exact ⟨2, 1, 2, tail978, added978, accepted978⟩
  · exact ⟨2, 0, 1, tail979, added979, accepted979⟩
  · exact ⟨0, 2, 2, tail982, added982, accepted982⟩
  · exact ⟨2, 1, 1, tail984, added984, accepted984⟩
  · exact ⟨0, 2, 1, tail985, added985, accepted985⟩
  · exact ⟨0, 1, 2, tail986, added986, accepted986⟩
  · exact ⟨2, 0, 1, tail988, added988, accepted988⟩
  · exact ⟨2, 0, 2, tail992, added992, accepted992⟩
  · exact ⟨1, 2, 1, tail993, added993, accepted993⟩
  · exact ⟨1, 0, 2, tail995, added995, accepted995⟩
def codes29 : List (Fin 1024) := [996, 997, 998, 1001, 1004, 1008, 1009, 1010, 1012, 1016]
theorem witness29 (n : Fin 1024) (hn : n ∈ codes29) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  simp only [codes29, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, 2, tail996, added996, accepted996⟩
  · exact ⟨0, 2, 1, tail997, added997, accepted997⟩
  · exact ⟨0, 1, 2, tail998, added998, accepted998⟩
  · exact ⟨0, 1, 1, tail1001, added1001, accepted1001⟩
  · exact ⟨1, 0, 2, tail1004, added1004, accepted1004⟩
  · exact ⟨1, 2, 1, tail1008, added1008, accepted1008⟩
  · exact ⟨0, 2, 1, tail1009, added1009, accepted1009⟩
  · exact ⟨0, 1, 2, tail1010, added1010, accepted1010⟩
  · exact ⟨2, 0, 1, tail1012, added1012, accepted1012⟩
  · exact ⟨1, 0, 2, tail1016, added1016, accepted1016⟩
private theorem append_witness {l r : List (Fin 1024)}
    (hl : ∀ n ∈ l, ∃ p q a t b, OriginalAccepted (decode n) p q a t b)
    (hr : ∀ n ∈ r, ∃ p q a t b, OriginalAccepted (decode n) p q a t b) :
    ∀ n ∈ l ++ r, ∃ p q a t b, OriginalAccepted (decode n) p q a t b := by
  intro n hn
  rcases List.mem_append.mp hn with h | h
  · exact hl n h
  · exact hr n h
/-- Every whole-deletion pair code has an original-edge certificate. -/
theorem original_witness (n : Fin 1024) (hn : n ∈ syntheticCodes) :
    ∃ p q a tail added, OriginalAccepted (decode n) p q a tail added := by
  exact (append_witness witness0 (append_witness witness1 (append_witness witness2 (append_witness witness3 (append_witness witness4 (append_witness witness5 (append_witness witness6 (append_witness witness7 (append_witness witness8 (append_witness witness9 (append_witness witness10 (append_witness witness11 (append_witness witness12 (append_witness witness13 (append_witness witness14 (append_witness witness15 (append_witness witness16 (append_witness witness17 (append_witness witness18 (append_witness witness19 (append_witness witness20 (append_witness witness21 (append_witness witness22 (append_witness witness23 (append_witness witness24 (append_witness witness25 (append_witness witness26 (append_witness witness27 (append_witness witness28 witness29))))))))))))))))))))))))))))) n hn
end Gallai.Certificate.ThreeAnchor.OriginalOrbits
