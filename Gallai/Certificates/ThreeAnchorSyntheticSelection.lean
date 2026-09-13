/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorSyntheticOrbits

namespace Gallai.Certificate.ThreeAnchor.Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def codes0 : List (Fin 1024) := [84, 86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109]
theorem witness0 (n : Fin 1024) (hn : n ∈ codes0) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes0, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector84, added84, accepted84⟩
  · exact ⟨2, 1, connector86, added86, accepted86⟩
  · exact ⟨2, 0, connector87, added87, accepted87⟩
  · exact ⟨0, 2, connector88, added88, accepted88⟩
  · exact ⟨1, 2, connector89, added89, accepted89⟩
  · exact ⟨1, 0, connector91, added91, accepted91⟩
  · exact ⟨1, 2, connector92, added92, accepted92⟩
  · exact ⟨0, 2, connector93, added93, accepted93⟩
  · exact ⟨0, 1, connector94, added94, accepted94⟩
  · exact ⟨0, 2, connector100, added100, accepted100⟩
  · exact ⟨1, 2, connector101, added101, accepted101⟩
  · exact ⟨1, 0, connector103, added103, accepted103⟩
  · exact ⟨0, 1, connector104, added104, accepted104⟩
  · exact ⟨2, 1, connector106, added106, accepted106⟩
  · exact ⟨2, 0, connector107, added107, accepted107⟩
  · exact ⟨1, 0, connector109, added109, accepted109⟩
def codes1 : List (Fin 1024) := [110, 111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154]
theorem witness1 (n : Fin 1024) (hn : n ∈ codes1) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes1, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, connector110, added110, accepted110⟩
  · exact ⟨1, 2, connector111, added111, accepted111⟩
  · exact ⟨1, 2, connector116, added116, accepted116⟩
  · exact ⟨0, 2, connector117, added117, accepted117⟩
  · exact ⟨0, 1, connector118, added118, accepted118⟩
  · exact ⟨0, 1, connector121, added121, accepted121⟩
  · exact ⟨0, 2, connector122, added122, accepted122⟩
  · exact ⟨1, 2, connector123, added123, accepted123⟩
  · exact ⟨1, 0, connector124, added124, accepted124⟩
  · exact ⟨2, 1, connector126, added126, accepted126⟩
  · exact ⟨2, 0, connector127, added127, accepted127⟩
  · exact ⟨0, 2, connector148, added148, accepted148⟩
  · exact ⟨1, 2, connector149, added149, accepted149⟩
  · exact ⟨1, 0, connector151, added151, accepted151⟩
  · exact ⟨0, 1, connector152, added152, accepted152⟩
  · exact ⟨2, 1, connector154, added154, accepted154⟩
def codes2 : List (Fin 1024) := [155, 157, 158, 159, 164, 166, 167, 168, 169, 171, 172, 173, 174, 181, 182, 183]
theorem witness2 (n : Fin 1024) (hn : n ∈ codes2) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes2, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, connector155, added155, accepted155⟩
  · exact ⟨0, 1, connector157, added157, accepted157⟩
  · exact ⟨2, 0, connector158, added158, accepted158⟩
  · exact ⟨2, 1, connector159, added159, accepted159⟩
  · exact ⟨0, 1, connector164, added164, accepted164⟩
  · exact ⟨2, 1, connector166, added166, accepted166⟩
  · exact ⟨2, 0, connector167, added167, accepted167⟩
  · exact ⟨0, 2, connector168, added168, accepted168⟩
  · exact ⟨1, 2, connector169, added169, accepted169⟩
  · exact ⟨1, 0, connector171, added171, accepted171⟩
  · exact ⟨2, 1, connector172, added172, accepted172⟩
  · exact ⟨0, 2, connector173, added173, accepted173⟩
  · exact ⟨0, 1, connector174, added174, accepted174⟩
  · exact ⟨0, 1, connector181, added181, accepted181⟩
  · exact ⟨0, 2, connector182, added182, accepted182⟩
  · exact ⟨2, 1, connector183, added183, accepted183⟩
def codes3 : List (Fin 1024) := [184, 185, 186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229]
theorem witness3 (n : Fin 1024) (hn : n ∈ codes3) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, connector184, added184, accepted184⟩
  · exact ⟨0, 2, connector185, added185, accepted185⟩
  · exact ⟨0, 1, connector186, added186, accepted186⟩
  · exact ⟨2, 0, connector188, added188, accepted188⟩
  · exact ⟨1, 2, connector189, added189, accepted189⟩
  · exact ⟨1, 0, connector191, added191, accepted191⟩
  · exact ⟨1, 2, connector212, added212, accepted212⟩
  · exact ⟨0, 2, connector213, added213, accepted213⟩
  · exact ⟨0, 1, connector214, added214, accepted214⟩
  · exact ⟨1, 0, connector217, added217, accepted217⟩
  · exact ⟨2, 0, connector218, added218, accepted218⟩
  · exact ⟨2, 1, connector219, added219, accepted219⟩
  · exact ⟨1, 0, connector220, added220, accepted220⟩
  · exact ⟨2, 1, connector222, added222, accepted222⟩
  · exact ⟨2, 0, connector223, added223, accepted223⟩
  · exact ⟨1, 0, connector229, added229, accepted229⟩
def codes4 : List (Fin 1024) := [230, 231, 232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 252, 253]
theorem witness4 (n : Fin 1024) (hn : n ∈ codes4) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, connector230, added230, accepted230⟩
  · exact ⟨1, 2, connector231, added231, accepted231⟩
  · exact ⟨2, 1, connector232, added232, accepted232⟩
  · exact ⟨0, 2, connector233, added233, accepted233⟩
  · exact ⟨0, 1, connector234, added234, accepted234⟩
  · exact ⟨2, 0, connector236, added236, accepted236⟩
  · exact ⟨1, 2, connector237, added237, accepted237⟩
  · exact ⟨1, 0, connector239, added239, accepted239⟩
  · exact ⟨1, 0, connector244, added244, accepted244⟩
  · exact ⟨2, 1, connector246, added246, accepted246⟩
  · exact ⟨2, 0, connector247, added247, accepted247⟩
  · exact ⟨2, 0, connector248, added248, accepted248⟩
  · exact ⟨1, 2, connector249, added249, accepted249⟩
  · exact ⟨1, 0, connector251, added251, accepted251⟩
  · exact ⟨1, 2, connector252, added252, accepted252⟩
  · exact ⟨0, 2, connector253, added253, accepted253⟩
def codes5 : List (Fin 1024) := [254, 276, 278, 279, 280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299]
theorem witness5 (n : Fin 1024) (hn : n ∈ codes5) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes5, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector254, added254, accepted254⟩
  · exact ⟨0, 1, connector276, added276, accepted276⟩
  · exact ⟨2, 1, connector278, added278, accepted278⟩
  · exact ⟨2, 0, connector279, added279, accepted279⟩
  · exact ⟨0, 2, connector280, added280, accepted280⟩
  · exact ⟨1, 2, connector281, added281, accepted281⟩
  · exact ⟨1, 0, connector283, added283, accepted283⟩
  · exact ⟨1, 2, connector284, added284, accepted284⟩
  · exact ⟨0, 2, connector285, added285, accepted285⟩
  · exact ⟨0, 1, connector286, added286, accepted286⟩
  · exact ⟨0, 2, connector292, added292, accepted292⟩
  · exact ⟨1, 2, connector293, added293, accepted293⟩
  · exact ⟨1, 0, connector295, added295, accepted295⟩
  · exact ⟨0, 1, connector296, added296, accepted296⟩
  · exact ⟨2, 1, connector298, added298, accepted298⟩
  · exact ⟨2, 0, connector299, added299, accepted299⟩
def codes6 : List (Fin 1024) := [301, 302, 303, 308, 309, 310, 313, 314, 315, 316, 318, 319, 324, 326, 327, 328]
theorem witness6 (n : Fin 1024) (hn : n ∈ codes6) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes6, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, connector301, added301, accepted301⟩
  · exact ⟨0, 2, connector302, added302, accepted302⟩
  · exact ⟨1, 2, connector303, added303, accepted303⟩
  · exact ⟨1, 2, connector308, added308, accepted308⟩
  · exact ⟨0, 2, connector309, added309, accepted309⟩
  · exact ⟨0, 1, connector310, added310, accepted310⟩
  · exact ⟨0, 1, connector313, added313, accepted313⟩
  · exact ⟨0, 2, connector314, added314, accepted314⟩
  · exact ⟨1, 2, connector315, added315, accepted315⟩
  · exact ⟨1, 0, connector316, added316, accepted316⟩
  · exact ⟨2, 1, connector318, added318, accepted318⟩
  · exact ⟨2, 0, connector319, added319, accepted319⟩
  · exact ⟨0, 1, connector324, added324, accepted324⟩
  · exact ⟨2, 1, connector326, added326, accepted326⟩
  · exact ⟨2, 0, connector327, added327, accepted327⟩
  · exact ⟨0, 2, connector328, added328, accepted328⟩
def codes7 : List (Fin 1024) := [329, 331, 332, 333, 334, 336, 338, 339, 344, 348, 352, 353, 355, 356, 363, 364]
theorem witness7 (n : Fin 1024) (hn : n ∈ codes7) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes7, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector329, added329, accepted329⟩
  · exact ⟨1, 0, connector331, added331, accepted331⟩
  · exact ⟨1, 2, connector332, added332, accepted332⟩
  · exact ⟨0, 2, connector333, added333, accepted333⟩
  · exact ⟨0, 1, connector334, added334, accepted334⟩
  · exact ⟨0, 1, connector336, added336, accepted336⟩
  · exact ⟨2, 1, connector338, added338, accepted338⟩
  · exact ⟨2, 0, connector339, added339, accepted339⟩
  · exact ⟨1, 2, connector344, added344, accepted344⟩
  · exact ⟨0, 2, connector348, added348, accepted348⟩
  · exact ⟨0, 2, connector352, added352, accepted352⟩
  · exact ⟨1, 2, connector353, added353, accepted353⟩
  · exact ⟨1, 0, connector355, added355, accepted355⟩
  · exact ⟨1, 2, connector356, added356, accepted356⟩
  · exact ⟨2, 1, connector363, added363, accepted363⟩
  · exact ⟨1, 0, connector364, added364, accepted364⟩
def codes8 : List (Fin 1024) := [366, 367, 368, 369, 370, 372, 376, 378, 379, 382, 388, 389, 391, 392, 394, 395]
theorem witness8 (n : Fin 1024) (hn : n ∈ codes8) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes8, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, connector366, added366, accepted366⟩
  · exact ⟨2, 0, connector367, added367, accepted367⟩
  · exact ⟨1, 2, connector368, added368, accepted368⟩
  · exact ⟨0, 2, connector369, added369, accepted369⟩
  · exact ⟨0, 1, connector370, added370, accepted370⟩
  · exact ⟨0, 2, connector372, added372, accepted372⟩
  · exact ⟨0, 1, connector376, added376, accepted376⟩
  · exact ⟨2, 1, connector378, added378, accepted378⟩
  · exact ⟨2, 0, connector379, added379, accepted379⟩
  · exact ⟨2, 0, connector382, added382, accepted382⟩
  · exact ⟨0, 2, connector388, added388, accepted388⟩
  · exact ⟨1, 2, connector389, added389, accepted389⟩
  · exact ⟨1, 0, connector391, added391, accepted391⟩
  · exact ⟨0, 1, connector392, added392, accepted392⟩
  · exact ⟨2, 1, connector394, added394, accepted394⟩
  · exact ⟨2, 0, connector395, added395, accepted395⟩
def codes9 : List (Fin 1024) := [397, 398, 399, 400, 401, 403, 404, 411, 412, 414, 415, 416, 418, 419, 423, 424]
theorem witness9 (n : Fin 1024) (hn : n ∈ codes9) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes9, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, connector397, added397, accepted397⟩
  · exact ⟨2, 0, connector398, added398, accepted398⟩
  · exact ⟨2, 1, connector399, added399, accepted399⟩
  · exact ⟨0, 2, connector400, added400, accepted400⟩
  · exact ⟨1, 2, connector401, added401, accepted401⟩
  · exact ⟨1, 0, connector403, added403, accepted403⟩
  · exact ⟨1, 2, connector404, added404, accepted404⟩
  · exact ⟨2, 1, connector411, added411, accepted411⟩
  · exact ⟨1, 0, connector412, added412, accepted412⟩
  · exact ⟨2, 1, connector414, added414, accepted414⟩
  · exact ⟨2, 0, connector415, added415, accepted415⟩
  · exact ⟨0, 1, connector416, added416, accepted416⟩
  · exact ⟨2, 1, connector418, added418, accepted418⟩
  · exact ⟨2, 0, connector419, added419, accepted419⟩
  · exact ⟨1, 2, connector423, added423, accepted423⟩
  · exact ⟨2, 1, connector424, added424, accepted424⟩
def codes10 : List (Fin 1024) := [428, 429, 431, 433, 434, 435, 436, 438, 439, 440, 441, 443, 444, 445, 446, 452]
theorem witness10 (n : Fin 1024) (hn : n ∈ codes10) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes10, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, connector428, added428, accepted428⟩
  · exact ⟨1, 2, connector429, added429, accepted429⟩
  · exact ⟨1, 0, connector431, added431, accepted431⟩
  · exact ⟨1, 0, connector433, added433, accepted433⟩
  · exact ⟨2, 0, connector434, added434, accepted434⟩
  · exact ⟨2, 1, connector435, added435, accepted435⟩
  · exact ⟨1, 0, connector436, added436, accepted436⟩
  · exact ⟨2, 1, connector438, added438, accepted438⟩
  · exact ⟨2, 0, connector439, added439, accepted439⟩
  · exact ⟨2, 0, connector440, added440, accepted440⟩
  · exact ⟨1, 2, connector441, added441, accepted441⟩
  · exact ⟨1, 0, connector443, added443, accepted443⟩
  · exact ⟨2, 1, connector444, added444, accepted444⟩
  · exact ⟨0, 2, connector445, added445, accepted445⟩
  · exact ⟨0, 1, connector446, added446, accepted446⟩
  · exact ⟨1, 2, connector452, added452, accepted452⟩
def codes11 : List (Fin 1024) := [453, 454, 457, 458, 459, 460, 462, 463, 464, 465, 466, 468, 472, 474, 475, 478]
theorem witness11 (n : Fin 1024) (hn : n ∈ codes11) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes11, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, connector453, added453, accepted453⟩
  · exact ⟨0, 1, connector454, added454, accepted454⟩
  · exact ⟨0, 1, connector457, added457, accepted457⟩
  · exact ⟨2, 0, connector458, added458, accepted458⟩
  · exact ⟨2, 1, connector459, added459, accepted459⟩
  · exact ⟨1, 0, connector460, added460, accepted460⟩
  · exact ⟨2, 1, connector462, added462, accepted462⟩
  · exact ⟨2, 0, connector463, added463, accepted463⟩
  · exact ⟨1, 2, connector464, added464, accepted464⟩
  · exact ⟨0, 2, connector465, added465, accepted465⟩
  · exact ⟨0, 1, connector466, added466, accepted466⟩
  · exact ⟨0, 2, connector468, added468, accepted468⟩
  · exact ⟨0, 1, connector472, added472, accepted472⟩
  · exact ⟨2, 1, connector474, added474, accepted474⟩
  · exact ⟨2, 0, connector475, added475, accepted475⟩
  · exact ⟨2, 0, connector478, added478, accepted478⟩
def codes12 : List (Fin 1024) := [481, 482, 483, 484, 486, 487, 488, 489, 491, 492, 493, 494, 496, 498, 499, 502]
theorem witness12 (n : Fin 1024) (hn : n ∈ codes12) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes12, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector481, added481, accepted481⟩
  · exact ⟨2, 0, connector482, added482, accepted482⟩
  · exact ⟨2, 1, connector483, added483, accepted483⟩
  · exact ⟨0, 1, connector484, added484, accepted484⟩
  · exact ⟨2, 1, connector486, added486, accepted486⟩
  · exact ⟨2, 0, connector487, added487, accepted487⟩
  · exact ⟨2, 0, connector488, added488, accepted488⟩
  · exact ⟨1, 2, connector489, added489, accepted489⟩
  · exact ⟨1, 0, connector491, added491, accepted491⟩
  · exact ⟨2, 1, connector492, added492, accepted492⟩
  · exact ⟨0, 2, connector493, added493, accepted493⟩
  · exact ⟨0, 1, connector494, added494, accepted494⟩
  · exact ⟨1, 0, connector496, added496, accepted496⟩
  · exact ⟨2, 1, connector498, added498, accepted498⟩
  · exact ⟨2, 0, connector499, added499, accepted499⟩
  · exact ⟨0, 2, connector502, added502, accepted502⟩
def codes13 : List (Fin 1024) := [504, 505, 506, 508, 532, 533, 535, 536, 538, 539, 541, 542, 543, 548, 550, 551]
theorem witness13 (n : Fin 1024) (hn : n ∈ codes13) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, connector504, added504, accepted504⟩
  · exact ⟨0, 2, connector505, added505, accepted505⟩
  · exact ⟨0, 1, connector506, added506, accepted506⟩
  · exact ⟨2, 0, connector508, added508, accepted508⟩
  · exact ⟨0, 2, connector532, added532, accepted532⟩
  · exact ⟨1, 2, connector533, added533, accepted533⟩
  · exact ⟨1, 0, connector535, added535, accepted535⟩
  · exact ⟨0, 1, connector536, added536, accepted536⟩
  · exact ⟨2, 1, connector538, added538, accepted538⟩
  · exact ⟨2, 0, connector539, added539, accepted539⟩
  · exact ⟨0, 1, connector541, added541, accepted541⟩
  · exact ⟨2, 0, connector542, added542, accepted542⟩
  · exact ⟨2, 1, connector543, added543, accepted543⟩
  · exact ⟨0, 1, connector548, added548, accepted548⟩
  · exact ⟨2, 1, connector550, added550, accepted550⟩
  · exact ⟨2, 0, connector551, added551, accepted551⟩
def codes14 : List (Fin 1024) := [552, 553, 555, 556, 557, 558, 565, 566, 567, 568, 569, 570, 572, 573, 575, 580]
theorem witness14 (n : Fin 1024) (hn : n ∈ codes14) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes14, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, connector552, added552, accepted552⟩
  · exact ⟨1, 2, connector553, added553, accepted553⟩
  · exact ⟨1, 0, connector555, added555, accepted555⟩
  · exact ⟨2, 1, connector556, added556, accepted556⟩
  · exact ⟨0, 2, connector557, added557, accepted557⟩
  · exact ⟨0, 1, connector558, added558, accepted558⟩
  · exact ⟨0, 1, connector565, added565, accepted565⟩
  · exact ⟨0, 2, connector566, added566, accepted566⟩
  · exact ⟨2, 1, connector567, added567, accepted567⟩
  · exact ⟨2, 1, connector568, added568, accepted568⟩
  · exact ⟨0, 2, connector569, added569, accepted569⟩
  · exact ⟨0, 1, connector570, added570, accepted570⟩
  · exact ⟨2, 0, connector572, added572, accepted572⟩
  · exact ⟨1, 2, connector573, added573, accepted573⟩
  · exact ⟨1, 0, connector575, added575, accepted575⟩
  · exact ⟨0, 2, connector580, added580, accepted580⟩
def codes15 : List (Fin 1024) := [581, 583, 584, 586, 587, 589, 590, 591, 592, 593, 595, 596, 603, 604, 606, 607]
theorem witness15 (n : Fin 1024) (hn : n ∈ codes15) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes15, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector581, added581, accepted581⟩
  · exact ⟨1, 0, connector583, added583, accepted583⟩
  · exact ⟨0, 1, connector584, added584, accepted584⟩
  · exact ⟨2, 1, connector586, added586, accepted586⟩
  · exact ⟨2, 0, connector587, added587, accepted587⟩
  · exact ⟨1, 0, connector589, added589, accepted589⟩
  · exact ⟨2, 0, connector590, added590, accepted590⟩
  · exact ⟨1, 2, connector591, added591, accepted591⟩
  · exact ⟨0, 2, connector592, added592, accepted592⟩
  · exact ⟨1, 2, connector593, added593, accepted593⟩
  · exact ⟨1, 0, connector595, added595, accepted595⟩
  · exact ⟨1, 2, connector596, added596, accepted596⟩
  · exact ⟨2, 1, connector603, added603, accepted603⟩
  · exact ⟨1, 0, connector604, added604, accepted604⟩
  · exact ⟨2, 1, connector606, added606, accepted606⟩
  · exact ⟨2, 0, connector607, added607, accepted607⟩
def codes16 : List (Fin 1024) := [608, 610, 611, 615, 616, 620, 621, 623, 625, 626, 627, 628, 630, 631, 632, 633]
theorem witness16 (n : Fin 1024) (hn : n ∈ codes16) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes16, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector608, added608, accepted608⟩
  · exact ⟨2, 1, connector610, added610, accepted610⟩
  · exact ⟨2, 0, connector611, added611, accepted611⟩
  · exact ⟨1, 2, connector615, added615, accepted615⟩
  · exact ⟨2, 1, connector616, added616, accepted616⟩
  · exact ⟨2, 0, connector620, added620, accepted620⟩
  · exact ⟨1, 2, connector621, added621, accepted621⟩
  · exact ⟨1, 0, connector623, added623, accepted623⟩
  · exact ⟨1, 0, connector625, added625, accepted625⟩
  · exact ⟨2, 0, connector626, added626, accepted626⟩
  · exact ⟨1, 2, connector627, added627, accepted627⟩
  · exact ⟨1, 0, connector628, added628, accepted628⟩
  · exact ⟨2, 1, connector630, added630, accepted630⟩
  · exact ⟨2, 0, connector631, added631, accepted631⟩
  · exact ⟨2, 0, connector632, added632, accepted632⟩
  · exact ⟨1, 2, connector633, added633, accepted633⟩
def codes17 : List (Fin 1024) := [635, 636, 637, 638, 644, 646, 647, 648, 649, 651, 652, 653, 654, 656, 658, 659]
theorem witness17 (n : Fin 1024) (hn : n ∈ codes17) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes17, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, connector635, added635, accepted635⟩
  · exact ⟨1, 2, connector636, added636, accepted636⟩
  · exact ⟨0, 2, connector637, added637, accepted637⟩
  · exact ⟨0, 1, connector638, added638, accepted638⟩
  · exact ⟨0, 1, connector644, added644, accepted644⟩
  · exact ⟨2, 1, connector646, added646, accepted646⟩
  · exact ⟨2, 0, connector647, added647, accepted647⟩
  · exact ⟨0, 2, connector648, added648, accepted648⟩
  · exact ⟨1, 2, connector649, added649, accepted649⟩
  · exact ⟨1, 0, connector651, added651, accepted651⟩
  · exact ⟨2, 1, connector652, added652, accepted652⟩
  · exact ⟨0, 2, connector653, added653, accepted653⟩
  · exact ⟨0, 1, connector654, added654, accepted654⟩
  · exact ⟨0, 1, connector656, added656, accepted656⟩
  · exact ⟨2, 1, connector658, added658, accepted658⟩
  · exact ⟨2, 0, connector659, added659, accepted659⟩
def codes18 : List (Fin 1024) := [663, 664, 668, 669, 671, 672, 673, 675, 676, 684, 688, 689, 690, 692, 693, 695]
theorem witness18 (n : Fin 1024) (hn : n ∈ codes18) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes18, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector663, added663, accepted663⟩
  · exact ⟨2, 1, connector664, added664, accepted664⟩
  · exact ⟨2, 0, connector668, added668, accepted668⟩
  · exact ⟨1, 2, connector669, added669, accepted669⟩
  · exact ⟨1, 0, connector671, added671, accepted671⟩
  · exact ⟨0, 2, connector672, added672, accepted672⟩
  · exact ⟨1, 2, connector673, added673, accepted673⟩
  · exact ⟨1, 0, connector675, added675, accepted675⟩
  · exact ⟨2, 1, connector676, added676, accepted676⟩
  · exact ⟨0, 1, connector684, added684, accepted684⟩
  · exact ⟨2, 1, connector688, added688, accepted688⟩
  · exact ⟨0, 2, connector689, added689, accepted689⟩
  · exact ⟨0, 1, connector690, added690, accepted690⟩
  · exact ⟨0, 2, connector692, added692, accepted692⟩
  · exact ⟨1, 2, connector693, added693, accepted693⟩
  · exact ⟨1, 0, connector695, added695, accepted695⟩
def codes19 : List (Fin 1024) := [696, 701, 709, 710, 711, 712, 713, 714, 716, 717, 719, 721, 722, 723, 724, 726]
theorem witness19 (n : Fin 1024) (hn : n ∈ codes19) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes19, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector696, added696, accepted696⟩
  · exact ⟨1, 0, connector701, added701, accepted701⟩
  · exact ⟨1, 0, connector709, added709, accepted709⟩
  · exact ⟨0, 2, connector710, added710, accepted710⟩
  · exact ⟨1, 2, connector711, added711, accepted711⟩
  · exact ⟨2, 1, connector712, added712, accepted712⟩
  · exact ⟨0, 2, connector713, added713, accepted713⟩
  · exact ⟨0, 1, connector714, added714, accepted714⟩
  · exact ⟨2, 0, connector716, added716, accepted716⟩
  · exact ⟨1, 2, connector717, added717, accepted717⟩
  · exact ⟨1, 0, connector719, added719, accepted719⟩
  · exact ⟨1, 0, connector721, added721, accepted721⟩
  · exact ⟨0, 2, connector722, added722, accepted722⟩
  · exact ⟨1, 2, connector723, added723, accepted723⟩
  · exact ⟨1, 0, connector724, added724, accepted724⟩
  · exact ⟨2, 1, connector726, added726, accepted726⟩
def codes20 : List (Fin 1024) := [727, 728, 729, 731, 732, 733, 734, 736, 737, 738, 740, 741, 743, 744, 749, 752]
theorem witness20 (n : Fin 1024) (hn : n ∈ codes20) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes20, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, connector727, added727, accepted727⟩
  · exact ⟨0, 2, connector728, added728, accepted728⟩
  · exact ⟨1, 2, connector729, added729, accepted729⟩
  · exact ⟨1, 0, connector731, added731, accepted731⟩
  · exact ⟨1, 2, connector732, added732, accepted732⟩
  · exact ⟨0, 2, connector733, added733, accepted733⟩
  · exact ⟨0, 1, connector734, added734, accepted734⟩
  · exact ⟨2, 1, connector736, added736, accepted736⟩
  · exact ⟨0, 2, connector737, added737, accepted737⟩
  · exact ⟨0, 1, connector738, added738, accepted738⟩
  · exact ⟨0, 2, connector740, added740, accepted740⟩
  · exact ⟨1, 2, connector741, added741, accepted741⟩
  · exact ⟨1, 0, connector743, added743, accepted743⟩
  · exact ⟨0, 1, connector744, added744, accepted744⟩
  · exact ⟨1, 0, connector749, added749, accepted749⟩
  · exact ⟨2, 0, connector752, added752, accepted752⟩
def codes21 : List (Fin 1024) := [753, 755, 756, 757, 758, 761, 764, 788, 789, 790, 793, 794, 795, 796, 798, 799]
theorem witness21 (n : Fin 1024) (hn : n ∈ codes21) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes21, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector753, added753, accepted753⟩
  · exact ⟨1, 0, connector755, added755, accepted755⟩
  · exact ⟨1, 2, connector756, added756, accepted756⟩
  · exact ⟨0, 2, connector757, added757, accepted757⟩
  · exact ⟨0, 1, connector758, added758, accepted758⟩
  · exact ⟨0, 1, connector761, added761, accepted761⟩
  · exact ⟨1, 0, connector764, added764, accepted764⟩
  · exact ⟨1, 2, connector788, added788, accepted788⟩
  · exact ⟨0, 2, connector789, added789, accepted789⟩
  · exact ⟨0, 1, connector790, added790, accepted790⟩
  · exact ⟨1, 0, connector793, added793, accepted793⟩
  · exact ⟨2, 0, connector794, added794, accepted794⟩
  · exact ⟨2, 1, connector795, added795, accepted795⟩
  · exact ⟨1, 0, connector796, added796, accepted796⟩
  · exact ⟨2, 1, connector798, added798, accepted798⟩
  · exact ⟨2, 0, connector799, added799, accepted799⟩
def codes22 : List (Fin 1024) := [805, 806, 807, 808, 809, 810, 812, 813, 815, 820, 822, 823, 824, 825, 827, 828]
theorem witness22 (n : Fin 1024) (hn : n ∈ codes22) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes22, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, connector805, added805, accepted805⟩
  · exact ⟨2, 0, connector806, added806, accepted806⟩
  · exact ⟨1, 2, connector807, added807, accepted807⟩
  · exact ⟨2, 1, connector808, added808, accepted808⟩
  · exact ⟨0, 2, connector809, added809, accepted809⟩
  · exact ⟨0, 1, connector810, added810, accepted810⟩
  · exact ⟨2, 0, connector812, added812, accepted812⟩
  · exact ⟨1, 2, connector813, added813, accepted813⟩
  · exact ⟨1, 0, connector815, added815, accepted815⟩
  · exact ⟨1, 0, connector820, added820, accepted820⟩
  · exact ⟨2, 1, connector822, added822, accepted822⟩
  · exact ⟨2, 0, connector823, added823, accepted823⟩
  · exact ⟨2, 0, connector824, added824, accepted824⟩
  · exact ⟨1, 2, connector825, added825, accepted825⟩
  · exact ⟨1, 0, connector827, added827, accepted827⟩
  · exact ⟨1, 2, connector828, added828, accepted828⟩
def codes23 : List (Fin 1024) := [829, 830, 836, 837, 838, 841, 842, 843, 844, 846, 847, 848, 849, 850, 852, 856]
theorem witness23 (n : Fin 1024) (hn : n ∈ codes23) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes23, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, connector829, added829, accepted829⟩
  · exact ⟨0, 1, connector830, added830, accepted830⟩
  · exact ⟨1, 2, connector836, added836, accepted836⟩
  · exact ⟨0, 2, connector837, added837, accepted837⟩
  · exact ⟨0, 1, connector838, added838, accepted838⟩
  · exact ⟨0, 1, connector841, added841, accepted841⟩
  · exact ⟨0, 2, connector842, added842, accepted842⟩
  · exact ⟨2, 1, connector843, added843, accepted843⟩
  · exact ⟨1, 0, connector844, added844, accepted844⟩
  · exact ⟨2, 1, connector846, added846, accepted846⟩
  · exact ⟨2, 0, connector847, added847, accepted847⟩
  · exact ⟨1, 2, connector848, added848, accepted848⟩
  · exact ⟨0, 2, connector849, added849, accepted849⟩
  · exact ⟨0, 1, connector850, added850, accepted850⟩
  · exact ⟨0, 2, connector852, added852, accepted852⟩
  · exact ⟨0, 1, connector856, added856, accepted856⟩
def codes24 : List (Fin 1024) := [858, 859, 862, 865, 866, 867, 868, 870, 871, 872, 873, 875, 876, 877, 878, 880]
theorem witness24 (n : Fin 1024) (hn : n ∈ codes24) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes24, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, connector858, added858, accepted858⟩
  · exact ⟨2, 0, connector859, added859, accepted859⟩
  · exact ⟨2, 0, connector862, added862, accepted862⟩
  · exact ⟨0, 1, connector865, added865, accepted865⟩
  · exact ⟨0, 2, connector866, added866, accepted866⟩
  · exact ⟨2, 1, connector867, added867, accepted867⟩
  · exact ⟨0, 1, connector868, added868, accepted868⟩
  · exact ⟨2, 1, connector870, added870, accepted870⟩
  · exact ⟨2, 0, connector871, added871, accepted871⟩
  · exact ⟨0, 2, connector872, added872, accepted872⟩
  · exact ⟨1, 2, connector873, added873, accepted873⟩
  · exact ⟨1, 0, connector875, added875, accepted875⟩
  · exact ⟨2, 1, connector876, added876, accepted876⟩
  · exact ⟨0, 2, connector877, added877, accepted877⟩
  · exact ⟨0, 1, connector878, added878, accepted878⟩
  · exact ⟨1, 0, connector880, added880, accepted880⟩
def codes25 : List (Fin 1024) := [882, 883, 886, 888, 889, 890, 892, 901, 902, 903, 904, 905, 906, 908, 909, 911]
theorem witness25 (n : Fin 1024) (hn : n ∈ codes25) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes25, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, connector882, added882, accepted882⟩
  · exact ⟨2, 0, connector883, added883, accepted883⟩
  · exact ⟨0, 2, connector886, added886, accepted886⟩
  · exact ⟨2, 1, connector888, added888, accepted888⟩
  · exact ⟨0, 2, connector889, added889, accepted889⟩
  · exact ⟨0, 1, connector890, added890, accepted890⟩
  · exact ⟨2, 0, connector892, added892, accepted892⟩
  · exact ⟨0, 1, connector901, added901, accepted901⟩
  · exact ⟨0, 2, connector902, added902, accepted902⟩
  · exact ⟨1, 2, connector903, added903, accepted903⟩
  · exact ⟨2, 1, connector904, added904, accepted904⟩
  · exact ⟨0, 2, connector905, added905, accepted905⟩
  · exact ⟨0, 1, connector906, added906, accepted906⟩
  · exact ⟨2, 0, connector908, added908, accepted908⟩
  · exact ⟨1, 2, connector909, added909, accepted909⟩
  · exact ⟨1, 0, connector911, added911, accepted911⟩
def codes26 : List (Fin 1024) := [913, 914, 915, 916, 918, 919, 920, 921, 923, 924, 925, 926, 928, 929, 930, 932]
theorem witness26 (n : Fin 1024) (hn : n ∈ codes26) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes26, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, connector913, added913, accepted913⟩
  · exact ⟨0, 2, connector914, added914, accepted914⟩
  · exact ⟨1, 2, connector915, added915, accepted915⟩
  · exact ⟨0, 1, connector916, added916, accepted916⟩
  · exact ⟨2, 1, connector918, added918, accepted918⟩
  · exact ⟨2, 0, connector919, added919, accepted919⟩
  · exact ⟨0, 2, connector920, added920, accepted920⟩
  · exact ⟨1, 2, connector921, added921, accepted921⟩
  · exact ⟨1, 0, connector923, added923, accepted923⟩
  · exact ⟨1, 2, connector924, added924, accepted924⟩
  · exact ⟨0, 2, connector925, added925, accepted925⟩
  · exact ⟨0, 1, connector926, added926, accepted926⟩
  · exact ⟨2, 1, connector928, added928, accepted928⟩
  · exact ⟨0, 2, connector929, added929, accepted929⟩
  · exact ⟨0, 1, connector930, added930, accepted930⟩
  · exact ⟨0, 2, connector932, added932, accepted932⟩
def codes27 : List (Fin 1024) := [933, 935, 936, 941, 944, 945, 947, 948, 949, 950, 953, 956, 964, 966, 967, 968]
theorem witness27 (n : Fin 1024) (hn : n ∈ codes27) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes27, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector933, added933, accepted933⟩
  · exact ⟨1, 0, connector935, added935, accepted935⟩
  · exact ⟨0, 1, connector936, added936, accepted936⟩
  · exact ⟨1, 0, connector941, added941, accepted941⟩
  · exact ⟨2, 0, connector944, added944, accepted944⟩
  · exact ⟨1, 2, connector945, added945, accepted945⟩
  · exact ⟨1, 0, connector947, added947, accepted947⟩
  · exact ⟨1, 2, connector948, added948, accepted948⟩
  · exact ⟨0, 2, connector949, added949, accepted949⟩
  · exact ⟨0, 1, connector950, added950, accepted950⟩
  · exact ⟨0, 1, connector953, added953, accepted953⟩
  · exact ⟨1, 0, connector956, added956, accepted956⟩
  · exact ⟨1, 0, connector964, added964, accepted964⟩
  · exact ⟨2, 1, connector966, added966, accepted966⟩
  · exact ⟨2, 0, connector967, added967, accepted967⟩
  · exact ⟨2, 0, connector968, added968, accepted968⟩
def codes28 : List (Fin 1024) := [969, 971, 972, 973, 974, 976, 978, 979, 982, 984, 985, 986, 988, 992, 993, 995]
theorem witness28 (n : Fin 1024) (hn : n ∈ codes28) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes28, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector969, added969, accepted969⟩
  · exact ⟨1, 0, connector971, added971, accepted971⟩
  · exact ⟨1, 2, connector972, added972, accepted972⟩
  · exact ⟨0, 2, connector973, added973, accepted973⟩
  · exact ⟨0, 1, connector974, added974, accepted974⟩
  · exact ⟨1, 0, connector976, added976, accepted976⟩
  · exact ⟨2, 1, connector978, added978, accepted978⟩
  · exact ⟨2, 0, connector979, added979, accepted979⟩
  · exact ⟨0, 2, connector982, added982, accepted982⟩
  · exact ⟨2, 1, connector984, added984, accepted984⟩
  · exact ⟨0, 2, connector985, added985, accepted985⟩
  · exact ⟨0, 1, connector986, added986, accepted986⟩
  · exact ⟨2, 0, connector988, added988, accepted988⟩
  · exact ⟨2, 0, connector992, added992, accepted992⟩
  · exact ⟨1, 2, connector993, added993, accepted993⟩
  · exact ⟨1, 0, connector995, added995, accepted995⟩
def codes29 : List (Fin 1024) := [996, 997, 998, 1001, 1004, 1008, 1009, 1010, 1012, 1016]
theorem witness29 (n : Fin 1024) (hn : n ∈ codes29) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  simp only [codes29, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, connector996, added996, accepted996⟩
  · exact ⟨0, 2, connector997, added997, accepted997⟩
  · exact ⟨0, 1, connector998, added998, accepted998⟩
  · exact ⟨0, 1, connector1001, added1001, accepted1001⟩
  · exact ⟨1, 0, connector1004, added1004, accepted1004⟩
  · exact ⟨1, 2, connector1008, added1008, accepted1008⟩
  · exact ⟨0, 2, connector1009, added1009, accepted1009⟩
  · exact ⟨0, 1, connector1010, added1010, accepted1010⟩
  · exact ⟨2, 0, connector1012, added1012, accepted1012⟩
  · exact ⟨1, 0, connector1016, added1016, accepted1016⟩
private theorem append_witness {l r : List (Fin 1024)}
    (hl : ∀ n ∈ l, ∃ p q c a, SyntheticAccepted (decode n) p q c a)
    (hr : ∀ n ∈ r, ∃ p q c a, SyntheticAccepted (decode n) p q c a) :
    ∀ n ∈ l ++ r, ∃ p q c a, SyntheticAccepted (decode n) p q c a := by
  intro n hn
  rcases List.mem_append.mp hn with h | h
  · exact hl n h
  · exact hr n h
/-- Every covered code supplies an actual accepted synthetic interface. -/
theorem synthetic_witness (n : Fin 1024) (hn : n ∈ syntheticCodes) :
    ∃ p q connector added, SyntheticAccepted (decode n) p q connector added := by
  exact (append_witness witness0 (append_witness witness1 (append_witness witness2 (append_witness witness3 (append_witness witness4 (append_witness witness5 (append_witness witness6 (append_witness witness7 (append_witness witness8 (append_witness witness9 (append_witness witness10 (append_witness witness11 (append_witness witness12 (append_witness witness13 (append_witness witness14 (append_witness witness15 (append_witness witness16 (append_witness witness17 (append_witness witness18 (append_witness witness19 (append_witness witness20 (append_witness witness21 (append_witness witness22 (append_witness witness23 (append_witness witness24 (append_witness witness25 (append_witness witness26 (append_witness witness27 (append_witness witness28 witness29))))))))))))))))))))))))))))) n hn
end Gallai.Certificate.ThreeAnchor.Orbits
