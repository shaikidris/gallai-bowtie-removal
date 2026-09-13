/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOrbits

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
def codes0 : List (Fin 1024) := [86, 87, 88, 89, 91, 92, 93, 94, 100, 101, 103, 104, 106, 107, 109, 110]
theorem witness0 (n : Fin 1024) (hn : n ∈ codes0) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes0, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, tails86, added86, attachments86, accepted86⟩
  · exact ⟨2, 0, tails87, added87, attachments87, accepted87⟩
  · exact ⟨0, 2, tails88, added88, attachments88, accepted88⟩
  · exact ⟨1, 2, tails89, added89, attachments89, accepted89⟩
  · exact ⟨1, 0, tails91, added91, attachments91, accepted91⟩
  · exact ⟨1, 2, tails92, added92, attachments92, accepted92⟩
  · exact ⟨0, 2, tails93, added93, attachments93, accepted93⟩
  · exact ⟨0, 1, tails94, added94, attachments94, accepted94⟩
  · exact ⟨0, 2, tails100, added100, attachments100, accepted100⟩
  · exact ⟨1, 2, tails101, added101, attachments101, accepted101⟩
  · exact ⟨1, 0, tails103, added103, attachments103, accepted103⟩
  · exact ⟨0, 1, tails104, added104, attachments104, accepted104⟩
  · exact ⟨2, 1, tails106, added106, attachments106, accepted106⟩
  · exact ⟨2, 0, tails107, added107, attachments107, accepted107⟩
  · exact ⟨1, 0, tails109, added109, attachments109, accepted109⟩
  · exact ⟨0, 2, tails110, added110, attachments110, accepted110⟩
def codes1 : List (Fin 1024) := [111, 116, 117, 118, 121, 122, 123, 124, 126, 127, 148, 149, 151, 152, 154, 155]
theorem witness1 (n : Fin 1024) (hn : n ∈ codes1) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes1, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails111, added111, attachments111, accepted111⟩
  · exact ⟨1, 2, tails116, added116, attachments116, accepted116⟩
  · exact ⟨0, 2, tails117, added117, attachments117, accepted117⟩
  · exact ⟨0, 1, tails118, added118, attachments118, accepted118⟩
  · exact ⟨0, 1, tails121, added121, attachments121, accepted121⟩
  · exact ⟨0, 2, tails122, added122, attachments122, accepted122⟩
  · exact ⟨1, 2, tails123, added123, attachments123, accepted123⟩
  · exact ⟨1, 0, tails124, added124, attachments124, accepted124⟩
  · exact ⟨2, 1, tails126, added126, attachments126, accepted126⟩
  · exact ⟨2, 0, tails127, added127, attachments127, accepted127⟩
  · exact ⟨0, 2, tails148, added148, attachments148, accepted148⟩
  · exact ⟨1, 2, tails149, added149, attachments149, accepted149⟩
  · exact ⟨1, 0, tails151, added151, attachments151, accepted151⟩
  · exact ⟨0, 1, tails152, added152, attachments152, accepted152⟩
  · exact ⟨2, 1, tails154, added154, attachments154, accepted154⟩
  · exact ⟨2, 0, tails155, added155, attachments155, accepted155⟩
def codes2 : List (Fin 1024) := [157, 158, 159, 164, 166, 167, 169, 171, 172, 173, 174, 181, 182, 183, 184, 185]
theorem witness2 (n : Fin 1024) (hn : n ∈ codes2) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes2, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails157, added157, attachments157, accepted157⟩
  · exact ⟨2, 0, tails158, added158, attachments158, accepted158⟩
  · exact ⟨2, 1, tails159, added159, attachments159, accepted159⟩
  · exact ⟨0, 1, tails164, added164, attachments164, accepted164⟩
  · exact ⟨2, 1, tails166, added166, attachments166, accepted166⟩
  · exact ⟨2, 0, tails167, added167, attachments167, accepted167⟩
  · exact ⟨1, 2, tails169, added169, attachments169, accepted169⟩
  · exact ⟨1, 0, tails171, added171, attachments171, accepted171⟩
  · exact ⟨2, 1, tails172, added172, attachments172, accepted172⟩
  · exact ⟨0, 2, tails173, added173, attachments173, accepted173⟩
  · exact ⟨0, 1, tails174, added174, attachments174, accepted174⟩
  · exact ⟨0, 1, tails181, added181, attachments181, accepted181⟩
  · exact ⟨0, 2, tails182, added182, attachments182, accepted182⟩
  · exact ⟨2, 1, tails183, added183, attachments183, accepted183⟩
  · exact ⟨2, 1, tails184, added184, attachments184, accepted184⟩
  · exact ⟨0, 2, tails185, added185, attachments185, accepted185⟩
def codes3 : List (Fin 1024) := [186, 188, 189, 191, 212, 213, 214, 217, 218, 219, 220, 222, 223, 229, 230, 231]
theorem witness3 (n : Fin 1024) (hn : n ∈ codes3) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes3, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails186, added186, attachments186, accepted186⟩
  · exact ⟨2, 0, tails188, added188, attachments188, accepted188⟩
  · exact ⟨1, 2, tails189, added189, attachments189, accepted189⟩
  · exact ⟨1, 0, tails191, added191, attachments191, accepted191⟩
  · exact ⟨1, 2, tails212, added212, attachments212, accepted212⟩
  · exact ⟨0, 2, tails213, added213, attachments213, accepted213⟩
  · exact ⟨0, 1, tails214, added214, attachments214, accepted214⟩
  · exact ⟨1, 0, tails217, added217, attachments217, accepted217⟩
  · exact ⟨2, 0, tails218, added218, attachments218, accepted218⟩
  · exact ⟨2, 1, tails219, added219, attachments219, accepted219⟩
  · exact ⟨1, 0, tails220, added220, attachments220, accepted220⟩
  · exact ⟨2, 1, tails222, added222, attachments222, accepted222⟩
  · exact ⟨2, 0, tails223, added223, attachments223, accepted223⟩
  · exact ⟨1, 0, tails229, added229, attachments229, accepted229⟩
  · exact ⟨2, 0, tails230, added230, attachments230, accepted230⟩
  · exact ⟨1, 2, tails231, added231, attachments231, accepted231⟩
def codes4 : List (Fin 1024) := [232, 233, 234, 236, 237, 239, 244, 246, 247, 248, 249, 251, 253, 254, 278, 279]
theorem witness4 (n : Fin 1024) (hn : n ∈ codes4) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes4, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, tails232, added232, attachments232, accepted232⟩
  · exact ⟨0, 2, tails233, added233, attachments233, accepted233⟩
  · exact ⟨0, 1, tails234, added234, attachments234, accepted234⟩
  · exact ⟨2, 0, tails236, added236, attachments236, accepted236⟩
  · exact ⟨1, 2, tails237, added237, attachments237, accepted237⟩
  · exact ⟨1, 0, tails239, added239, attachments239, accepted239⟩
  · exact ⟨1, 0, tails244, added244, attachments244, accepted244⟩
  · exact ⟨2, 1, tails246, added246, attachments246, accepted246⟩
  · exact ⟨2, 0, tails247, added247, attachments247, accepted247⟩
  · exact ⟨2, 0, tails248, added248, attachments248, accepted248⟩
  · exact ⟨1, 2, tails249, added249, attachments249, accepted249⟩
  · exact ⟨1, 0, tails251, added251, attachments251, accepted251⟩
  · exact ⟨0, 2, tails253, added253, attachments253, accepted253⟩
  · exact ⟨0, 1, tails254, added254, attachments254, accepted254⟩
  · exact ⟨2, 1, tails278, added278, attachments278, accepted278⟩
  · exact ⟨2, 0, tails279, added279, attachments279, accepted279⟩
def codes5 : List (Fin 1024) := [280, 281, 283, 284, 285, 286, 292, 293, 295, 296, 298, 299, 301, 302, 303, 308]
theorem witness5 (n : Fin 1024) (hn : n ∈ codes5) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes5, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, tails280, added280, attachments280, accepted280⟩
  · exact ⟨1, 2, tails281, added281, attachments281, accepted281⟩
  · exact ⟨1, 0, tails283, added283, attachments283, accepted283⟩
  · exact ⟨1, 2, tails284, added284, attachments284, accepted284⟩
  · exact ⟨0, 2, tails285, added285, attachments285, accepted285⟩
  · exact ⟨0, 1, tails286, added286, attachments286, accepted286⟩
  · exact ⟨0, 2, tails292, added292, attachments292, accepted292⟩
  · exact ⟨1, 2, tails293, added293, attachments293, accepted293⟩
  · exact ⟨1, 0, tails295, added295, attachments295, accepted295⟩
  · exact ⟨0, 1, tails296, added296, attachments296, accepted296⟩
  · exact ⟨2, 1, tails298, added298, attachments298, accepted298⟩
  · exact ⟨2, 0, tails299, added299, attachments299, accepted299⟩
  · exact ⟨1, 0, tails301, added301, attachments301, accepted301⟩
  · exact ⟨0, 2, tails302, added302, attachments302, accepted302⟩
  · exact ⟨1, 2, tails303, added303, attachments303, accepted303⟩
  · exact ⟨1, 2, tails308, added308, attachments308, accepted308⟩
def codes6 : List (Fin 1024) := [309, 310, 313, 314, 315, 316, 318, 319, 326, 327, 328, 329, 331, 332, 333, 334]
theorem witness6 (n : Fin 1024) (hn : n ∈ codes6) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes6, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, tails309, added309, attachments309, accepted309⟩
  · exact ⟨0, 1, tails310, added310, attachments310, accepted310⟩
  · exact ⟨0, 1, tails313, added313, attachments313, accepted313⟩
  · exact ⟨0, 2, tails314, added314, attachments314, accepted314⟩
  · exact ⟨1, 2, tails315, added315, attachments315, accepted315⟩
  · exact ⟨1, 0, tails316, added316, attachments316, accepted316⟩
  · exact ⟨2, 1, tails318, added318, attachments318, accepted318⟩
  · exact ⟨2, 0, tails319, added319, attachments319, accepted319⟩
  · exact ⟨2, 1, tails326, added326, attachments326, accepted326⟩
  · exact ⟨2, 0, tails327, added327, attachments327, accepted327⟩
  · exact ⟨0, 2, tails328, added328, attachments328, accepted328⟩
  · exact ⟨1, 2, tails329, added329, attachments329, accepted329⟩
  · exact ⟨1, 0, tails331, added331, attachments331, accepted331⟩
  · exact ⟨1, 2, tails332, added332, attachments332, accepted332⟩
  · exact ⟨0, 2, tails333, added333, attachments333, accepted333⟩
  · exact ⟨0, 1, tails334, added334, attachments334, accepted334⟩
def codes7 : List (Fin 1024) := [338, 339, 344, 348, 352, 353, 355, 356, 363, 364, 366, 367, 368, 369, 370, 372]
theorem witness7 (n : Fin 1024) (hn : n ∈ codes7) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes7, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, tails338, added338, attachments338, accepted338⟩
  · exact ⟨2, 0, tails339, added339, attachments339, accepted339⟩
  · exact ⟨1, 2, tails344, added344, attachments344, accepted344⟩
  · exact ⟨0, 2, tails348, added348, attachments348, accepted348⟩
  · exact ⟨0, 2, tails352, added352, attachments352, accepted352⟩
  · exact ⟨1, 2, tails353, added353, attachments353, accepted353⟩
  · exact ⟨1, 0, tails355, added355, attachments355, accepted355⟩
  · exact ⟨1, 2, tails356, added356, attachments356, accepted356⟩
  · exact ⟨2, 1, tails363, added363, attachments363, accepted363⟩
  · exact ⟨1, 0, tails364, added364, attachments364, accepted364⟩
  · exact ⟨2, 1, tails366, added366, attachments366, accepted366⟩
  · exact ⟨2, 0, tails367, added367, attachments367, accepted367⟩
  · exact ⟨1, 2, tails368, added368, attachments368, accepted368⟩
  · exact ⟨0, 2, tails369, added369, attachments369, accepted369⟩
  · exact ⟨0, 1, tails370, added370, attachments370, accepted370⟩
  · exact ⟨0, 2, tails372, added372, attachments372, accepted372⟩
def codes8 : List (Fin 1024) := [376, 378, 379, 382, 388, 389, 391, 392, 394, 395, 397, 398, 399, 400, 401, 403]
theorem witness8 (n : Fin 1024) (hn : n ∈ codes8) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes8, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails376, added376, attachments376, accepted376⟩
  · exact ⟨2, 1, tails378, added378, attachments378, accepted378⟩
  · exact ⟨2, 0, tails379, added379, attachments379, accepted379⟩
  · exact ⟨2, 0, tails382, added382, attachments382, accepted382⟩
  · exact ⟨0, 2, tails388, added388, attachments388, accepted388⟩
  · exact ⟨1, 2, tails389, added389, attachments389, accepted389⟩
  · exact ⟨1, 0, tails391, added391, attachments391, accepted391⟩
  · exact ⟨0, 1, tails392, added392, attachments392, accepted392⟩
  · exact ⟨2, 1, tails394, added394, attachments394, accepted394⟩
  · exact ⟨2, 0, tails395, added395, attachments395, accepted395⟩
  · exact ⟨1, 0, tails397, added397, attachments397, accepted397⟩
  · exact ⟨2, 0, tails398, added398, attachments398, accepted398⟩
  · exact ⟨2, 1, tails399, added399, attachments399, accepted399⟩
  · exact ⟨0, 2, tails400, added400, attachments400, accepted400⟩
  · exact ⟨1, 2, tails401, added401, attachments401, accepted401⟩
  · exact ⟨1, 0, tails403, added403, attachments403, accepted403⟩
def codes9 : List (Fin 1024) := [404, 411, 412, 414, 415, 416, 418, 419, 423, 424, 428, 429, 431, 433, 434, 435]
theorem witness9 (n : Fin 1024) (hn : n ∈ codes9) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes9, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails404, added404, attachments404, accepted404⟩
  · exact ⟨2, 1, tails411, added411, attachments411, accepted411⟩
  · exact ⟨1, 0, tails412, added412, attachments412, accepted412⟩
  · exact ⟨2, 1, tails414, added414, attachments414, accepted414⟩
  · exact ⟨2, 0, tails415, added415, attachments415, accepted415⟩
  · exact ⟨0, 1, tails416, added416, attachments416, accepted416⟩
  · exact ⟨2, 1, tails418, added418, attachments418, accepted418⟩
  · exact ⟨2, 0, tails419, added419, attachments419, accepted419⟩
  · exact ⟨1, 2, tails423, added423, attachments423, accepted423⟩
  · exact ⟨2, 1, tails424, added424, attachments424, accepted424⟩
  · exact ⟨2, 0, tails428, added428, attachments428, accepted428⟩
  · exact ⟨1, 2, tails429, added429, attachments429, accepted429⟩
  · exact ⟨1, 0, tails431, added431, attachments431, accepted431⟩
  · exact ⟨1, 0, tails433, added433, attachments433, accepted433⟩
  · exact ⟨2, 0, tails434, added434, attachments434, accepted434⟩
  · exact ⟨2, 1, tails435, added435, attachments435, accepted435⟩
def codes10 : List (Fin 1024) := [436, 438, 439, 440, 441, 443, 444, 445, 446, 452, 453, 454, 457, 458, 459, 460]
theorem witness10 (n : Fin 1024) (hn : n ∈ codes10) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes10, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, tails436, added436, attachments436, accepted436⟩
  · exact ⟨2, 1, tails438, added438, attachments438, accepted438⟩
  · exact ⟨2, 0, tails439, added439, attachments439, accepted439⟩
  · exact ⟨2, 0, tails440, added440, attachments440, accepted440⟩
  · exact ⟨1, 2, tails441, added441, attachments441, accepted441⟩
  · exact ⟨1, 0, tails443, added443, attachments443, accepted443⟩
  · exact ⟨2, 1, tails444, added444, attachments444, accepted444⟩
  · exact ⟨0, 2, tails445, added445, attachments445, accepted445⟩
  · exact ⟨0, 1, tails446, added446, attachments446, accepted446⟩
  · exact ⟨1, 2, tails452, added452, attachments452, accepted452⟩
  · exact ⟨0, 2, tails453, added453, attachments453, accepted453⟩
  · exact ⟨0, 1, tails454, added454, attachments454, accepted454⟩
  · exact ⟨0, 1, tails457, added457, attachments457, accepted457⟩
  · exact ⟨2, 0, tails458, added458, attachments458, accepted458⟩
  · exact ⟨2, 1, tails459, added459, attachments459, accepted459⟩
  · exact ⟨1, 0, tails460, added460, attachments460, accepted460⟩
def codes11 : List (Fin 1024) := [462, 463, 464, 465, 466, 468, 472, 474, 475, 478, 481, 482, 483, 484, 486, 487]
theorem witness11 (n : Fin 1024) (hn : n ∈ codes11) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes11, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, tails462, added462, attachments462, accepted462⟩
  · exact ⟨2, 0, tails463, added463, attachments463, accepted463⟩
  · exact ⟨1, 2, tails464, added464, attachments464, accepted464⟩
  · exact ⟨0, 2, tails465, added465, attachments465, accepted465⟩
  · exact ⟨0, 1, tails466, added466, attachments466, accepted466⟩
  · exact ⟨0, 2, tails468, added468, attachments468, accepted468⟩
  · exact ⟨0, 1, tails472, added472, attachments472, accepted472⟩
  · exact ⟨2, 1, tails474, added474, attachments474, accepted474⟩
  · exact ⟨2, 0, tails475, added475, attachments475, accepted475⟩
  · exact ⟨2, 0, tails478, added478, attachments478, accepted478⟩
  · exact ⟨0, 1, tails481, added481, attachments481, accepted481⟩
  · exact ⟨2, 0, tails482, added482, attachments482, accepted482⟩
  · exact ⟨2, 1, tails483, added483, attachments483, accepted483⟩
  · exact ⟨0, 1, tails484, added484, attachments484, accepted484⟩
  · exact ⟨2, 1, tails486, added486, attachments486, accepted486⟩
  · exact ⟨2, 0, tails487, added487, attachments487, accepted487⟩
def codes12 : List (Fin 1024) := [488, 489, 491, 492, 493, 494, 496, 498, 499, 502, 504, 505, 506, 508, 532, 533]
theorem witness12 (n : Fin 1024) (hn : n ∈ codes12) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes12, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, tails488, added488, attachments488, accepted488⟩
  · exact ⟨1, 2, tails489, added489, attachments489, accepted489⟩
  · exact ⟨1, 0, tails491, added491, attachments491, accepted491⟩
  · exact ⟨2, 1, tails492, added492, attachments492, accepted492⟩
  · exact ⟨0, 2, tails493, added493, attachments493, accepted493⟩
  · exact ⟨0, 1, tails494, added494, attachments494, accepted494⟩
  · exact ⟨1, 0, tails496, added496, attachments496, accepted496⟩
  · exact ⟨2, 1, tails498, added498, attachments498, accepted498⟩
  · exact ⟨2, 0, tails499, added499, attachments499, accepted499⟩
  · exact ⟨0, 2, tails502, added502, attachments502, accepted502⟩
  · exact ⟨2, 1, tails504, added504, attachments504, accepted504⟩
  · exact ⟨0, 2, tails505, added505, attachments505, accepted505⟩
  · exact ⟨0, 1, tails506, added506, attachments506, accepted506⟩
  · exact ⟨2, 0, tails508, added508, attachments508, accepted508⟩
  · exact ⟨0, 2, tails532, added532, attachments532, accepted532⟩
  · exact ⟨1, 2, tails533, added533, attachments533, accepted533⟩
def codes13 : List (Fin 1024) := [535, 536, 538, 539, 541, 542, 543, 548, 550, 551, 553, 555, 556, 557, 558, 565]
theorem witness13 (n : Fin 1024) (hn : n ∈ codes13) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes13, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, tails535, added535, attachments535, accepted535⟩
  · exact ⟨0, 1, tails536, added536, attachments536, accepted536⟩
  · exact ⟨2, 1, tails538, added538, attachments538, accepted538⟩
  · exact ⟨2, 0, tails539, added539, attachments539, accepted539⟩
  · exact ⟨0, 1, tails541, added541, attachments541, accepted541⟩
  · exact ⟨2, 0, tails542, added542, attachments542, accepted542⟩
  · exact ⟨2, 1, tails543, added543, attachments543, accepted543⟩
  · exact ⟨0, 1, tails548, added548, attachments548, accepted548⟩
  · exact ⟨2, 1, tails550, added550, attachments550, accepted550⟩
  · exact ⟨2, 0, tails551, added551, attachments551, accepted551⟩
  · exact ⟨1, 2, tails553, added553, attachments553, accepted553⟩
  · exact ⟨1, 0, tails555, added555, attachments555, accepted555⟩
  · exact ⟨2, 1, tails556, added556, attachments556, accepted556⟩
  · exact ⟨0, 2, tails557, added557, attachments557, accepted557⟩
  · exact ⟨0, 1, tails558, added558, attachments558, accepted558⟩
  · exact ⟨0, 1, tails565, added565, attachments565, accepted565⟩
def codes14 : List (Fin 1024) := [566, 567, 568, 569, 570, 572, 573, 575, 580, 581, 583, 584, 586, 587, 589, 590]
theorem witness14 (n : Fin 1024) (hn : n ∈ codes14) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes14, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, tails566, added566, attachments566, accepted566⟩
  · exact ⟨2, 1, tails567, added567, attachments567, accepted567⟩
  · exact ⟨2, 1, tails568, added568, attachments568, accepted568⟩
  · exact ⟨0, 2, tails569, added569, attachments569, accepted569⟩
  · exact ⟨0, 1, tails570, added570, attachments570, accepted570⟩
  · exact ⟨2, 0, tails572, added572, attachments572, accepted572⟩
  · exact ⟨1, 2, tails573, added573, attachments573, accepted573⟩
  · exact ⟨1, 0, tails575, added575, attachments575, accepted575⟩
  · exact ⟨0, 2, tails580, added580, attachments580, accepted580⟩
  · exact ⟨1, 2, tails581, added581, attachments581, accepted581⟩
  · exact ⟨1, 0, tails583, added583, attachments583, accepted583⟩
  · exact ⟨0, 1, tails584, added584, attachments584, accepted584⟩
  · exact ⟨2, 1, tails586, added586, attachments586, accepted586⟩
  · exact ⟨2, 0, tails587, added587, attachments587, accepted587⟩
  · exact ⟨1, 0, tails589, added589, attachments589, accepted589⟩
  · exact ⟨2, 0, tails590, added590, attachments590, accepted590⟩
def codes15 : List (Fin 1024) := [591, 592, 593, 595, 596, 603, 604, 606, 607, 608, 610, 611, 615, 616, 620, 621]
theorem witness15 (n : Fin 1024) (hn : n ∈ codes15) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes15, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails591, added591, attachments591, accepted591⟩
  · exact ⟨0, 2, tails592, added592, attachments592, accepted592⟩
  · exact ⟨1, 2, tails593, added593, attachments593, accepted593⟩
  · exact ⟨1, 0, tails595, added595, attachments595, accepted595⟩
  · exact ⟨1, 2, tails596, added596, attachments596, accepted596⟩
  · exact ⟨2, 1, tails603, added603, attachments603, accepted603⟩
  · exact ⟨1, 0, tails604, added604, attachments604, accepted604⟩
  · exact ⟨2, 1, tails606, added606, attachments606, accepted606⟩
  · exact ⟨2, 0, tails607, added607, attachments607, accepted607⟩
  · exact ⟨0, 1, tails608, added608, attachments608, accepted608⟩
  · exact ⟨2, 1, tails610, added610, attachments610, accepted610⟩
  · exact ⟨2, 0, tails611, added611, attachments611, accepted611⟩
  · exact ⟨1, 2, tails615, added615, attachments615, accepted615⟩
  · exact ⟨2, 1, tails616, added616, attachments616, accepted616⟩
  · exact ⟨2, 0, tails620, added620, attachments620, accepted620⟩
  · exact ⟨1, 2, tails621, added621, attachments621, accepted621⟩
def codes16 : List (Fin 1024) := [623, 625, 626, 627, 628, 630, 631, 632, 633, 635, 636, 637, 638, 644, 646, 647]
theorem witness16 (n : Fin 1024) (hn : n ∈ codes16) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes16, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, tails623, added623, attachments623, accepted623⟩
  · exact ⟨1, 0, tails625, added625, attachments625, accepted625⟩
  · exact ⟨2, 0, tails626, added626, attachments626, accepted626⟩
  · exact ⟨1, 2, tails627, added627, attachments627, accepted627⟩
  · exact ⟨1, 0, tails628, added628, attachments628, accepted628⟩
  · exact ⟨2, 1, tails630, added630, attachments630, accepted630⟩
  · exact ⟨2, 0, tails631, added631, attachments631, accepted631⟩
  · exact ⟨2, 0, tails632, added632, attachments632, accepted632⟩
  · exact ⟨1, 2, tails633, added633, attachments633, accepted633⟩
  · exact ⟨1, 0, tails635, added635, attachments635, accepted635⟩
  · exact ⟨1, 2, tails636, added636, attachments636, accepted636⟩
  · exact ⟨0, 2, tails637, added637, attachments637, accepted637⟩
  · exact ⟨0, 1, tails638, added638, attachments638, accepted638⟩
  · exact ⟨0, 1, tails644, added644, attachments644, accepted644⟩
  · exact ⟨2, 1, tails646, added646, attachments646, accepted646⟩
  · exact ⟨2, 0, tails647, added647, attachments647, accepted647⟩
def codes17 : List (Fin 1024) := [649, 651, 652, 653, 654, 656, 658, 659, 663, 664, 668, 669, 671, 673, 675, 676]
theorem witness17 (n : Fin 1024) (hn : n ∈ codes17) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes17, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails649, added649, attachments649, accepted649⟩
  · exact ⟨1, 0, tails651, added651, attachments651, accepted651⟩
  · exact ⟨2, 1, tails652, added652, attachments652, accepted652⟩
  · exact ⟨0, 2, tails653, added653, attachments653, accepted653⟩
  · exact ⟨0, 1, tails654, added654, attachments654, accepted654⟩
  · exact ⟨0, 1, tails656, added656, attachments656, accepted656⟩
  · exact ⟨2, 1, tails658, added658, attachments658, accepted658⟩
  · exact ⟨2, 0, tails659, added659, attachments659, accepted659⟩
  · exact ⟨1, 2, tails663, added663, attachments663, accepted663⟩
  · exact ⟨2, 1, tails664, added664, attachments664, accepted664⟩
  · exact ⟨2, 0, tails668, added668, attachments668, accepted668⟩
  · exact ⟨1, 2, tails669, added669, attachments669, accepted669⟩
  · exact ⟨1, 0, tails671, added671, attachments671, accepted671⟩
  · exact ⟨1, 2, tails673, added673, attachments673, accepted673⟩
  · exact ⟨1, 0, tails675, added675, attachments675, accepted675⟩
  · exact ⟨2, 1, tails676, added676, attachments676, accepted676⟩
def codes18 : List (Fin 1024) := [684, 688, 689, 690, 692, 693, 695, 696, 701, 709, 710, 711, 712, 713, 714, 716]
theorem witness18 (n : Fin 1024) (hn : n ∈ codes18) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes18, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails684, added684, attachments684, accepted684⟩
  · exact ⟨2, 1, tails688, added688, attachments688, accepted688⟩
  · exact ⟨0, 2, tails689, added689, attachments689, accepted689⟩
  · exact ⟨0, 1, tails690, added690, attachments690, accepted690⟩
  · exact ⟨0, 2, tails692, added692, attachments692, accepted692⟩
  · exact ⟨1, 2, tails693, added693, attachments693, accepted693⟩
  · exact ⟨1, 0, tails695, added695, attachments695, accepted695⟩
  · exact ⟨0, 1, tails696, added696, attachments696, accepted696⟩
  · exact ⟨1, 0, tails701, added701, attachments701, accepted701⟩
  · exact ⟨1, 0, tails709, added709, attachments709, accepted709⟩
  · exact ⟨0, 2, tails710, added710, attachments710, accepted710⟩
  · exact ⟨1, 2, tails711, added711, attachments711, accepted711⟩
  · exact ⟨2, 1, tails712, added712, attachments712, accepted712⟩
  · exact ⟨0, 2, tails713, added713, attachments713, accepted713⟩
  · exact ⟨0, 1, tails714, added714, attachments714, accepted714⟩
  · exact ⟨2, 0, tails716, added716, attachments716, accepted716⟩
def codes19 : List (Fin 1024) := [717, 719, 721, 722, 723, 724, 726, 727, 728, 729, 731, 732, 733, 734, 736, 737]
theorem witness19 (n : Fin 1024) (hn : n ∈ codes19) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes19, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails717, added717, attachments717, accepted717⟩
  · exact ⟨1, 0, tails719, added719, attachments719, accepted719⟩
  · exact ⟨1, 0, tails721, added721, attachments721, accepted721⟩
  · exact ⟨0, 2, tails722, added722, attachments722, accepted722⟩
  · exact ⟨1, 2, tails723, added723, attachments723, accepted723⟩
  · exact ⟨1, 0, tails724, added724, attachments724, accepted724⟩
  · exact ⟨2, 1, tails726, added726, attachments726, accepted726⟩
  · exact ⟨2, 0, tails727, added727, attachments727, accepted727⟩
  · exact ⟨0, 2, tails728, added728, attachments728, accepted728⟩
  · exact ⟨1, 2, tails729, added729, attachments729, accepted729⟩
  · exact ⟨1, 0, tails731, added731, attachments731, accepted731⟩
  · exact ⟨1, 2, tails732, added732, attachments732, accepted732⟩
  · exact ⟨0, 2, tails733, added733, attachments733, accepted733⟩
  · exact ⟨0, 1, tails734, added734, attachments734, accepted734⟩
  · exact ⟨2, 1, tails736, added736, attachments736, accepted736⟩
  · exact ⟨0, 2, tails737, added737, attachments737, accepted737⟩
def codes20 : List (Fin 1024) := [738, 740, 741, 743, 744, 749, 752, 753, 755, 756, 757, 758, 761, 764, 788, 789]
theorem witness20 (n : Fin 1024) (hn : n ∈ codes20) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes20, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails738, added738, attachments738, accepted738⟩
  · exact ⟨0, 2, tails740, added740, attachments740, accepted740⟩
  · exact ⟨1, 2, tails741, added741, attachments741, accepted741⟩
  · exact ⟨1, 0, tails743, added743, attachments743, accepted743⟩
  · exact ⟨0, 1, tails744, added744, attachments744, accepted744⟩
  · exact ⟨1, 0, tails749, added749, attachments749, accepted749⟩
  · exact ⟨2, 0, tails752, added752, attachments752, accepted752⟩
  · exact ⟨1, 2, tails753, added753, attachments753, accepted753⟩
  · exact ⟨1, 0, tails755, added755, attachments755, accepted755⟩
  · exact ⟨1, 2, tails756, added756, attachments756, accepted756⟩
  · exact ⟨0, 2, tails757, added757, attachments757, accepted757⟩
  · exact ⟨0, 1, tails758, added758, attachments758, accepted758⟩
  · exact ⟨0, 1, tails761, added761, attachments761, accepted761⟩
  · exact ⟨1, 0, tails764, added764, attachments764, accepted764⟩
  · exact ⟨1, 2, tails788, added788, attachments788, accepted788⟩
  · exact ⟨0, 2, tails789, added789, attachments789, accepted789⟩
def codes21 : List (Fin 1024) := [790, 793, 794, 795, 796, 798, 799, 805, 806, 807, 808, 809, 810, 812, 813, 815]
theorem witness21 (n : Fin 1024) (hn : n ∈ codes21) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes21, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails790, added790, attachments790, accepted790⟩
  · exact ⟨1, 0, tails793, added793, attachments793, accepted793⟩
  · exact ⟨2, 0, tails794, added794, attachments794, accepted794⟩
  · exact ⟨2, 1, tails795, added795, attachments795, accepted795⟩
  · exact ⟨1, 0, tails796, added796, attachments796, accepted796⟩
  · exact ⟨2, 1, tails798, added798, attachments798, accepted798⟩
  · exact ⟨2, 0, tails799, added799, attachments799, accepted799⟩
  · exact ⟨1, 0, tails805, added805, attachments805, accepted805⟩
  · exact ⟨2, 0, tails806, added806, attachments806, accepted806⟩
  · exact ⟨1, 2, tails807, added807, attachments807, accepted807⟩
  · exact ⟨2, 1, tails808, added808, attachments808, accepted808⟩
  · exact ⟨0, 2, tails809, added809, attachments809, accepted809⟩
  · exact ⟨0, 1, tails810, added810, attachments810, accepted810⟩
  · exact ⟨2, 0, tails812, added812, attachments812, accepted812⟩
  · exact ⟨1, 2, tails813, added813, attachments813, accepted813⟩
  · exact ⟨1, 0, tails815, added815, attachments815, accepted815⟩
def codes22 : List (Fin 1024) := [820, 822, 823, 824, 825, 827, 829, 830, 836, 837, 838, 841, 842, 843, 844, 846]
theorem witness22 (n : Fin 1024) (hn : n ∈ codes22) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes22, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 0, tails820, added820, attachments820, accepted820⟩
  · exact ⟨2, 1, tails822, added822, attachments822, accepted822⟩
  · exact ⟨2, 0, tails823, added823, attachments823, accepted823⟩
  · exact ⟨2, 0, tails824, added824, attachments824, accepted824⟩
  · exact ⟨1, 2, tails825, added825, attachments825, accepted825⟩
  · exact ⟨1, 0, tails827, added827, attachments827, accepted827⟩
  · exact ⟨0, 2, tails829, added829, attachments829, accepted829⟩
  · exact ⟨0, 1, tails830, added830, attachments830, accepted830⟩
  · exact ⟨1, 2, tails836, added836, attachments836, accepted836⟩
  · exact ⟨0, 2, tails837, added837, attachments837, accepted837⟩
  · exact ⟨0, 1, tails838, added838, attachments838, accepted838⟩
  · exact ⟨0, 1, tails841, added841, attachments841, accepted841⟩
  · exact ⟨0, 2, tails842, added842, attachments842, accepted842⟩
  · exact ⟨2, 1, tails843, added843, attachments843, accepted843⟩
  · exact ⟨1, 0, tails844, added844, attachments844, accepted844⟩
  · exact ⟨2, 1, tails846, added846, attachments846, accepted846⟩
def codes23 : List (Fin 1024) := [847, 848, 849, 850, 852, 856, 858, 859, 862, 865, 866, 867, 868, 870, 871, 872]
theorem witness23 (n : Fin 1024) (hn : n ∈ codes23) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes23, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 0, tails847, added847, attachments847, accepted847⟩
  · exact ⟨1, 2, tails848, added848, attachments848, accepted848⟩
  · exact ⟨0, 2, tails849, added849, attachments849, accepted849⟩
  · exact ⟨0, 1, tails850, added850, attachments850, accepted850⟩
  · exact ⟨0, 2, tails852, added852, attachments852, accepted852⟩
  · exact ⟨0, 1, tails856, added856, attachments856, accepted856⟩
  · exact ⟨2, 1, tails858, added858, attachments858, accepted858⟩
  · exact ⟨2, 0, tails859, added859, attachments859, accepted859⟩
  · exact ⟨2, 0, tails862, added862, attachments862, accepted862⟩
  · exact ⟨0, 1, tails865, added865, attachments865, accepted865⟩
  · exact ⟨0, 2, tails866, added866, attachments866, accepted866⟩
  · exact ⟨2, 1, tails867, added867, attachments867, accepted867⟩
  · exact ⟨0, 1, tails868, added868, attachments868, accepted868⟩
  · exact ⟨2, 1, tails870, added870, attachments870, accepted870⟩
  · exact ⟨2, 0, tails871, added871, attachments871, accepted871⟩
  · exact ⟨0, 2, tails872, added872, attachments872, accepted872⟩
def codes24 : List (Fin 1024) := [873, 875, 876, 877, 878, 880, 882, 883, 886, 888, 889, 890, 892, 901, 902, 903]
theorem witness24 (n : Fin 1024) (hn : n ∈ codes24) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes24, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨1, 2, tails873, added873, attachments873, accepted873⟩
  · exact ⟨1, 0, tails875, added875, attachments875, accepted875⟩
  · exact ⟨2, 1, tails876, added876, attachments876, accepted876⟩
  · exact ⟨0, 2, tails877, added877, attachments877, accepted877⟩
  · exact ⟨0, 1, tails878, added878, attachments878, accepted878⟩
  · exact ⟨1, 0, tails880, added880, attachments880, accepted880⟩
  · exact ⟨2, 1, tails882, added882, attachments882, accepted882⟩
  · exact ⟨2, 0, tails883, added883, attachments883, accepted883⟩
  · exact ⟨0, 2, tails886, added886, attachments886, accepted886⟩
  · exact ⟨2, 1, tails888, added888, attachments888, accepted888⟩
  · exact ⟨0, 2, tails889, added889, attachments889, accepted889⟩
  · exact ⟨0, 1, tails890, added890, attachments890, accepted890⟩
  · exact ⟨2, 0, tails892, added892, attachments892, accepted892⟩
  · exact ⟨0, 1, tails901, added901, attachments901, accepted901⟩
  · exact ⟨0, 2, tails902, added902, attachments902, accepted902⟩
  · exact ⟨1, 2, tails903, added903, attachments903, accepted903⟩
def codes25 : List (Fin 1024) := [904, 905, 906, 908, 909, 911, 913, 914, 915, 916, 918, 919, 920, 921, 923, 924]
theorem witness25 (n : Fin 1024) (hn : n ∈ codes25) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes25, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨2, 1, tails904, added904, attachments904, accepted904⟩
  · exact ⟨0, 2, tails905, added905, attachments905, accepted905⟩
  · exact ⟨0, 1, tails906, added906, attachments906, accepted906⟩
  · exact ⟨2, 0, tails908, added908, attachments908, accepted908⟩
  · exact ⟨1, 2, tails909, added909, attachments909, accepted909⟩
  · exact ⟨1, 0, tails911, added911, attachments911, accepted911⟩
  · exact ⟨0, 1, tails913, added913, attachments913, accepted913⟩
  · exact ⟨0, 2, tails914, added914, attachments914, accepted914⟩
  · exact ⟨1, 2, tails915, added915, attachments915, accepted915⟩
  · exact ⟨0, 1, tails916, added916, attachments916, accepted916⟩
  · exact ⟨2, 1, tails918, added918, attachments918, accepted918⟩
  · exact ⟨2, 0, tails919, added919, attachments919, accepted919⟩
  · exact ⟨0, 2, tails920, added920, attachments920, accepted920⟩
  · exact ⟨1, 2, tails921, added921, attachments921, accepted921⟩
  · exact ⟨1, 0, tails923, added923, attachments923, accepted923⟩
  · exact ⟨1, 2, tails924, added924, attachments924, accepted924⟩
def codes26 : List (Fin 1024) := [925, 926, 928, 929, 930, 932, 933, 935, 936, 941, 944, 945, 947, 948, 949, 950]
theorem witness26 (n : Fin 1024) (hn : n ∈ codes26) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes26, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 2, tails925, added925, attachments925, accepted925⟩
  · exact ⟨0, 1, tails926, added926, attachments926, accepted926⟩
  · exact ⟨2, 1, tails928, added928, attachments928, accepted928⟩
  · exact ⟨0, 2, tails929, added929, attachments929, accepted929⟩
  · exact ⟨0, 1, tails930, added930, attachments930, accepted930⟩
  · exact ⟨0, 2, tails932, added932, attachments932, accepted932⟩
  · exact ⟨1, 2, tails933, added933, attachments933, accepted933⟩
  · exact ⟨1, 0, tails935, added935, attachments935, accepted935⟩
  · exact ⟨0, 1, tails936, added936, attachments936, accepted936⟩
  · exact ⟨1, 0, tails941, added941, attachments941, accepted941⟩
  · exact ⟨2, 0, tails944, added944, attachments944, accepted944⟩
  · exact ⟨1, 2, tails945, added945, attachments945, accepted945⟩
  · exact ⟨1, 0, tails947, added947, attachments947, accepted947⟩
  · exact ⟨1, 2, tails948, added948, attachments948, accepted948⟩
  · exact ⟨0, 2, tails949, added949, attachments949, accepted949⟩
  · exact ⟨0, 1, tails950, added950, attachments950, accepted950⟩
def codes27 : List (Fin 1024) := [953, 956, 964, 966, 967, 968, 969, 971, 973, 974, 976, 978, 979, 982, 984, 985]
theorem witness27 (n : Fin 1024) (hn : n ∈ codes27) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes27, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails953, added953, attachments953, accepted953⟩
  · exact ⟨1, 0, tails956, added956, attachments956, accepted956⟩
  · exact ⟨1, 0, tails964, added964, attachments964, accepted964⟩
  · exact ⟨2, 1, tails966, added966, attachments966, accepted966⟩
  · exact ⟨2, 0, tails967, added967, attachments967, accepted967⟩
  · exact ⟨2, 0, tails968, added968, attachments968, accepted968⟩
  · exact ⟨1, 2, tails969, added969, attachments969, accepted969⟩
  · exact ⟨1, 0, tails971, added971, attachments971, accepted971⟩
  · exact ⟨0, 2, tails973, added973, attachments973, accepted973⟩
  · exact ⟨0, 1, tails974, added974, attachments974, accepted974⟩
  · exact ⟨1, 0, tails976, added976, attachments976, accepted976⟩
  · exact ⟨2, 1, tails978, added978, attachments978, accepted978⟩
  · exact ⟨2, 0, tails979, added979, attachments979, accepted979⟩
  · exact ⟨0, 2, tails982, added982, attachments982, accepted982⟩
  · exact ⟨2, 1, tails984, added984, attachments984, accepted984⟩
  · exact ⟨0, 2, tails985, added985, attachments985, accepted985⟩
def codes28 : List (Fin 1024) := [986, 988, 992, 993, 995, 996, 997, 998, 1001, 1004, 1009, 1010, 1012, 1016]
theorem witness28 (n : Fin 1024) (hn : n ∈ codes28) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  simp only [codes28, List.mem_cons, List.not_mem_nil, or_false] at hn
  rcases hn with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact ⟨0, 1, tails986, added986, attachments986, accepted986⟩
  · exact ⟨2, 0, tails988, added988, attachments988, accepted988⟩
  · exact ⟨2, 0, tails992, added992, attachments992, accepted992⟩
  · exact ⟨1, 2, tails993, added993, attachments993, accepted993⟩
  · exact ⟨1, 0, tails995, added995, attachments995, accepted995⟩
  · exact ⟨1, 2, tails996, added996, attachments996, accepted996⟩
  · exact ⟨0, 2, tails997, added997, attachments997, accepted997⟩
  · exact ⟨0, 1, tails998, added998, attachments998, accepted998⟩
  · exact ⟨0, 1, tails1001, added1001, attachments1001, accepted1001⟩
  · exact ⟨1, 0, tails1004, added1004, attachments1004, accepted1004⟩
  · exact ⟨0, 2, tails1009, added1009, attachments1009, accepted1009⟩
  · exact ⟨0, 1, tails1010, added1010, attachments1010, accepted1010⟩
  · exact ⟨2, 0, tails1012, added1012, attachments1012, accepted1012⟩
  · exact ⟨1, 0, tails1016, added1016, attachments1016, accepted1016⟩
private theorem append_witness {l r : List (Fin 1024)}
    (hl : ∀ n ∈ l, ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a)
    (hr : ∀ n ∈ r, ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a) :
    ∀ n ∈ l ++ r, ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  intro n hn
  rcases List.mem_append.mp hn with h | h
  · exact hl n h
  · exact hr n h
/-- Every cheap-domain code supplies an accepted one-credit interface. -/
theorem cheap_witness (n : Fin 1024) (hn : n ∈ cheapCodes) :
    ∃ p q tails added a, CheapOriginalAccepted (decode n) p q tails added a := by
  exact (append_witness witness0 (append_witness witness1 (append_witness witness2 (append_witness witness3 (append_witness witness4 (append_witness witness5 (append_witness witness6 (append_witness witness7 (append_witness witness8 (append_witness witness9 (append_witness witness10 (append_witness witness11 (append_witness witness12 (append_witness witness13 (append_witness witness14 (append_witness witness15 (append_witness witness16 (append_witness witness17 (append_witness witness18 (append_witness witness19 (append_witness witness20 (append_witness witness21 (append_witness witness22 (append_witness witness23 (append_witness witness24 (append_witness witness25 (append_witness witness26 (append_witness witness27 witness28)))))))))))))))))))))))))))) n hn
end Gallai.Certificate.ThreeAnchor.CheapOrbits
