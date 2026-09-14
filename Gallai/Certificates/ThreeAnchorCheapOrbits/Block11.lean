/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails820 : List (List Vertex) := [[6, 5, 1, 2, 0, 3, 4, 7], [7, 2, 6, 1, 0, 4]]
def added820 : List (List Vertex) := [[4, 6]]
def attachments820 : Fin tails820.length → Fin 3 := ![1, 2]
theorem accepted820 : CheapOriginalAccepted (decode 820) 1 0
    tails820 added820 attachments820 := by decide

def tails822 : List (List Vertex) := [[7, 4, 3, 0, 2, 6, 1, 5], [5, 0, 1, 2, 7, 6, 4]]
def added822 : List (List Vertex) := [[4, 0, 7]]
def attachments822 : Fin tails822.length → Fin 3 := ![2, 0]
theorem accepted822 : CheapOriginalAccepted (decode 822) 2 1
    tails822 added822 attachments822 := by decide

def tails823 : List (List Vertex) := [[6, 0, 2, 1, 5, 7, 4, 3], [7, 2, 6, 4, 0, 3]]
def added823 : List (List Vertex) := [[6, 1, 0, 7]]
def attachments823 : Fin tails823.length → Fin 3 := ![1, 2]
theorem accepted823 : CheapOriginalAccepted (decode 823) 2 0
    tails823 added823 attachments823 := by decide

def tails824 : List (List Vertex) := [[7, 5, 1, 2, 0, 3, 4, 6], [6, 2, 7, 1, 0, 4]]
def added824 : List (List Vertex) := [[4, 7]]
def attachments824 : Fin tails824.length → Fin 3 := ![2, 1]
theorem accepted824 : CheapOriginalAccepted (decode 824) 2 0
    tails824 added824 attachments824 := by decide

def tails825 : List (List Vertex) := [[6, 4, 3, 0, 2, 7, 1, 5], [5, 0, 1, 2, 6, 7, 4]]
def added825 : List (List Vertex) := [[4, 0, 6]]
def attachments825 : Fin tails825.length → Fin 3 := ![1, 0]
theorem accepted825 : CheapOriginalAccepted (decode 825) 1 2
    tails825 added825 attachments825 := by decide

def tails827 : List (List Vertex) := [[7, 0, 2, 1, 5, 6, 4, 3], [6, 2, 7, 4, 0, 3]]
def added827 : List (List Vertex) := [[7, 1, 0, 6]]
def attachments827 : Fin tails827.length → Fin 3 := ![2, 1]
theorem accepted827 : CheapOriginalAccepted (decode 827) 1 0
    tails827 added827 attachments827 := by decide

def tails829 : List (List Vertex) := [[6, 4, 3, 0, 1, 2, 7, 5], [5, 0, 2, 6, 1, 7, 4]]
def added829 : List (List Vertex) := [[4, 0, 6]]
def attachments829 : Fin tails829.length → Fin 3 := ![1, 0]
theorem accepted829 : CheapOriginalAccepted (decode 829) 0 2
    tails829 added829 attachments829 := by decide

def tails830 : List (List Vertex) := [[7, 4, 3, 0, 1, 2, 6, 5], [5, 0, 2, 7, 1, 6, 4]]
def added830 : List (List Vertex) := [[4, 0, 7]]
def attachments830 : Fin tails830.length → Fin 3 := ![2, 0]
theorem accepted830 : CheapOriginalAccepted (decode 830) 0 1
    tails830 added830 attachments830 := by decide

def tails836 : List (List Vertex) := [[6, 7, 4, 3, 0, 2, 1, 5], [5, 3, 6, 4, 0, 1]]
def added836 : List (List Vertex) := [[1, 6]]
def attachments836 : Fin tails836.length → Fin 3 := ![1, 0]
theorem accepted836 : CheapOriginalAccepted (decode 836) 1 2
    tails836 added836 attachments836 := by decide

def tails837 : List (List Vertex) := [[6, 0, 3, 4, 7, 5, 1, 2], [5, 3, 6, 1, 0, 2]]
def added837 : List (List Vertex) := [[6, 4, 0, 5]]
def attachments837 : Fin tails837.length → Fin 3 := ![1, 0]
theorem accepted837 : CheapOriginalAccepted (decode 837) 0 2
    tails837 added837 attachments837 := by decide

def tails838 : List (List Vertex) := [[5, 1, 2, 0, 3, 6, 4, 7], [7, 0, 4, 3, 5, 6, 1]]
def added838 : List (List Vertex) := [[1, 0, 5]]
def attachments838 : Fin tails838.length → Fin 3 := ![0, 2]
theorem accepted838 : CheapOriginalAccepted (decode 838) 0 1
    tails838 added838 attachments838 := by decide

def tails841 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 1, 2], [6, 5, 1, 0, 2]]
def added841 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments841 : Fin tails841.length → Fin 3 := ![0, 1]
theorem accepted841 : CheapOriginalAccepted (decode 841) 0 1
    tails841 added841 attachments841 := by decide

def tails842 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 1, 2], [7, 5, 3, 4, 0, 2]]
def added842 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments842 : Fin tails842.length → Fin 3 := ![0, 2]
theorem accepted842 : CheapOriginalAccepted (decode 842) 0 2
    tails842 added842 attachments842 := by decide

def tails843 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 1, 2], [6, 7, 1, 0, 2]]
def added843 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments843 : Fin tails843.length → Fin 3 := ![2, 1]
theorem accepted843 : CheapOriginalAccepted (decode 843) 2 1
    tails843 added843 attachments843 := by decide

def tails844 : List (List Vertex) := [[6, 5, 3, 4, 0, 2, 1, 7], [7, 4, 6, 3, 0, 1]]
def added844 : List (List Vertex) := [[1, 6]]
def attachments844 : Fin tails844.length → Fin 3 := ![1, 2]
theorem accepted844 : CheapOriginalAccepted (decode 844) 1 0
    tails844 added844 attachments844 := by decide

def tails846 : List (List Vertex) := [[7, 1, 2, 0, 4, 6, 3, 5], [5, 0, 3, 4, 7, 6, 1]]
def added846 : List (List Vertex) := [[1, 0, 7]]
def attachments846 : Fin tails846.length → Fin 3 := ![2, 0]
theorem accepted846 : CheapOriginalAccepted (decode 846) 2 1
    tails846 added846 attachments846 := by decide

def tails847 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 1, 2], [7, 4, 6, 1, 0, 2]]
def added847 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments847 : Fin tails847.length → Fin 3 := ![1, 2]
theorem accepted847 : CheapOriginalAccepted (decode 847) 2 0
    tails847 added847 attachments847 := by decide

def tails848 : List (List Vertex) := [[6, 7, 4, 3, 0, 1, 2, 5], [5, 3, 6, 4, 0, 2]]
def added848 : List (List Vertex) := [[2, 6]]
def attachments848 : Fin tails848.length → Fin 3 := ![1, 0]
theorem accepted848 : CheapOriginalAccepted (decode 848) 1 2
    tails848 added848 attachments848 := by decide

def tails849 : List (List Vertex) := [[6, 0, 3, 4, 7, 5, 2, 1], [5, 3, 6, 2, 0, 1]]
def added849 : List (List Vertex) := [[6, 4, 0, 5]]
def attachments849 : Fin tails849.length → Fin 3 := ![1, 0]
theorem accepted849 : CheapOriginalAccepted (decode 849) 0 2
    tails849 added849 attachments849 := by decide

def tails850 : List (List Vertex) := [[5, 2, 1, 0, 3, 6, 4, 7], [7, 0, 4, 3, 5, 6, 2]]
def added850 : List (List Vertex) := [[2, 0, 5]]
def attachments850 : Fin tails850.length → Fin 3 := ![0, 2]
theorem accepted850 : CheapOriginalAccepted (decode 850) 0 1
    tails850 added850 attachments850 := by decide

def tails852 : List (List Vertex) := [[6, 3, 0, 4, 7, 5, 2, 1], [5, 3, 4, 6, 2, 0, 1]]
def added852 : List (List Vertex) := [[6, 1, 5]]
def attachments852 : Fin tails852.length → Fin 3 := ![1, 0]
theorem accepted852 : CheapOriginalAccepted (decode 852) 0 2
    tails852 added852 attachments852 := by decide

def tails856 : List (List Vertex) := [[5, 6, 3, 0, 4, 7, 1, 2], [6, 4, 3, 5, 1, 0, 2]]
def added856 : List (List Vertex) := [[5, 2, 6]]
def attachments856 : Fin tails856.length → Fin 3 := ![0, 1]
theorem accepted856 : CheapOriginalAccepted (decode 856) 0 1
    tails856 added856 attachments856 := by decide

def tails858 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 2, 1], [7, 6, 4, 0, 2, 5, 1]]
def added858 : List (List Vertex) := [[5, 3, 0, 1, 7]]
def attachments858 : Fin tails858.length → Fin 3 := ![0, 2]
theorem accepted858 : CheapOriginalAccepted (decode 858) 2 1
    tails858 added858 attachments858 := by decide

def tails859 : List (List Vertex) := [[6, 0, 7, 1, 2, 5, 3, 4], [7, 5, 1, 0, 3, 6, 4]]
def added859 : List (List Vertex) := [[6, 2, 0, 4, 7]]
def attachments859 : Fin tails859.length → Fin 3 := ![1, 2]
theorem accepted859 : CheapOriginalAccepted (decode 859) 2 0
    tails859 added859 attachments859 := by decide

def tails862 : List (List Vertex) := [[7, 0, 4, 6, 3, 5, 2, 1], [5, 7, 4, 3, 0, 2, 6, 1]]
def added862 : List (List Vertex) := [[7, 1, 0, 5]]
def attachments862 : Fin tails862.length → Fin 3 := ![2, 0]
theorem accepted862 : CheapOriginalAccepted (decode 862) 2 0
    tails862 added862 attachments862 := by decide

def tails865 : List (List Vertex) := [[5, 0, 6, 3, 4, 7, 2, 1], [6, 5, 2, 0, 1]]
def added865 : List (List Vertex) := [[5, 3, 0, 4, 6]]
def attachments865 : Fin tails865.length → Fin 3 := ![0, 1]
theorem accepted865 : CheapOriginalAccepted (decode 865) 0 1
    tails865 added865 attachments865 := by decide

def tails866 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 2, 1], [7, 5, 3, 4, 0, 1]]
def added866 : List (List Vertex) := [[5, 2, 0, 7]]
def attachments866 : Fin tails866.length → Fin 3 := ![0, 2]
theorem accepted866 : CheapOriginalAccepted (decode 866) 0 2
    tails866 added866 attachments866 := by decide

def tails867 : List (List Vertex) := [[7, 0, 6, 4, 3, 5, 2, 1], [6, 7, 2, 0, 1]]
def added867 : List (List Vertex) := [[7, 4, 0, 3, 6]]
def attachments867 : Fin tails867.length → Fin 3 := ![2, 1]
theorem accepted867 : CheapOriginalAccepted (decode 867) 2 1
    tails867 added867 attachments867 := by decide

def tails868 : List (List Vertex) := [[5, 6, 3, 0, 4, 7, 2, 1], [6, 4, 3, 5, 2, 0, 1]]
def added868 : List (List Vertex) := [[5, 1, 6]]
def attachments868 : Fin tails868.length → Fin 3 := ![0, 1]
theorem accepted868 : CheapOriginalAccepted (decode 868) 0 1
    tails868 added868 attachments868 := by decide

def tails870 : List (List Vertex) := [[5, 0, 7, 4, 3, 6, 1, 2], [7, 6, 4, 0, 1, 5, 2]]
def added870 : List (List Vertex) := [[5, 3, 0, 2, 7]]
def attachments870 : Fin tails870.length → Fin 3 := ![0, 2]
theorem accepted870 : CheapOriginalAccepted (decode 870) 2 1
    tails870 added870 attachments870 := by decide

def tails871 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 5, 2, 0, 3, 6, 4]]
def added871 : List (List Vertex) := [[6, 1, 0, 4, 7]]
def attachments871 : Fin tails871.length → Fin 3 := ![1, 2]
theorem accepted871 : CheapOriginalAccepted (decode 871) 2 0
    tails871 added871 attachments871 := by decide

def tails872 : List (List Vertex) := [[5, 7, 4, 6, 3, 0, 2, 1], [7, 2, 5, 3, 4, 0, 1]]
def added872 : List (List Vertex) := [[5, 1, 7]]
def attachments872 : Fin tails872.length → Fin 3 := ![0, 2]
theorem accepted872 : CheapOriginalAccepted (decode 872) 0 2
    tails872 added872 attachments872 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
