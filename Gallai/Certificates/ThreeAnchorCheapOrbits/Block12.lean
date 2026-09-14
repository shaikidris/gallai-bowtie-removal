/- Generated from source SHA-256 2fd2d64dc139a192f5a06434e43534362ba6b3906e0d1bb22ce25e9649a92dda. -/
import Gallai.Certificates.ThreeAnchorCheapOriginal
import Gallai.Certificates.ThreeAnchorSyntheticOrbits
import Gallai.Certificates.ThreeAnchorCheapOrbits.Core

namespace Gallai.Certificate.ThreeAnchor.CheapOrbits
open Orbits
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000

def tails873 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 1, 0, 2, 7, 6, 3]]
def added873 : List (List Vertex) := [[6, 4, 0, 3, 5]]
def attachments873 : Fin tails873.length → Fin 3 := ![1, 0]
theorem accepted873 : CheapOriginalAccepted (decode 873) 1 2
    tails873 added873 attachments873 := by decide

def tails875 : List (List Vertex) := [[6, 0, 7, 2, 1, 5, 3, 4], [7, 1, 0, 2, 5, 6, 4]]
def added875 : List (List Vertex) := [[6, 3, 0, 4, 7]]
def attachments875 : Fin tails875.length → Fin 3 := ![1, 2]
theorem accepted875 : CheapOriginalAccepted (decode 875) 1 0
    tails875 added875 attachments875 := by decide

def tails876 : List (List Vertex) := [[7, 6, 4, 0, 3, 5, 2, 1], [6, 3, 4, 7, 2, 0, 1]]
def added876 : List (List Vertex) := [[7, 1, 6]]
def attachments876 : Fin tails876.length → Fin 3 := ![2, 1]
theorem accepted876 : CheapOriginalAccepted (decode 876) 2 1
    tails876 added876 attachments876 := by decide

def tails877 : List (List Vertex) := [[6, 0, 5, 2, 1, 7, 4, 3], [5, 7, 2, 0, 4, 6, 3]]
def added877 : List (List Vertex) := [[6, 1, 0, 3, 5]]
def attachments877 : Fin tails877.length → Fin 3 := ![1, 0]
theorem accepted877 : CheapOriginalAccepted (decode 877) 0 2
    tails877 added877 attachments877 := by decide

def tails878 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 1, 2], [5, 6, 3, 0, 1, 7, 2]]
def added878 : List (List Vertex) := [[7, 4, 0, 2, 5]]
def attachments878 : Fin tails878.length → Fin 3 := ![2, 0]
theorem accepted878 : CheapOriginalAccepted (decode 878) 0 1
    tails878 added878 attachments878 := by decide

def tails880 : List (List Vertex) := [[6, 5, 3, 4, 0, 1, 2, 7], [7, 4, 6, 3, 0, 2]]
def added880 : List (List Vertex) := [[2, 6]]
def attachments880 : Fin tails880.length → Fin 3 := ![1, 2]
theorem accepted880 : CheapOriginalAccepted (decode 880) 1 0
    tails880 added880 attachments880 := by decide

def tails882 : List (List Vertex) := [[7, 2, 1, 0, 4, 6, 3, 5], [5, 0, 3, 4, 7, 6, 2]]
def added882 : List (List Vertex) := [[2, 0, 7]]
def attachments882 : Fin tails882.length → Fin 3 := ![2, 0]
theorem accepted882 : CheapOriginalAccepted (decode 882) 2 1
    tails882 added882 attachments882 := by decide

def tails883 : List (List Vertex) := [[6, 0, 4, 3, 5, 7, 2, 1], [7, 4, 6, 2, 0, 1]]
def added883 : List (List Vertex) := [[6, 3, 0, 7]]
def attachments883 : Fin tails883.length → Fin 3 := ![1, 2]
theorem accepted883 : CheapOriginalAccepted (decode 883) 2 0
    tails883 added883 attachments883 := by decide

def tails886 : List (List Vertex) := [[5, 0, 3, 6, 4, 7, 2, 1], [7, 5, 3, 4, 0, 2, 6, 1]]
def added886 : List (List Vertex) := [[5, 1, 0, 7]]
def attachments886 : Fin tails886.length → Fin 3 := ![0, 2]
theorem accepted886 : CheapOriginalAccepted (decode 886) 0 2
    tails886 added886 attachments886 := by decide

def tails888 : List (List Vertex) := [[7, 6, 4, 0, 3, 5, 1, 2], [6, 3, 4, 7, 1, 0, 2]]
def added888 : List (List Vertex) := [[7, 2, 6]]
def attachments888 : Fin tails888.length → Fin 3 := ![2, 1]
theorem accepted888 : CheapOriginalAccepted (decode 888) 2 1
    tails888 added888 attachments888 := by decide

def tails889 : List (List Vertex) := [[6, 0, 5, 1, 2, 7, 4, 3], [5, 7, 1, 0, 4, 6, 3]]
def added889 : List (List Vertex) := [[6, 2, 0, 3, 5]]
def attachments889 : Fin tails889.length → Fin 3 := ![1, 0]
theorem accepted889 : CheapOriginalAccepted (decode 889) 0 2
    tails889 added889 attachments889 := by decide

def tails890 : List (List Vertex) := [[7, 0, 5, 3, 4, 6, 2, 1], [5, 6, 3, 0, 2, 7, 1]]
def added890 : List (List Vertex) := [[7, 4, 0, 1, 5]]
def attachments890 : Fin tails890.length → Fin 3 := ![2, 0]
theorem accepted890 : CheapOriginalAccepted (decode 890) 0 1
    tails890 added890 attachments890 := by decide

def tails892 : List (List Vertex) := [[6, 4, 0, 3, 5, 7, 2, 1], [7, 4, 3, 6, 2, 0, 1]]
def added892 : List (List Vertex) := [[6, 1, 7]]
def attachments892 : Fin tails892.length → Fin 3 := ![1, 2]
theorem accepted892 : CheapOriginalAccepted (decode 892) 2 0
    tails892 added892 attachments892 := by decide

def tails901 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 1, 2], [6, 5, 3, 4, 0, 2]]
def added901 : List (List Vertex) := [[5, 1, 0, 6]]
def attachments901 : Fin tails901.length → Fin 3 := ![0, 1]
theorem accepted901 : CheapOriginalAccepted (decode 901) 0 1
    tails901 added901 attachments901 := by decide

def tails902 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 1, 2], [7, 5, 1, 0, 2]]
def added902 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments902 : Fin tails902.length → Fin 3 := ![0, 2]
theorem accepted902 : CheapOriginalAccepted (decode 902) 0 2
    tails902 added902 attachments902 := by decide

def tails903 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 1, 2], [7, 6, 1, 0, 2]]
def added903 : List (List Vertex) := [[6, 4, 0, 3, 7]]
def attachments903 : Fin tails903.length → Fin 3 := ![1, 2]
theorem accepted903 : CheapOriginalAccepted (decode 903) 1 2
    tails903 added903 attachments903 := by decide

def tails904 : List (List Vertex) := [[7, 6, 4, 3, 0, 2, 1, 5], [5, 3, 7, 4, 0, 1]]
def added904 : List (List Vertex) := [[1, 7]]
def attachments904 : Fin tails904.length → Fin 3 := ![2, 0]
theorem accepted904 : CheapOriginalAccepted (decode 904) 2 1
    tails904 added904 attachments904 := by decide

def tails905 : List (List Vertex) := [[5, 1, 2, 0, 3, 7, 4, 6], [6, 0, 4, 3, 5, 7, 1]]
def added905 : List (List Vertex) := [[1, 0, 5]]
def attachments905 : Fin tails905.length → Fin 3 := ![0, 1]
theorem accepted905 : CheapOriginalAccepted (decode 905) 0 2
    tails905 added905 attachments905 := by decide

def tails906 : List (List Vertex) := [[7, 0, 3, 4, 6, 5, 1, 2], [5, 3, 7, 1, 0, 2]]
def added906 : List (List Vertex) := [[7, 4, 0, 5]]
def attachments906 : Fin tails906.length → Fin 3 := ![2, 0]
theorem accepted906 : CheapOriginalAccepted (decode 906) 0 1
    tails906 added906 attachments906 := by decide

def tails908 : List (List Vertex) := [[7, 5, 3, 4, 0, 2, 1, 6], [6, 4, 7, 3, 0, 1]]
def added908 : List (List Vertex) := [[1, 7]]
def attachments908 : Fin tails908.length → Fin 3 := ![2, 1]
theorem accepted908 : CheapOriginalAccepted (decode 908) 2 0
    tails908 added908 attachments908 := by decide

def tails909 : List (List Vertex) := [[6, 1, 2, 0, 4, 7, 3, 5], [5, 0, 3, 4, 6, 7, 1]]
def added909 : List (List Vertex) := [[1, 0, 6]]
def attachments909 : Fin tails909.length → Fin 3 := ![1, 0]
theorem accepted909 : CheapOriginalAccepted (decode 909) 1 2
    tails909 added909 attachments909 := by decide

def tails911 : List (List Vertex) := [[7, 0, 4, 3, 5, 6, 1, 2], [6, 4, 7, 1, 0, 2]]
def added911 : List (List Vertex) := [[7, 3, 0, 6]]
def attachments911 : Fin tails911.length → Fin 3 := ![2, 1]
theorem accepted911 : CheapOriginalAccepted (decode 911) 1 0
    tails911 added911 attachments911 := by decide

def tails913 : List (List Vertex) := [[5, 0, 3, 7, 4, 6, 2, 1], [6, 5, 3, 4, 0, 1]]
def added913 : List (List Vertex) := [[5, 2, 0, 6]]
def attachments913 : Fin tails913.length → Fin 3 := ![0, 1]
theorem accepted913 : CheapOriginalAccepted (decode 913) 0 1
    tails913 added913 attachments913 := by decide

def tails914 : List (List Vertex) := [[5, 0, 7, 3, 4, 6, 2, 1], [7, 5, 2, 0, 1]]
def added914 : List (List Vertex) := [[5, 3, 0, 4, 7]]
def attachments914 : Fin tails914.length → Fin 3 := ![0, 2]
theorem accepted914 : CheapOriginalAccepted (decode 914) 0 2
    tails914 added914 attachments914 := by decide

def tails915 : List (List Vertex) := [[6, 0, 7, 4, 3, 5, 2, 1], [7, 6, 2, 0, 1]]
def added915 : List (List Vertex) := [[6, 4, 0, 3, 7]]
def attachments915 : Fin tails915.length → Fin 3 := ![1, 2]
theorem accepted915 : CheapOriginalAccepted (decode 915) 1 2
    tails915 added915 attachments915 := by decide

def tails916 : List (List Vertex) := [[5, 6, 4, 7, 3, 0, 2, 1], [6, 2, 5, 3, 4, 0, 1]]
def added916 : List (List Vertex) := [[5, 1, 6]]
def attachments916 : Fin tails916.length → Fin 3 := ![0, 1]
theorem accepted916 : CheapOriginalAccepted (decode 916) 0 1
    tails916 added916 attachments916 := by decide

def tails918 : List (List Vertex) := [[7, 0, 5, 2, 1, 6, 4, 3], [5, 1, 0, 2, 6, 7, 3]]
def added918 : List (List Vertex) := [[7, 4, 0, 3, 5]]
def attachments918 : Fin tails918.length → Fin 3 := ![2, 0]
theorem accepted918 : CheapOriginalAccepted (decode 918) 2 1
    tails918 added918 attachments918 := by decide

def tails919 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 1, 0, 2, 5, 7, 4]]
def added919 : List (List Vertex) := [[7, 3, 0, 4, 6]]
def attachments919 : Fin tails919.length → Fin 3 := ![2, 1]
theorem accepted919 : CheapOriginalAccepted (decode 919) 2 0
    tails919 added919 attachments919 := by decide

def tails920 : List (List Vertex) := [[5, 7, 3, 0, 4, 6, 2, 1], [7, 4, 3, 5, 2, 0, 1]]
def added920 : List (List Vertex) := [[5, 1, 7]]
def attachments920 : Fin tails920.length → Fin 3 := ![0, 2]
theorem accepted920 : CheapOriginalAccepted (decode 920) 0 2
    tails920 added920 attachments920 := by decide

def tails921 : List (List Vertex) := [[5, 0, 6, 4, 3, 7, 1, 2], [6, 7, 4, 0, 1, 5, 2]]
def added921 : List (List Vertex) := [[5, 3, 0, 2, 6]]
def attachments921 : Fin tails921.length → Fin 3 := ![0, 1]
theorem accepted921 : CheapOriginalAccepted (decode 921) 1 2
    tails921 added921 attachments921 := by decide

def tails923 : List (List Vertex) := [[7, 0, 6, 2, 1, 5, 3, 4], [6, 5, 2, 0, 3, 7, 4]]
def added923 : List (List Vertex) := [[7, 1, 0, 4, 6]]
def attachments923 : Fin tails923.length → Fin 3 := ![2, 1]
theorem accepted923 : CheapOriginalAccepted (decode 923) 1 0
    tails923 added923 attachments923 := by decide

def tails924 : List (List Vertex) := [[6, 7, 4, 0, 3, 5, 2, 1], [7, 3, 4, 6, 2, 0, 1]]
def added924 : List (List Vertex) := [[6, 1, 7]]
def attachments924 : Fin tails924.length → Fin 3 := ![1, 2]
theorem accepted924 : CheapOriginalAccepted (decode 924) 1 2
    tails924 added924 attachments924 := by decide

end Gallai.Certificate.ThreeAnchor.CheapOrbits
