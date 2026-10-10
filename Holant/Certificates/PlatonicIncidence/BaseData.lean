import Holant.Certificates.PlatonicIncidence.BaseSecants

/-! Literal identity secants. Every row is proved against all imaginary minors
of the original golden-ratio dictionary by trusted kernel computation. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def tetrahedralLines : Fin 7 → Finset (Fin 12) :=
  ![{0,1},{0,2},{0,3},{0,4,11},{0,5,10},{0,6,9},{0,7,8}]

def tetrahedralLineOf : Fin 12 → Fin 7 := ![0,0,1,2,3,4,5,6,6,5,4,3]

def tetrahedralAnchor : Fin 7 → Fin 12 := ![1,2,3,4,5,6,7]

def octahedralLines : Fin 13 → Finset (Fin 24) :=
  ![{0,1,12,13},{0,2,14,15},{0,3,16,17},{0,4,11},{0,5,10},{0,6,9},{0,7,8},{0,18},{0,19},{0,20},{0,21},{0,22},{0,23}]

def octahedralLineOf : Fin 24 → Fin 13 := ![0,0,1,2,3,4,5,6,6,5,4,3,0,0,1,1,2,2,7,8,9,10,11,12]

def octahedralAnchor : Fin 13 → Fin 24 := ![1,2,3,4,5,6,7,18,19,20,21,22,23]

def icosahedralLines : Fin 31 → Finset (Fin 60) :=
  ![{0,1},{0,2},{0,3},{0,4,11},{0,5,10},{0,6,9},{0,7,8},{0,12},{0,13},{0,14},{0,15},{0,16},{0,17},{0,18},{0,19},{0,20},{0,21},{0,22},{0,23},{0,24,27},{0,25,26},{0,28,30,32,33},{0,29,31,34,35},{0,36,39},{0,37,38},{0,40,41,44,46},{0,42,43,45,47},{0,48,51},{0,49,50},{0,52,54,56,57},{0,53,55,58,59}]

def icosahedralLineOf : Fin 60 → Fin 31 := ![0,0,1,2,3,4,5,6,6,5,4,3,7,8,9,10,11,12,13,14,15,16,17,18,19,20,20,19,21,22,21,22,21,21,22,22,23,24,24,23,25,25,26,26,25,26,25,26,27,28,28,27,29,30,29,30,29,29,30,30]

def icosahedralAnchor : Fin 31 → Fin 60 := ![1,2,3,4,5,6,7,12,13,14,15,16,17,18,19,20,21,22,23,24,25,28,29,36,37,40,42,48,49,52,53]

def baseCount : PlatonicModel → ℕ
  | .tetrahedral => 7
  | .octahedral => 13
  | .icosahedral => 31

def baseLine : (g : PlatonicModel) → Fin (baseCount g) → Finset (Fin (size g))
  | .tetrahedral => tetrahedralLines
  | .octahedral => octahedralLines
  | .icosahedral => icosahedralLines

def baseLineOf : (g : PlatonicModel) → Fin (size g) → Fin (baseCount g)
  | .tetrahedral => tetrahedralLineOf
  | .octahedral => octahedralLineOf
  | .icosahedral => icosahedralLineOf

def baseAnchor : (g : PlatonicModel) → Fin (baseCount g) → Fin (size g)
  | .tetrahedral => tetrahedralAnchor
  | .octahedral => octahedralAnchor
  | .icosahedral => icosahedralAnchor

end Holant.Certificates.PlatonicIncidence
