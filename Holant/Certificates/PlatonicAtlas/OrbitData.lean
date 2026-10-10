import Holant.Certificates.PlatonicIncidence.BaseData

namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
set_option maxRecDepth 100000
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

def tetrahedralSeed (n : ℕ) : Fin 7 :=
  if n=2 then 0 else
  if n=3 then 3 else
  0

def tetrahedralBaseWord (b : Fin 7) : Fin 12 × Fin 12 :=
  (#[(0,0),(5,4),(4,6),(0,0),(3,3),(2,2),(1,1)] : Array (Fin 12 × Fin 12)).getD b.val (0,0)

def octahedralSeed (n : ℕ) : Fin 13 :=
  if n=2 then 7 else
  if n=3 then 3 else
  if n=4 then 0 else
  0

def octahedralBaseWord (b : Fin 13) : Fin 24 × Fin 24 :=
  (#[(0,0),(5,4),(4,6),(0,0),(3,3),(2,2),(1,1),(0,0),(1,1),(4,11),(9,6),(6,9),(5,10)] : Array (Fin 24 × Fin 24)).getD b.val (0,0)

def icosahedralSeed (n : ℕ) : Fin 31 :=
  if n=2 then 0 else
  if n=3 then 3 else
  if n=5 then 21 else
  0

def icosahedralBaseWord (b : Fin 31) : Fin 60 × Fin 60 :=
  (#[(0,0),(5,4),(4,6),(0,0),(3,3),(2,2),(1,1),(15,15),(14,14),(13,13),(12,12),(20,20),(22,22),(23,23),(21,21),(17,17),(18,18),(16,16),(19,19),(16,16),(13,13),(0,0),(2,2),(15,15),(17,17),(5,10),(6,9),(12,12),(21,21),(4,11),(7,8)] : Array (Fin 60 × Fin 60)).getD b.val (0,0)

def seed : (g : PlatonicModel) → ℕ → Fin (baseCount g)
  | .tetrahedral => tetrahedralSeed
  | .octahedral => octahedralSeed
  | .icosahedral => icosahedralSeed

def baseWord : (g : PlatonicModel) → Fin (baseCount g) → Fin (size g) × Fin (size g)
  | .tetrahedral => tetrahedralBaseWord
  | .octahedral => octahedralBaseWord
  | .icosahedral => icosahedralBaseWord

def twoSidedIndex (g : PlatonicModel) (a b k : Fin (size g)) : Fin (size g) :=
  productIndex g (productIndex g a k) b

def BaseOrbitEntry (g : PlatonicModel) (b : Fin (baseCount g)) : Prop :=
  (baseLine g (seed g (baseLine g b).card)).image
    (twoSidedIndex g (baseWord g b).1 (baseWord g b).2)=baseLine g b

instance (g : PlatonicModel) (b : Fin (baseCount g)) : Decidable (BaseOrbitEntry g b) :=
  inferInstanceAs (Decidable (_=_))

end Holant.Certificates.PlatonicAtlas
