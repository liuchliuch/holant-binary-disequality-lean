import Holant.Certificates.OctahedralSeparator.TensorData

namespace Holant.Certificates.OctahedralSeparator
open Holant
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

def wordIndex (x : Word) : Fin 16 :=
  Fin.ofNat 16 (8*(x 0).toNat+4*(x 1).toNat+2*(x 2).toNat+(x 3).toNat)
def tensorFrom (v : Fin 16 → Scalar) : Signature Scalar 4 := fun x => v (wordIndex x)

def baseValues : Fin 15 → Fin 16 → Scalar :=
  ![![(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0),0,(coeff (-1/2) 0 0 0),(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0),(coeff (-1/2) 0 0 0),0,(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0)],![0,0,0,1,0,0,0,0,0,0,0,0,1,0,0,0],![(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0),0,(coeff (-1/2) 0 0 0),(coeff (-1/2) 0 0 0),0,0,(coeff (-1/2) 0 0 0),(coeff (-1/2) 0 0 0),0,(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0)],![(coeff (1/4) 0 0 0),(coeff 0 0 (1/4) 0),(coeff 0 0 (-1/4) 0),(coeff (3/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff 0 0 (1/4) 0),(coeff 0 0 (1/4) 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff (3/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff 0 0 (1/4) 0),(coeff (1/4) 0 0 0)],![(coeff (1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff 0 0 (1/4) 0),(coeff (3/4) 0 0 0),(coeff 0 0 (1/4) 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff 0 0 (1/4) 0),(coeff (3/4) 0 0 0),(coeff 0 0 (1/4) 0),(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 0 0)],![(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0),0,(coeff (-1/2) 0 0 0),(coeff 0 0 (1/2) 0),0,0,(coeff 0 0 (-1/2) 0),(coeff (-1/2) 0 0 0),0,(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0)],![(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0),0,(coeff (-1/2) 0 0 0),(coeff 0 0 (-1/2) 0),0,0,(coeff 0 0 (1/2) 0),(coeff (-1/2) 0 0 0),0,(coeff (1/2) 0 0 0),0,0,(coeff (1/2) 0 0 0)],![(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (3/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (3/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0)],![(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (3/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (3/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0)],![(coeff 0 0 (-1/4) 0),0,0,(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),0,(coeff (-1/4) 0 (1/4) 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),0,0,(coeff 0 0 (1/4) 0)],![0,0,(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff (-1/4) 0 0 0),0,(coeff (-1/4) 0 (-1/4) 0),(coeff (1/4) 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),0,0],![(coeff 0 0 (-1/4) 0),0,(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),0,(coeff 0 0 (-1/4) 0),(coeff 0 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),0,(coeff (1/4) 0 (1/4) 0),(coeff 0 0 (-1/4) 0),0,(coeff 0 0 (1/4) 0)],![(coeff 0 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),(coeff (1/4) 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),0,(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),0,(coeff (-1/4) 0 0 0),0,(coeff (1/4) 0 (1/4) 0),(coeff (1/4) 0 0 0),0,(coeff 0 0 (1/4) 0)],![(coeff 0 0 (-1/4) 0),0,0,(coeff (1/4) 0 0 0),(coeff 0 0 (-1/4) 0),(coeff (-1/4) 0 (-1/4) 0),0,(coeff 0 0 (-1/4) 0),(coeff 0 0 (-1/4) 0),0,(coeff (-1/4) 0 (1/4) 0),(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 0 0),0,0,(coeff 0 0 (1/4) 0)],![0,0,(coeff 0 0 (-1/4) 0),(coeff (1/4) 0 0 0),(coeff (-1/4) 0 0 0),(coeff (-1/4) 0 0 0),0,(coeff (-1/4) 0 (-1/4) 0),(coeff (1/4) 0 (-1/4) 0),0,(coeff (-1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff (1/4) 0 0 0),(coeff 0 0 (-1/4) 0),0,0]]
def cachedBase (r : Fin 15) : Signature Scalar 4 := tensorFrom (baseValues r)

theorem base_exact_0 : cachedBase 0 = baseCard 0 := by decide +kernel
theorem base_exact_1 : cachedBase 1 = baseCard 1 := by decide +kernel
theorem base_exact_2 : cachedBase 2 = baseCard 2 := by decide +kernel
theorem base_exact_3 : cachedBase 3 = baseCard 3 := by decide +kernel
theorem base_exact_4 : cachedBase 4 = baseCard 4 := by decide +kernel
theorem base_exact_5 : cachedBase 5 = baseCard 5 := by decide +kernel
theorem base_exact_6 : cachedBase 6 = baseCard 6 := by decide +kernel
theorem base_exact_7 : cachedBase 7 = baseCard 7 := by decide +kernel
theorem base_exact_8 : cachedBase 8 = baseCard 8 := by decide +kernel
theorem base_exact_9 : cachedBase 9 = baseCard 9 := by decide +kernel
theorem base_exact_10 : cachedBase 10 = baseCard 10 := by decide +kernel
theorem base_exact_11 : cachedBase 11 = baseCard 11 := by decide +kernel
theorem base_exact_12 : cachedBase 12 = baseCard 12 := by decide +kernel
theorem base_exact_13 : cachedBase 13 = baseCard 13 := by decide +kernel
theorem base_exact_14 : cachedBase 14 = baseCard 14 := by decide +kernel
theorem base_exact (r : Fin 15) : cachedBase r=baseCard r := by
  fin_cases r
  · exact base_exact_0
  · exact base_exact_1
  · exact base_exact_2
  · exact base_exact_3
  · exact base_exact_4
  · exact base_exact_5
  · exact base_exact_6
  · exact base_exact_7
  · exact base_exact_8
  · exact base_exact_9
  · exact base_exact_10
  · exact base_exact_11
  · exact base_exact_12
  · exact base_exact_13
  · exact base_exact_14

end Holant.Certificates.OctahedralSeparator
