import Holant.Certificates.PlatonicDeficient.OutputData

/-! Ninety exact two-by-two minors of the six reconstructed ancestors,
one for each original unordered pair of their six physical ports. -/
namespace Holant.Certificates.PlatonicDeficient
open Holant Holant.Certificates.OctahedralSeparator
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

def sixWord (i : Fin 64) (j : Fin 6) : Bool := i.val.testBit (5-j.val)
def spliceWord (i j : Fin 6) (x y : Fin 6 → Bool) : Fin 6 → Bool :=
  fun k => if k=i ∨ k=j then x k else y k

def ancestorMinorWords : Fin 6 → Fin 15 → Fin 4 → Fin 64 :=
  ![![![0,16,0,3],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,2,0,1],![0,1,0,2],![0,1,0,4]],
    ![![0,16,0,3],![0,8,2,3],![0,4,1,3],![0,2,1,5],![0,1,2,10],![0,8,2,3],![0,4,1,3],![0,2,1,5],![0,1,2,10],![0,4,1,3],![0,2,1,5],![0,1,2,16],![0,2,1,16],![0,1,2,10],![0,1,4,12]],
    ![![0,16,0,3],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,2,0,1],![0,1,0,2],![0,1,0,4]],
    ![![0,16,0,3],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,2,0,1],![0,1,0,2],![0,1,0,4]],
    ![![0,16,0,3],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,8,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,4,0,1],![0,2,0,1],![0,1,0,2],![0,2,0,1],![0,1,0,2],![0,1,0,4]],
    ![![0,16,0,3],![0,8,2,3],![0,4,1,3],![0,2,1,5],![0,1,2,10],![0,8,2,3],![0,4,1,3],![0,2,1,5],![0,1,2,10],![0,4,1,3],![0,2,1,5],![0,1,2,16],![0,2,1,16],![0,1,2,10],![0,1,4,12]]]

def ancestorPairMinor (p : Fin 6) (t : Fin 15) : Scalar :=
  let i := (TetrahedralDeck.pairs t).1
  let j := (TetrahedralDeck.pairs t).2
  let w := fun r => sixWord (ancestorMinorWords p t r)
  let h := reconstruct (deficientImages p)
  h (spliceWord i j (w 0) (w 2))*h (spliceWord i j (w 1) (w 3))-
    h (spliceWord i j (w 0) (w 3))*h (spliceWord i j (w 1) (w 2))

theorem ancestor_pair_minor_nonzero : ∀p : Fin 6,∀t : Fin 15,ancestorPairMinor p t≠0 := by
  intro p
  fin_cases p <;> decide +kernel

end Holant.Certificates.PlatonicDeficient
