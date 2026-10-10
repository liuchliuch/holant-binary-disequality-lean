import Holant.Certificates.PlatonicIncidence.Coordinates
import Holant.Certificates.MatchingProductBridge.Interface
import Holant.Certificates.TetrahedralBridge.Basis

/-! Literal directions and orderings for the five frames in Lemma9.29.
The indices refer to the already proved complete sixty-point group dictionary. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit

def directionIndex : Fin 15 → Fin 60 :=
  ![3,1,0,45,41,37,46,43,36,38,40,47,39,42,44]

def permutation : Fin 6 → Fin 3 → Fin 3 :=
  ![![0,1,2],![1,2,0],![2,0,1],![0,2,1],![1,0,2],![2,1,0]]

def ordering (i : Fin 30) (j : Fin 3) : Fin 15 :=
  ⟨3*(i.val/6)+(permutation ⟨i.val%6,by omega⟩ j).val,by
    have h := (permutation ⟨i.val%6,by omega⟩ j).isLt
    omega⟩

noncomputable section

def regular (j : Fin 15) : FourTensor :=
  matrixR (representative .icosahedral (directionIndex j))

def candidate (i : Fin 18) : FourTensor :=
  Fin.addCases (fun j : Fin 3 => ![0,(1/2 : ℂ) • A,(1/2 : ℂ) • B] j) regular i

def sliceVector (j : Fin 15) : Fin 3 → ℝ := fun k =>
  GoldenInt.eval (icosahedralRaw (directionIndex j) (![0,1,3] k))

def sourceFrame : Fin 15 → Fin 3 → ℝ :=
  ![![0,0,1],![0,1,0],![1,0,0],
    ![1,-goldenReciprocal^2,goldenReciprocal],![1,-goldenRatio,-goldenRatio^2],![1,goldenRatio,-goldenReciprocal],
    ![1,-goldenReciprocal^2,-goldenReciprocal],![1,-goldenRatio,goldenRatio^2],![1,goldenRatio,goldenReciprocal],
    ![1,-goldenRatio,goldenReciprocal],![1,goldenRatio,goldenRatio^2],![1,goldenReciprocal^2,-goldenReciprocal],
    ![1,-goldenRatio,-goldenReciprocal],![1,goldenRatio,-goldenRatio^2],![1,goldenReciprocal^2,goldenReciprocal]]

def uniformKernel : Binary := (goldenRatio : ℂ) • Q1 - (goldenReciprocal : ℂ) • Q2 + Q3
def subsequentKernel : Binary := Q0 - ((goldenReciprocal : ℂ)^2) • Q1 + (goldenReciprocal : ℂ) • Q3
def uniformOutput (i : Fin 30) : FourTensor :=
  (goldenRatio : ℂ) • regular (ordering i 0) -
    (goldenReciprocal : ℂ) • regular (ordering i 1) + regular (ordering i 2)

end
end Holant.Certificates.IcosahedralSeparator
