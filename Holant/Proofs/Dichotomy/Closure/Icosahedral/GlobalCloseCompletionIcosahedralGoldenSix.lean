import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralPreserver
import Holant.Certificates.PlatonicIncidence.Subspaces
import Holant.Certificates.TetrahedralPreservers.RangeGeometry

/-! Generic I/opposite-I coefficient proof extracted from RankTwo/GoldenSix.
No old saved-State dispatcher or caller-supplied classification is imported.
This candidate retains the actual full sixty-point hypotheses and proof. -/
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
set_option maxRecDepth 32768

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankTwo
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.PlatonicIncidence Holant.Certificates.RainbowOrbit
open Holant.Certificates.TetrahedralPreservers
open scoped BigOperators Matrix

def goldenPair (u v : GoldenVector) : GoldenInt :=
  GoldenInt.add
    (GoldenInt.sub (GoldenInt.mul (u 0) (v 0)) (GoldenInt.mul (u 1) (v 1)))
    (GoldenInt.sub (GoldenInt.mul (u 2) (v 2)) (GoldenInt.mul (u 3) (v 3)))

def goldenProjectionCross (j r s : Fin 60) : GoldenInt :=
  GoldenInt.sub
    (GoldenInt.mul (goldenPair (icosahedralRaw 0) (icosahedralRaw r))
      (goldenPair (icosahedralRaw j) (icosahedralRaw s)))
    (GoldenInt.mul (goldenPair (icosahedralRaw 0) (icosahedralRaw s))
      (goldenPair (icosahedralRaw j) (icosahedralRaw r)))

/-- Rows follow the OLD baseAnchor .icosahedral order exactly. No selected
coverage of independent pairs is asserted by this table alone. -/
def sixWitness : Fin 31 → Fin 6 → Fin 60 :=
  ![![0,1,4,8,36,38], ![0,2,4,6,24,25], ![0,3,4,5,24,26],
    ![0,1,4,5,6,9], ![0,1,4,5,7,8], ![0,1,4,5,7,11], ![0,1,4,5,6,10],
    ![0,1,5,6,7,8], ![0,1,4,6,7,8], ![0,1,4,5,7,8], ![0,1,4,5,6,9],
    ![0,1,4,5,6,9], ![0,1,5,6,7,8], ![0,1,4,5,7,8], ![0,1,4,6,7,8],
    ![0,1,4,6,7,8], ![0,1,4,5,6,9], ![0,1,4,5,7,8], ![0,1,5,6,7,8],
    ![0,2,4,5,6,7], ![0,2,4,5,6,7], ![0,2,4,5,6,7], ![0,2,4,5,6,7],
    ![0,1,4,5,8,9], ![0,1,4,5,8,9], ![0,1,4,5,8,9], ![0,1,4,5,8,9],
    ![0,1,4,6,8,10], ![0,1,4,6,8,10], ![0,1,4,6,8,10], ![0,1,4,6,8,10]]

def GoldenSix (t : Fin 31) : Prop :=
  ∀ a b : Fin 6, a ≠ b →
    GoldenInt.norm (goldenProjectionCross (baseAnchor .icosahedral t)
      (sixWitness t a) (sixWitness t b)) ≠ 0

instance (t : Fin 31) : Decidable (GoldenSix t) := by
  unfold GoldenSix
  infer_instance

/- Separate kernel proofs keep the fixed default budget for every actual
six-by-six row. Each check concerns only small integers, including BOTH
coefficients of phi and its norm, never complex decidable equality. -/
private theorem row00 : GoldenSix 0 := by decide +kernel
private theorem row01 : GoldenSix 1 := by decide +kernel
private theorem row02 : GoldenSix 2 := by decide +kernel
private theorem row03 : GoldenSix 3 := by decide +kernel
private theorem row04 : GoldenSix 4 := by decide +kernel
private theorem row05 : GoldenSix 5 := by decide +kernel
private theorem row06 : GoldenSix 6 := by decide +kernel
private theorem row07 : GoldenSix 7 := by decide +kernel
private theorem row08 : GoldenSix 8 := by decide +kernel
private theorem row09 : GoldenSix 9 := by decide +kernel
private theorem row10 : GoldenSix 10 := by decide +kernel
private theorem row11 : GoldenSix 11 := by decide +kernel
private theorem row12 : GoldenSix 12 := by decide +kernel
private theorem row13 : GoldenSix 13 := by decide +kernel
private theorem row14 : GoldenSix 14 := by decide +kernel
private theorem row15 : GoldenSix 15 := by decide +kernel
private theorem row16 : GoldenSix 16 := by decide +kernel
private theorem row17 : GoldenSix 17 := by decide +kernel
private theorem row18 : GoldenSix 18 := by decide +kernel
private theorem row19 : GoldenSix 19 := by decide +kernel
private theorem row20 : GoldenSix 20 := by decide +kernel
private theorem row21 : GoldenSix 21 := by decide +kernel
private theorem row22 : GoldenSix 22 := by decide +kernel
private theorem row23 : GoldenSix 23 := by decide +kernel
private theorem row24 : GoldenSix 24 := by decide +kernel
private theorem row25 : GoldenSix 25 := by decide +kernel
private theorem row26 : GoldenSix 26 := by decide +kernel
private theorem row27 : GoldenSix 27 := by decide +kernel
private theorem row28 : GoldenSix 28 := by decide +kernel
private theorem row29 : GoldenSix 29 := by decide +kernel
private theorem row30 : GoldenSix 30 := by decide +kernel

theorem golden_six (t : Fin 31) : GoldenSix t := by
  fin_cases t
  · exact row00
  · exact row01
  · exact row02
  · exact row03
  · exact row04
  · exact row05
  · exact row06
  · exact row07
  · exact row08
  · exact row09
  · exact row10
  · exact row11
  · exact row12
  · exact row13
  · exact row14
  · exact row15
  · exact row16
  · exact row17
  · exact row18
  · exact row19
  · exact row20
  · exact row21
  · exact row22
  · exact row23
  · exact row24
  · exact row25
  · exact row26
  · exact row27
  · exact row28
  · exact row29
  · exact row30

noncomputable section
abbrev rootPoint := Preserver.Completion.point

theorem goldenPair_eval (u v : GoldenVector) :
    (GoldenInt.eval (goldenPair u v) : ℂ) =
      pairing (coordinates (goldenMatrix u)) (coordinates (goldenMatrix v)) := by
  have hcoordinates (w : GoldenVector) : coordinates (goldenMatrix w) =
      fun i => (GoldenInt.eval (w i) : ℂ) := by
    funext i
    exact coordinates_golden w i
  rw [hcoordinates u, hcoordinates v]
  simp [goldenPair,GoldenInt.eval_add,GoldenInt.eval_sub,GoldenInt.eval_mul,
    pairing,frobeniusSigns,Fin.sum_univ_succ] <;> ring

theorem goldenCross_eval (j r s : Fin 60) :
    (GoldenInt.eval (goldenProjectionCross j r s) : ℂ) =
      pairing (rootPoint false 0) (rootPoint false r) *
        pairing (rootPoint false j) (rootPoint false s) -
      pairing (rootPoint false 0) (rootPoint false s) *
        pairing (rootPoint false j) (rootPoint false r) := by
  simp only [goldenProjectionCross,GoldenInt.eval_sub,GoldenInt.eval_mul,
    Complex.ofReal_sub,Complex.ofReal_mul,goldenPair_eval] <;> rfl

/-- Six actual original-root images in the bilinear quotient of the same
identity/anchor span. Nonzero cross products also prove each direction is
nonzero; the six witnesses are not just six dictionary rows. -/
theorem identity_six (t : Fin 31) (a b : Fin 6) (hab : a ≠ b) :
    pairing (rootPoint false 0) (rootPoint false (sixWitness t a)) *
      pairing (rootPoint false (baseAnchor .icosahedral t)) (rootPoint false (sixWitness t b)) -
    pairing (rootPoint false 0) (rootPoint false (sixWitness t b)) *
      pairing (rootPoint false (baseAnchor .icosahedral t)) (rootPoint false (sixWitness t a)) ≠ 0 := by
  have he := goldenCross_eval (baseAnchor .icosahedral t) (sixWitness t a) (sixWitness t b)
  intro hz
  have hzero : (GoldenInt.eval (goldenProjectionCross (baseAnchor .icosahedral t)
      (sixWitness t a) (sixWitness t b)) : ℂ) = 0 := he.trans hz
  exact (GoldenInt.eval_ne_zero _ (golden_six t a b hab)) (Complex.ofReal_eq_zero.mp hzero)

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.RankTwo
