import Holant.Certificates.OppositeIcosahedral.Outputs
import Holant.Certificates.MatchingContractionClosure.NativeCollection

namespace Holant.Certificates.OppositeIcosahedral
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 1000000
set_option maxHeartbeats 10000000

theorem X_Q1 : X=(-Complex.I) • (Matrix.of Q1) := by
  ext a b
  cases a <;> cases b <;> simp [X,Q1,Signature.disequality,Complex.I_sq]

theorem X_tetrahedral : groupDirection .tetrahedral X := by
  rw [X_Q1]
  exact groupDirection_smul .tetrahedral (quaternion_axis_direction .tetrahedral 1)
    (neg_ne_zero.mpr Complex.I_ne_zero)

theorem direction_X : Direction X := Direction.of_tetrahedral X_tetrahedral

theorem standardRepresentative_Q2 : standardRepresentative 2=Matrix.of Q2 := by
  ext a b
  cases a <;> cases b <;>
    simp [standardRepresentative,RainbowOrbit.representative,RainbowOrbit.raw,RainbowOrbit.icosahedralRaw,
      RainbowOrbit.goldenMatrix,RainbowOrbit.GoldenInt.eval,quaternion,Q0,Q1,Q2,Q3,Signature.equality]

theorem X_conjugate_Q2 : X=(-Complex.I) • conjugate (Matrix.of Q2) := by
  ext a b
  cases a <;> cases b <;>
    simp [X,conjugate,D,Dinv,Q0,Q1,Q2,Q3,Signature.equality,Signature.disequality,Matrix.mul_apply,
      Matrix.smul_apply] <;> ring_nf <;> simp [Complex.I_sq] <;> ring

def binaryIndex (i : Fin 60) : Fin 60 :=
  RainbowOrbit.productIndex .icosahedral
    (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) (2 : Fin 60)

def binaryScale (i : Fin 60) : ℂ :=
  -(RainbowOrbit.productScale .icosahedral (2 : Fin 60) i : ℂ)*
    (RainbowOrbit.productScale .icosahedral
      (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) (2 : Fin 60) : ℂ)

theorem binaryScale_ne_zero (i : Fin 60) : binaryScale i≠0 := by
  apply mul_ne_zero
  · exact neg_ne_zero.mpr (Int.cast_ne_zero.mpr (RainbowOrbit.raw_certificate .icosahedral (2 : Fin 60) i).1)
  · exact Int.cast_ne_zero.mpr (RainbowOrbit.raw_certificate .icosahedral
      (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) (2 : Fin 60)).1

/-- Every inserted native-X binary is itself one fixed actual opposite-group
representative with a recorded, nonzero scale. -/
theorem native_pair_fixed (i : Fin 60) :
    MatchingContractionClosure.nativePair (oppositeRepresentative i)=
      binaryScale i • oppositeRepresentative (binaryIndex i) := by
  change X*oppositeRepresentative i*X=_
  rw [X_conjugate_Q2,←standardRepresentative_Q2]
  simp only [oppositeRepresentative,Matrix.smul_mul,Matrix.mul_smul,smul_smul,←conjugate_mul]
  have h1 : standardRepresentative 2*standardRepresentative i=
      (RainbowOrbit.productScale .icosahedral (2 : Fin 60) i : ℂ) •
        standardRepresentative (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) :=
    RainbowOrbit.mul_exact .icosahedral (2 : Fin 60) i
  have h2 : standardRepresentative (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i)*standardRepresentative 2=
      (RainbowOrbit.productScale .icosahedral (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) (2 : Fin 60) : ℂ) •
        standardRepresentative (binaryIndex i) :=
    RainbowOrbit.mul_exact .icosahedral (RainbowOrbit.productIndex .icosahedral (2 : Fin 60) i) (2 : Fin 60)
  rw [h1,Matrix.smul_mul,h2,conjugate_smul,conjugate_smul,smul_smul,smul_smul]
  unfold binaryScale binaryIndex
  congr 1
  ring_nf
  simp [Complex.I_sq] <;> ring

theorem binaryIndex_bijective : Function.Bijective binaryIndex := by decide +kernel

theorem native_pair_direction {K : Mat} (hK : Direction K) :
    Direction (MatchingContractionClosure.nativePair K) ∧
      Direction ((MatchingContractionClosure.nativePair K)*X) := by
  have hb : Direction (MatchingContractionClosure.nativePair K) := (direction_X.mul hK).mul direction_X
  exact ⟨hb,hb.mul direction_X⟩

end
end Holant.Certificates.OppositeIcosahedral
