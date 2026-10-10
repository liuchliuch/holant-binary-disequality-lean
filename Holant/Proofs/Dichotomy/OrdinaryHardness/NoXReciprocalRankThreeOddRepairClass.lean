import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalRankThreeOddRepairCore
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniform

/-! The correction copy has two occurrences of each used variable. Its
uniform phase is therefore an invertible affine gauge. The repaired row
keeps the source A or alpha-A class with exact coefficients. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairClass
open Holant Holant.Tractable
open scoped BigOperators
namespace C
export NoXReciprocalRankThreeOddRepairCore (exotic correction correctionPorts correction_even correction_affine word_correction)
export NoXReciprocalMixedProjectionCore (logical)
end C
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
export OrdinaryNegativeSignedRowsUniform (affine_iff product)
export OrdinaryNegativeSparseMixingAlpha (twist twist_action)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable (f : Signature AlgebraicComplex 7)
def output : Signature AlgebraicComplex 7 := fun z=>f (C.logical C.exotic z)*f (C.correction z)

theorem affine (ha : Affine f) : Affine (output f) :=
  (ha.precompose (C.logical C.exotic) (NoXGeneralUniformTranslation.affine_map C.exotic)).mul
    (ha.precompose C.correction C.correction_affine)

theorem alpha (ha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (output f)) := by
  have hf : Affine (U.uniform f) := by
    rw [U.twist_action] at ha
    convert ha using 1
    funext z
    simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,U.twist]
  have first:=NoXGeneralUniformTranslation.uniform_affine C.exotic f hf
  have second : Affine (fun z=>f (C.correction z)) := by
    have he : ∀q,Even (∑_i : Fin 1,OrdinaryNegativeSignedPortsIncidence.bundleSize C.correctionPorts q) := by
      intro q
      simpa only [Fin.sum_univ_one] using C.correction_even q
    have hiff:=U.affine_iff (fun _ : Fin 1=>f) (fun _=>C.correctionPorts) he
    have one (g : Signature AlgebraicComplex 7) :
        U.product (fun _ : Fin 1=>g) (fun _=>C.correctionPorts)=(fun z=>g (C.correction z)) := by
      funext z
      change (∏_i : Fin 1,g (OrdinaryNegativeSignedPortsCore.word C.correctionPorts z))=_
      rw [Fin.prod_univ_one,C.word_correction]
    rw [one,one] at hiff
    exact hiff.mp (hf.precompose C.correction C.correction_affine)
  rw [U.twist_action]
  convert first.mul second using 1
  funext z
  simp only [output,U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,U.twist]
  ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXReciprocalRankThreeOddRepairClass
end
