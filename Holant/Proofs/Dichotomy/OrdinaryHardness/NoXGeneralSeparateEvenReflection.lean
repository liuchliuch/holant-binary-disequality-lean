import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateEvenLocal

/-! On separately even signed support, LocalAffine and Affine coincide.
The converse removes the proved full Affine local phase at one supported
marker, so it applies to smaller L faces without ordinary minimality. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateEvenReflection
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalSignedMultiplicityPhase (original unitPhase unitPhase_nonzero)
export NoXSeparateSignedProjection (signedCount)
end P
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {n m r : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
variable (ps : Fin n→Port m) (even : ∀j b,Even (P.signedCount ps j b))
variable (code : Word r→Word m) (code_affine : TwoTranslate.IsAffineMap code)
variable (chart : ∀x,word ps (code x)=D.encode x)

include even code_affine chart in
theorem affine_of_local (square : Affine (fun x=>f x^2)) (good : LocalAffine f) : Affine f:=by
  have nonzero : f≠0:=by intro hz;exact D.supported (origin _) (congrFun hz _)
  obtain ⟨S,hS⟩:=OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  apply D.affine_of_reduced S hS
  let a : Word r:=origin r
  have phase:=(NoXGeneralSeparateEvenLocal.phase_affine ps even (code a)).precompose code code_affine
  have phaseInv:=OrdinaryNegativeAffineSquareReciprocal.affine_inverse _ phase
  have twist:=(good (D.encode a) (D.supported a)).precompose D.encode D.affine
  convert phaseInv.mul twist using 1
  funext x
  change f (D.encode x)=(P.original ps (code a) (code x))⁻¹*
    localTwist (D.encode a) f (D.encode x)
  have exactPhase : P.original ps (code a) (code x)=
      ∏i,if D.encode a i && D.encode x i then zetaEight else 1:=by
    simp only [P.original,P.unitPhase,chart]
  have phaseNonzero : P.original ps (code a) (code x)≠0:=by
    unfold P.original
    exact Finset.prod_ne_zero_iff.mpr (fun i _=>P.unitPhase_nonzero _)
  rw [localTwist_apply,←exactPhase,←mul_assoc,inv_mul_cancel₀ phaseNonzero,one_mul]

include even code_affine chart in
theorem local_iff_affine (square : Affine (fun x=>f x^2)) : LocalAffine f ↔ Affine f:=
  ⟨affine_of_local D ps even code code_affine chart square,
    NoXGeneralSeparateEvenLocal.local_of_affine ps even D code code_affine chart square⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateEvenReflection
end
