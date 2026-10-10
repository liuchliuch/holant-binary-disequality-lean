import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalSignedMultiplicity
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalAffineCubeWitness

/-! Separately even positive and negative multiplicities make every local
twist a full Affine coordinate phase. Consequently an Affine original row
with this exact signed support is LocalAffine, at every support rank. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateEvenLocal
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeAffineSystematicSupport
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace P
export NoXLocalSignedMultiplicityPhase (original original_grouped constant localFactor unitPhase unitPhase_nonzero)
export NoXSeparateSignedProjection (signedCount)
end P
namespace F
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {n m r : ℕ} (ps : Fin n→Port m) (even : ∀j b,Even (P.signedCount ps j b))

include even in
theorem phase_affine (a : Word m) : Affine (P.original ps a) := by
  have product : Affine (fun x : Word m=>∏j,∏b : Bool,(P.localFactor a x j b)^P.signedCount ps j b):=by
    apply F.affine_prod
    intro j
    apply F.affine_prod
    intro b
    let value (t : Bool):=P.unitPhase ((b ^^ a j)&&(b ^^ t))^P.signedCount ps j b
    have fourth (t : Bool) : value t^4=1:=by
      dsimp only [value]
      rw [pow_right_comm]
      cases hc : (b ^^ a j)&&(b ^^ t)
      · simp [P.unitPhase]
      · simp only [P.unitPhase,ite_true,zetaEight_pow_four]
        exact (even j b).neg_one_pow
    have unary:=GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers j
      (value false) (value true) (pow_ne_zero _ (P.unitPhase_nonzero _))
      ((fourth false).trans (fourth true).symm)
    convert unary using 1
    funext x
    cases hx : x j <;> simp [P.localFactor,value,hx]
  convert product.scale (P.constant ps) using 1
  funext x
  exact P.original_grouped ps a x

variable {f : Signature AlgebraicComplex n} (D : SystematicSupport f r)
variable (code : Word r→Word m) (code_affine : TwoTranslate.IsAffineMap code)
variable (chart : ∀x,word ps (code x)=D.encode x)

include even code_affine chart in
theorem local_of_affine (square : Affine (fun x=>f x^2)) (good : Affine f) : LocalAffine f := by
  have nonzero : f≠0:=by intro hz;exact D.supported (origin _) (congrFun hz _)
  obtain ⟨S,hS⟩:=OrdinaryNegativeAffineSquareSupport.exists_support_system f square nonzero
  intro alpha supported
  let a : Word r:=fun i=>alpha (D.ports i)
  have ha : D.encode a=alpha:=D.covers alpha supported
  rw [←ha]
  apply (NoXLocalAffineCubeWitness.twistChart D a).affine_of_reduced S
  · intro x
    exact (hS x).trans (NoXLocalRankOneCriterion.twist_support f (D.encode a) x).symm
  · have phase:=(phase_affine ps even (code a)).precompose code code_affine
    have actual:=phase.mul (D.reduced_affine good)
    convert actual using 1
    funext x
    simp only [SystematicSupport.reduced,NoXLocalAffineCubeWitness.twistChart,localTwist_apply,
      P.original,P.unitPhase,chart]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSeparateEvenLocal
end
