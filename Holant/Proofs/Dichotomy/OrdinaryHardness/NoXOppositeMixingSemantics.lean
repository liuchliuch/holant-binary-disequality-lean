import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXOppositeMixingLift

/-! Opposite physical rows mix through their logical pullbacks. The alpha
condition is imposed on that pullback, retaining both actual source scales. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingSemantics
open Holant Holant.Tractable
open OrdinaryNegativeMixedBlockData OrdinaryNegativeXUniversalResource
open NoXOppositeMixingLift
namespace M
export OrdinaryNegativeXUniversalMixingCore (same_nonaffine unary_first_nonaffine unary_second_nonaffine three_first_value three_second_value)
export OrdinaryNegativeSparseMixingThreeSeven (three_alpha_nonaffine seven_alpha_nonaffine mixed)
end M
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable (ka kb : Kind)
variable (f : Signature AlgebraicComplex ka.arity) (g : Signature AlgebraicComplex kb.arity)
variable (alpha : Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action f))
variable (affine : Affine g) (full_f : ∀x,f (ka.code x)≠0) (full_g : ∀x,g (kb.code x)≠0)
include alpha affine full_f full_g in
theorem base_bad : ¬Affine (coefficient (P.table f g) (base ka kb) 0) := by
  cases ka <;> cases kb
  · exact M.same_nonaffine .one f g alpha affine full_f full_g
  · exact M.unary_first_nonaffine .three f g alpha affine full_f full_g
  · exact M.unary_first_nonaffine .seven f g alpha affine full_f full_g
  · exact M.unary_second_nonaffine .three f g alpha affine full_f full_g
  · exact M.same_nonaffine .three f g alpha affine full_f full_g
  · have h:=M.three_alpha_nonaffine g f affine alpha full_g full_f
    have he : coefficient (P.table f g) (base .three .seven) 0=M.mixed g f := funext (M.three_first_value f g)
    rwa [he]
  · exact M.unary_second_nonaffine .seven f g alpha affine full_f full_g
  · have h:=M.seven_alpha_nonaffine f g alpha affine full_f full_g
    have he : coefficient (P.table f g) (base .seven .three) 0=M.mixed f g := funext (M.three_second_value f g)
    rwa [he]
  · exact M.same_nonaffine .seven f g alpha affine full_f full_g

variable (H : (j : Fin 2)→Signature AlgebraicComplex
    (P.arity ka.arity kb.arity j.val+P.arity ka.arity kb.arity j.val))
include alpha affine full_f full_g in
theorem lifted_bad (eq : compressed H=P.table f g) :
    ¬Affine (coefficient H (lift (base ka kb)) 0) := by
  intro aff
  apply base_bad ka kb f g alpha affine full_f full_g
  have pull:=aff.precompose (@opposite (size ka kb)) (opposite_affine _)
  have he : (fun x=>coefficient H (lift (base ka kb)) 0 (opposite x))=
      coefficient (P.table f g) (base ka kb) 0 := by
    funext x
    rw [value,eq]
  rwa [he] at pull

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOppositeMixingSemantics
end
