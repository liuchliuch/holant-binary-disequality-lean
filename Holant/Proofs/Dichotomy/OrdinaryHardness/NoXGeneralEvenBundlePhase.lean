import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSeparateEvenLocal

/-! A complete signed bundle with separately even cumulative incidence
has a full Affine product of supported local phases. Individual rows may
have arbitrary odd incidence; only the complete physical recipe is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenBundlePhase
open Holant Holant.Tractable
open Holant.Tractable.SymmetricBinaryPullback
open OrdinaryNegativeSignedPortsCore (Port)
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
variable {n m k : ℕ} (ps : Fin k→Fin n→Port m)
variable (even : ∀j b,Even (∑v,P.signedCount (ps v) j b))

theorem grouped (a x : Fin m→Bool) :
    (∏v,P.original (ps v) a x)=(∏v,P.constant (ps v))*
      ∏j,∏b : Bool,(P.localFactor a x j b)^(∑v,P.signedCount (ps v) j b) := by
  simp_rw [P.original_grouped]
  rw [Finset.prod_mul_distrib]
  congr 1
  rw [Finset.prod_comm]
  apply Finset.prod_congr rfl
  intro j _
  rw [Finset.prod_comm]
  simp_rw [Finset.prod_pow_eq_pow_sum]

include even in
theorem affine (a : Fin m→Bool) : Affine (fun x=>∏v,P.original (ps v) a x) := by
  have product : Affine (fun x : Fin m→Bool=>∏j,∏b : Bool,(P.localFactor a x j b)^(∑v,P.signedCount (ps v) j b)):=by
    apply F.affine_prod
    intro j
    apply F.affine_prod
    intro b
    let value (t : Bool):=P.unitPhase ((b ^^ a j)&&(b ^^ t))^(∑v,P.signedCount (ps v) j b)
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
  convert product.scale (∏v,P.constant (ps v)) using 1
  funext x
  exact grouped ps a x

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralEvenBundlePhase
end
