import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXLocalMergePhase

/-! A selected bad local twist becomes an origin-supported non-Affine row
after weighted-antidiagonal attachments at exactly its true marker ports. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizationPhase
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
namespace F
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.GeneralEOPairedFamilyExtractionPhaseNormalization (affine_prod)
end F
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false
variable {n : ℕ}

def weight (a x : Word n) (v w : AlgebraicComplex) : AlgebraicComplex :=
  ∏i,if a i then (if x i then v else w) else 1

def normalized (f : Signature AlgebraicComplex n) (a : Word n) (v w : AlgebraicComplex) :
    Signature AlgebraicComplex n := fun x=>weight a x v w*f (xor a x)

def coeff (a x : Word n) (v w : AlgebraicComplex) : AlgebraicComplex :=
  ∏i,if a i then (if x i then w/zetaEight else v) else 1

theorem translated (f : Signature AlgebraicComplex n) (a x : Word n) (v w : AlgebraicComplex) :
    normalized f a v w (xor a x)=coeff a x v w*localTwist a f x := by
  rw [normalized,xor_cancel_left,localTwist_apply,←mul_assoc]
  congr 1
  rw [weight,coeff,←Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  cases ha : a i <;> cases hx : x i <;>
    simp [AffinePhase.xor,ha,hx,zetaEight_ne_zero]

theorem coeff_nonzero (a x : Word n) (v w : AlgebraicComplex) (hv : v≠0) (hw : w≠0) :
    coeff a x v w≠0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases ha : a i <;> cases hx : x i <;> simp [ha,hx,hv,hw,zetaEight_ne_zero]

theorem inverse_coeff_affine (a : Word n) (v w : AlgebraicComplex)
    (hv : v≠0) (hw : w≠0) (fourth : v^4= -(w^4)) :
    Affine (fun x=>(coeff a x v w)⁻¹) := by
  have form : (fun x=>(coeff a x v w)⁻¹)=
      (fun x=>∏i,if a i then (if x i then (w/zetaEight)⁻¹ else v⁻¹) else 1) := by
    funext x
    simp only [coeff]
    rw [←Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro i _
    cases a i <;> cases x i <;> simp
  rw [form]
  apply F.affine_prod
  intro i
  cases ha : a i with
  | false =>
    simpa only [ha,Bool.false_eq_true,ite_false] using
      (affine_constant n 1)
  | true =>
    simp only [ha,ite_true]
    apply GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers i
      v⁻¹ (w/zetaEight)⁻¹ (inv_ne_zero hv)
    simp only [inv_pow,div_pow,zetaEight_pow_four]
    rw [fourth]
    simp [div_eq_mul_inv]

theorem translate_affine (a : Word n) : TwoTranslate.IsAffineMap (xor a) := by
  intro x y
  funext i
  simp only [AffinePhase.xor,origin]
  cases a i <;> cases x i <;> cases y i <;> rfl

theorem not_affine (f : Signature AlgebraicComplex n) (a : Word n) (v w : AlgebraicComplex)
    (hv : v≠0) (hw : w≠0) (fourth : v^4= -(w^4)) (bad : ¬Affine (localTwist a f)) :
    ¬Affine (normalized f a v w) := by
  intro good
  have h := (inverse_coeff_affine a v w hv hw fourth).mul
    (good.precompose (xor a) (translate_affine a))
  apply bad
  convert h using 1
  funext x
  rw [translated,←mul_assoc,inv_mul_cancel₀ (coeff_nonzero a x v w hv hw),one_mul]

theorem origin_nonzero (f : Signature AlgebraicComplex n) (a : Word n) (v w : AlgebraicComplex)
    (hw : w≠0) (supported : f a≠0) : normalized f a v w (origin n)≠0 := by
  rw [normalized,xor_origin]
  apply mul_ne_zero _ supported
  apply Finset.prod_ne_zero_iff.mpr
  intro i _
  cases ha : a i <;> simp [origin,ha,hw]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXOriginNormalizationPhase
end
