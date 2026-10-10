import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryZeroPower
import Holant.Tractable.Anchor

/-! The two sourced independent-unary branches have different exact pin
coordinates. The perpendicular pair gives ordinary pins in its conformal
frame. The reflected isotropic pair gives opposite native pins in source-K
coordinates, with the same nonzero scalar on both. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsAlgebra
open Holant Holant.Tractable
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace U
export GeneralOddNonisotropicFrame (norm chart frame inverse chart_unary)
end U
namespace O
export GlobalCloseCompletionUnaryZeroPower (opposite)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option Elab.async false

section Perpendicular
variable {K : Type} [Field K]

theorem opposite_norm (u : Signature K 1) (hu : U.norm u≠0) :
    U.norm (fun x=>O.opposite u (x 0))=(U.norm u)⁻¹ := by
  calc
    _=(U.norm u)⁻¹*((U.norm u)⁻¹*U.norm u) := by
      simp only [U.norm,O.opposite,U.inverse,U.frame]
      ring
    _=(U.norm u)⁻¹ := by rw [inv_mul_cancel₀ hu,mul_one]

theorem opposite_nonisotropic (u : Signature K 1) (hu : U.norm u≠0) :
    U.norm (fun x=>O.opposite u (x 0))≠0 := by
  rw [opposite_norm u hu]
  exact inv_ne_zero hu

theorem chart_opposite (u : Signature K 1) (hu : U.norm u≠0) :
    U.chart u (fun x=>O.opposite u (x 0))=purePin 1 true 1 := by
  funext x
  have word : x=(fun _=>x 0) := by
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  rw [word,U.chart_unary]
  cases x 0 <;> simp only [U.frame,O.opposite,U.inverse,purePin,Bool.false_eq_true,
    Bool.true_eq_false,ite_false,ite_true,ne_eq,funext_iff,not_false_eq_true,implies_true,
    forall_const,one_mul]
  · ring
  · calc
      _=(U.norm u)⁻¹*U.norm u := by simp only [U.norm]; ring
      _=1 := inv_mul_cancel₀ hu

theorem perpendicular (u : Signature K 1) :
    u (fun _=>false)*O.opposite u false+u (fun _=>true)*O.opposite u true=0 := by
  simp only [O.opposite,U.inverse,U.frame]
  ring
end Perpendicular

def reflected (u : Signature AlgebraicComplex 1) : Signature AlgebraicComplex 1 :=
  fun x=>if x 0 then -u (fun _=>true) else u (fun _=>false)

theorem inverseK_unary (u : Signature AlgebraicComplex 1) (b : Bool) :
    sourceKBasis.symm.action u (fun _=>b)=
      (u (fun _=>false)+(if b then imaginaryUnit else -imaginaryUnit)*u (fun _=>true))/sqrtTwo := by
  unfold InvertibleKernel.action Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp only [Fin.prod_univ_one,Fintype.sum_bool]
  change sourceKBasis.inverse b true*u (fun _=>true)+
    sourceKBasis.inverse b false*u (fun _=>false)=_
  cases b <;> simp [sourceKBasis,InvertibleKernel.symm,KInverse] <;> ring

theorem inverseK_product (u : Signature AlgebraicComplex 1) :
    sourceKBasis.symm.action u (fun _=>false)*sourceKBasis.symm.action u (fun _=>true)=U.norm u/2 := by
  rw [inverseK_unary,inverseK_unary]
  simp only [Bool.false_eq_true,ite_false,ite_true]
  calc
    _=(u (fun _=>false)^2-imaginaryUnit^2*u (fun _=>true)^2)/sqrtTwo^2 := by ring
    _=U.norm u/2 := by rw [imaginaryUnit_sq,sqrtTwo_sq]; simp [U.norm]

theorem inverseK_reflected (u : Signature AlgebraicComplex 1) (b : Bool) :
    sourceKBasis.symm.action (reflected u) (fun _=>b)=sourceKBasis.symm.action u (fun _=>!b) := by
  rw [inverseK_unary,inverseK_unary]
  cases b <;> simp [reflected] <;> ring

theorem inverseK_nonzero (u : Signature AlgebraicComplex 1) (nonzero : u≠0) :
    sourceKBasis.symm.action u≠0 := by
  intro zero
  apply nonzero
  exact (Conformal.action_eq_zero_iff sourceKBasis.symm u).mp zero

/-- Both axes have the same coefficient, so their exact normalization can
be charged uniformly by the fixed-field source compiler. -/
theorem isotropic_axes (u : Signature AlgebraicComplex 1) (nonzero : u≠0) (isotropic : U.norm u=0) :
    ∃b : Bool,∃c : AlgebraicComplex,c≠0 ∧
      sourceKBasis.symm.action u=purePin c b 1 ∧
      sourceKBasis.symm.action (reflected u)=purePin c (!b) 1 := by
  have product : sourceKBasis.symm.action u (fun _=>false)*sourceKBasis.symm.action u (fun _=>true)=0 := by
    rw [inverseK_product,isotropic,zero_div]
  have live:=inverseK_nonzero u nonzero
  have word (x : Fin 1→Bool) : x=(fun _=>x 0) := by
    funext i
    exact congrArg x (Subsingleton.elim _ _)
  have not_both : ¬(sourceKBasis.symm.action u (fun _=>false)=0 ∧
      sourceKBasis.symm.action u (fun _=>true)=0) := by
    rintro ⟨h0,h1⟩
    apply live
    funext x
    rw [word x]
    cases x 0 <;> assumption
  rcases mul_eq_zero.mp product with h0|h1
  · refine ⟨true,sourceKBasis.symm.action u (fun _=>true),?_,?_,?_⟩
    · exact fun h1=>not_both ⟨h0,h1⟩
    · funext x
      rw [word x]
      cases x 0 <;> simp [purePin,funext_iff,h0]
    · funext x
      rw [word x,inverseK_reflected]
      cases x 0 <;> simp [purePin,funext_iff,h0]
  · refine ⟨false,sourceKBasis.symm.action u (fun _=>false),?_,?_,?_⟩
    · exact fun h0=>not_both ⟨h0,h1⟩
    · funext x
      rw [word x]
      cases x 0 <;> simp [purePin,funext_iff,h1]
    · funext x
      rw [word x,inverseK_reflected]
      cases x 0 <;> simp [purePin,funext_iff,h1]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsAlgebra
end
