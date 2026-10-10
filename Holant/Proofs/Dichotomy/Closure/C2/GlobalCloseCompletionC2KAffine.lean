import Holant.Proofs.Dichotomy.Closure.Product.GlobalCloseCompletionProductAncestorAffine
import Holant.ReedMuller.AffinePatching.Walsh
import Holant.Tractable.KPresentation

/-! The fixed source K sends actual affine tensors to actual affine tensors.
Its Hadamard sum, fourth-root row phases, and sqrt-two scale are all retained;
this is a class theorem, not a physical gate or changed oracle resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2KAffine
open Holant Holant.Tractable
open Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open scoped BigOperators
namespace W
export Holant.ReedMuller.AffinePatching (hadamard walsh walshKernel walsh_affine)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false

def phase (b : Bool) : AlgebraicComplex := if b then imaginaryUnit else 1

theorem matrix_factor (a b : Bool) : KMatrix a b=sqrtTwo⁻¹*phase a*W.hadamard a b := by
  cases a <;> cases b <;> simp [KMatrix,phase,W.hadamard,div_eq_mul_inv] <;> ring

theorem phase_affine {n : ℕ} (i : Fin n) : Affine (fun x : Fin n→Bool=>phase (x i)) :=
  GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers i 1 imaginaryUnit one_ne_zero
    (by simp [imaginaryUnit_pow_four])

theorem sourceK_formula {n : ℕ} (f : Signature AlgebraicComplex n) :
    sourceKBasis.action f=fun x=>sqrtTwo⁻¹^n*((∏i,phase (x i))*W.walsh f x) := by
  funext x
  simp only [InvertibleKernel.action,sourceKBasis,Signature.coordinateAction,matrix_factor,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,W.walsh,W.walshKernel]
  rw [Finset.mul_sum,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem sourceK_affine {n : ℕ} (f : Signature AlgebraicComplex n) (hf : Affine f) :
    Affine (sourceKBasis.action f) := by
  have phases : Affine (fun x : Fin n→Bool=>∏i,phase (x i)) := by
    simpa using Holant.ReedMuller.AffinePatching.affine_finset_prod Finset.univ
      (fun i x=>phase (x i)) (fun i _=>phase_affine i)
  have h := (phases.mul (W.walsh_affine f hf)).scale (sqrtTwo⁻¹^n)
  rw [sourceK_formula]
  exact h

def inversePhase (b : Bool) : AlgebraicComplex := if b then -imaginaryUnit else 1

theorem inverse_matrix_factor (a b : Bool) : KInverse a b=sqrtTwo⁻¹*W.hadamard a b*inversePhase b := by
  cases a <;> cases b <;> simp [KInverse,inversePhase,W.hadamard,div_eq_mul_inv] <;> ring

theorem inversePhase_affine {n : ℕ} (i : Fin n) : Affine (fun x : Fin n→Bool=>inversePhase (x i)) :=
  GlobalCloseCompletionProductAncestorAffine.unary_of_equal_fourth_powers i 1 (-imaginaryUnit) one_ne_zero
    (by
      calc
        1^4=1 := one_pow 4
        _=imaginaryUnit^4 := imaginaryUnit_pow_four.symm
        _=(-imaginaryUnit)^4 := by ring)

theorem inverse_formula {n : ℕ} (f : Signature AlgebraicComplex n) :
    sourceKBasis.symm.action f=fun x=>sqrtTwo⁻¹^n*W.walsh (fun y=>(∏i,inversePhase (y i))*f y) x := by
  funext x
  simp only [InvertibleKernel.action,InvertibleKernel.symm,sourceKBasis,Signature.coordinateAction,inverse_matrix_factor,
    Finset.prod_mul_distrib,Finset.prod_const,Finset.card_univ,Fintype.card_fin,W.walsh,W.walshKernel]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

theorem inverse_affine {n : ℕ} (f : Signature AlgebraicComplex n) (hf : Affine f) :
    Affine (sourceKBasis.symm.action f) := by
  have phases : Affine (fun x : Fin n→Bool=>∏i,inversePhase (x i)) := by
    simpa using Holant.ReedMuller.AffinePatching.affine_finset_prod Finset.univ
      (fun i x=>inversePhase (x i)) (fun i _=>inversePhase_affine i)
  have h := (W.walsh_affine _ (phases.mul hf)).scale (sqrtTwo⁻¹^n)
  rw [inverse_formula]
  exact h

theorem sourceK_affine_iff {n : ℕ} (f : Signature AlgebraicComplex n) :
    Affine (sourceKBasis.action f) ↔ Affine f := by
  constructor
  · intro h
    simpa only [InvertibleKernel.symm_action_action] using inverse_affine _ h
  · exact sourceK_affine f


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2KAffine
end
