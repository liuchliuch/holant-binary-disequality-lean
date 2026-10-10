import Holant.Proofs.Hardness.PositiveDynamicSeparation
import Holant.Complexity.BinaryInterpolation.FormulaProducts
import Holant.Complexity.BinaryInterpolation.RingFormulaMachine

/-! Explicit, input-dependent stage and root formulas. The finite literal
alphabet is fixed by the original signature. Runtime powers are formula trees,
not newly supplied field constants or evaluator callbacks. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeFormulas
open Holant.Complexity.BinaryInterpolation
abbrev Labels := Fin 6
abbrev Formula := RingFormula Labels

def coefficients {K : Type*} [Field K] (a b c : K) : Labels → K :=
  ![a+b,b-a,c,-1,(2:K)⁻¹,1]

def A (n : ℕ) : Formula := .mul
  (.add ((.literal 0 : Formula).power n) (.mul (.literal 3) ((.literal 1 : Formula).power n))) (.literal 4)
def B (n : ℕ) : Formula := .mul
  (.add ((.literal 0 : Formula).power n) ((.literal 1 : Formula).power n)) (.literal 4)
def C (n : ℕ) : Formula := (.literal 2 : Formula).power n
def lam (n : ℕ) : Formula := A n
def mu (n : ℕ) : Formula := .add (B n) (C n)
def nu (n : ℕ) : Formula := .add (B n) (.mul (.literal 3) (C n))

def root (N m : ℕ) (ij : ℕ × ℕ) : Formula :=
  .mul (.mul ((lam N).power (m-ij.1-ij.2)) ((mu N).power ij.1)) ((nu N).power ij.2)
def desired (N m : ℕ) : Formula := (lam N).power m

variable {K : Type*} [Field K] (a b c : K)
@[simp] theorem eval_lam (n : ℕ) : (lam n).eval (coefficients a b c)=PositiveDynamicSeparation.lam a b n := by
  simp [lam,A,coefficients,RingFormula.eval,PositiveDynamicSeparation.lam,
    PositiveDynamicSeparation.chainA,sub_eq_add_neg,div_eq_mul_inv]
@[simp] theorem eval_mu (n : ℕ) : (mu n).eval (coefficients a b c)=PositiveDynamicSeparation.mu a b c n := by
  simp [mu,B,C,coefficients,RingFormula.eval,PositiveDynamicSeparation.mu,
    PositiveDynamicSeparation.chainB,div_eq_mul_inv]
@[simp] theorem eval_nu (n : ℕ) : (nu n).eval (coefficients a b c)=PositiveDynamicSeparation.nu a b c n := by
  simp [nu,B,C,coefficients,RingFormula.eval,PositiveDynamicSeparation.nu,
    PositiveDynamicSeparation.chainB,sub_eq_add_neg,div_eq_mul_inv]
@[simp] theorem eval_root (N m : ℕ) (ij : ℕ × ℕ) :
    (root N m ij).eval (coefficients a b c)=ThreeModeAnnihilator.mode m
      (PositiveDynamicSeparation.lam a b N) (PositiveDynamicSeparation.mu a b c N)
      (PositiveDynamicSeparation.nu a b c N) ij := by
  simp only [root,RingFormula.eval,RingFormula.eval_power,eval_lam,eval_mu,eval_nu]
  rfl
@[simp] theorem eval_desired (N m : ℕ) :
    (desired N m).eval (coefficients a b c)=(PositiveDynamicSeparation.lam a b N)^m := by
  simp [desired]
@[simp] theorem coefficient_unit : coefficients a b c 5=1 := rfl
@[simp] theorem coefficient_minus : coefficients a b c 3= -1 := rfl

@[simp] theorem size_lam (n : ℕ) : (lam n).size=4*n+7 := by
  simp [lam,A,RingFormula.size,RingFormula.size_power]; omega
@[simp] theorem size_mu (n : ℕ) : (mu n).size=6*n+7 := by
  simp [mu,B,C,RingFormula.size,RingFormula.size_power]; omega
@[simp] theorem size_nu (n : ℕ) : (nu n).size=6*n+9 := by
  simp [nu,B,C,RingFormula.size,RingFormula.size_power]; omega

theorem size_root_le (N m : ℕ) (ij : ℕ×ℕ) (hij : ij.1+ij.2≤m) :
    (root N m ij).size≤m*(6*N+10)+5 := by
  simp only [root,RingFormula.size,RingFormula.size_power,size_lam,size_mu,size_nu]
  have hs : m-ij.1-ij.2+ij.1+ij.2=m := by omega
  have hl : (m-ij.1-ij.2)*(4*N+7+1)≤(m-ij.1-ij.2)*(6*N+10) :=
    Nat.mul_le_mul_left _ (by omega)
  have hm : ij.1*(6*N+7+1)≤ ij.1*(6*N+10) := Nat.mul_le_mul_left _ (by omega)
  nlinarith

theorem size_desired_le (N m : ℕ) : (desired N m).size≤m*(6*N+10)+5 := by
  simp only [desired,RingFormula.size_power,size_lam]
  have h := Nat.mul_le_mul_left m (by omega : 4*N+7+1≤6*N+10)
  omega

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.PositiveDynamicProgrammeFormulas
