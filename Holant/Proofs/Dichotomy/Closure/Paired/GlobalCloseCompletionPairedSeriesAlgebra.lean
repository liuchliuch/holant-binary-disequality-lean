import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCore

/-! A nonsingular paired matrix has an actual positive power with both
diagonal entries nonzero, or an actual scalar equality power. No Jordan
normal form or four-boundary interpolation is needed for this reduction. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesAlgebra
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

theorem square00 (B : Matrix Bool Bool K) : (B^2) false false=B false false^2+B false true*B true false := by
  simp [pow_two,Matrix.mul_apply,Fintype.sum_bool]
  ring
theorem square11 (B : Matrix Bool Bool K) : (B^2) true true=B true true^2+B false true*B true false := by
  simp [pow_two,Matrix.mul_apply,Fintype.sum_bool]
  ring
theorem cube00 (B : Matrix Bool Bool K) : (B^3) false false=
    B false false^3+2*B false false*B false true*B true false+B false true*B true false*B true true := by
  simp [pow_succ,Matrix.mul_apply,Fintype.sum_bool]
  ring
theorem cube11 (B : Matrix Bool Bool K) : (B^3) true true=
    B true true^3+2*B true true*B false true*B true false+B false true*B true false*B false false := by
  simp [pow_succ,Matrix.mul_apply,Fintype.sum_bool]
  ring

theorem prepare (B : Matrix Bool Bool K) (det : B.det≠0) :
    (∃k : ℕ,0<k ∧ ∃c : K,c≠0 ∧ B^k=c • (1 : Matrix Bool Bool K)) ∨
    (∃k : ℕ,0<k ∧ (B^k) false false≠0 ∧ (B^k) true true≠0) := by
  have determinant:=Holant.Complexity.BinaryInterpolation.det_entries B
  by_cases h0 : B false false=0
  · have bc : B false true*B true false≠0 := by
      intro zero
      exact det (by rw [determinant,h0,zero_mul,zero,sub_self])
    by_cases h1 : B true true=0
    · left
      refine ⟨2,by decide,B false true*B true false,bc,?_⟩
      ext i j
      cases i <;> cases j <;> simp [pow_two,Matrix.mul_apply,Fintype.sum_bool,h0,h1,Matrix.one_apply,mul_comm]
    · right
      by_cases second : (B^2) true true=0
      · have eqn : B true true^2= -(B false true*B true false) := by rw [square11] at second;exact eq_neg_of_add_eq_zero_left second
        refine ⟨3,by decide,?_,?_⟩
        · rw [cube00,h0]
          simpa using mul_ne_zero bc h1
        · have value : (B^3) true true=B false true*B true false*B true true := by
            rw [cube11,h0,pow_succ,eqn]
            ring
          rw [value]
          exact mul_ne_zero bc h1
      · refine ⟨2,by decide,?_,second⟩
        rw [square00,h0]
        simpa using bc
  · by_cases h1 : B true true=0
    · have bc : B false true*B true false≠0 := by
        intro zero
        exact det (by rw [determinant,h1,mul_zero,zero,sub_self])
      right
      by_cases first : (B^2) false false=0
      · have eqn : B false false^2= -(B false true*B true false) := by rw [square00] at first;exact eq_neg_of_add_eq_zero_left first
        refine ⟨3,by decide,?_,?_⟩
        · have value : (B^3) false false=B false true*B true false*B false false := by
            rw [cube00,h1,pow_succ,eqn]
            ring
          rw [value]
          exact mul_ne_zero bc h0
        · rw [cube11,h1]
          simpa using mul_ne_zero bc h0
      · refine ⟨2,by decide,first,?_⟩
        rw [square11,h1]
        simpa using bc
    · exact Or.inr ⟨1,by decide,by simpa using h0,by simpa using h1⟩

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesAlgebra
end
