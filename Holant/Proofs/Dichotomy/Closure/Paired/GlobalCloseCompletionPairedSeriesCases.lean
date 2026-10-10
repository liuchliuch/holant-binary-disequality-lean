import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesChoice

/-! Complete equal-diagonal paired-matrix dispatch, including both literal
scalar powers. The surviving cap is one of four fixed physical choices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCases
open Holant
namespace C
export GlobalCloseCompletionPairedSeriesChoice (Read Cap upper)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K] [CharZero K]
variable (phi : K→+*ℂ) (B : Matrix Bool Bool K)
variable (nonzero : B false false≠0) (same : B true true=B false false) (det : B.det≠0)
include phi nonzero same det in
theorem choose : (B false true=0 ∧ B true false=0) ∨
    ((B^2) false false=0 ∧ (B^2) true true=0) ∨ C.Cap B := by
  classical
  by_cases upper : B false true=0
  · by_cases lower : B true false=0
    · exact Or.inl ⟨upper,lower⟩
    · right
      have trans := C.upper phi B.transpose nonzero same (by simpa using det) lower
      rcases trans with anti|cap
      · exact Or.inl (by simpa only [←Matrix.transpose_pow,Matrix.transpose_apply] using anti)
      · right
        obtain ⟨k,hk,swap,h0,h1,hi⟩:=cap
        refine ⟨k,hk,!swap,?_,?_,?_⟩
        · cases swap <;> simpa [C.Read,←Matrix.transpose_pow] using h0
        · cases swap <;> simpa [C.Read,←Matrix.transpose_pow] using h1
        · cases swap <;> simpa [C.Read,←Matrix.transpose_pow] using hi
  · exact Or.inr (C.upper phi B nonzero same det upper)

include same in
theorem diagonal_scalar (h0 : B false true=0) (h1 : B true false=0) :
    B=B false false • (1 : Matrix Bool Bool K) := by
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply,h0,h1,same]

include det in
theorem anti_square (h0 : B false false=0) (h1 : B true true=0) :
    B^2=(B false true*B true false) • (1 : Matrix Bool Bool K) ∧ B false true*B true false≠0 := by
  constructor
  · ext i j
    cases i <;> cases j <;> simp [pow_two,Matrix.mul_apply,Matrix.one_apply,h0,h1,mul_comm]
  · intro zero
    apply det
    rw [Holant.Complexity.BinaryInterpolation.det_entries,h0,h1,zero]
    ring

include det in
theorem fourth_scalar (h0 : (B^2) false false=0) (h1 : (B^2) true true=0) :
    B^4=((B^2) false true*(B^2) true false) • (1 : Matrix Bool Bool K) ∧
      (B^2) false true*(B^2) true false≠0 := by
  have hd : (B^2).det≠0 := by rw [Matrix.det_pow];exact pow_ne_zero _ det
  have h:=anti_square (B^2) hd h0 h1
  simpa only [←pow_mul,Nat.reduceMul] using h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPairedSeriesCases
end
