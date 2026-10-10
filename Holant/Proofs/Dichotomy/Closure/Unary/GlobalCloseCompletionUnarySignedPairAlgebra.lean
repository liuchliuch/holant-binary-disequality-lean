import Holant.Proofs.Dichotomy.Closure.Paired.GlobalCloseCompletionPairedSeriesCore
import Mathlib.Tactic.LinearCombination

/-! Exact signed-pair algebra. Squaring removes the signs except at one
explicit determinant exception; that exception has full matrix support and
can be corrected with a genuine weighted-antidiagonal graph. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairAlgebra
open Holant
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1100000
set_option Elab.async false
variable {K : Type} [Field K]

def row (B : Matrix Bool Bool K) (e₀ e₁ : Bool) : Signature K 4 := fun x=>
  if x 1=Bool.xor (x 0) e₀ ∧ x 3=Bool.xor (x 2) e₁ then B (x 0) (x 2) else 0

def square (B : Matrix Bool Bool K) (e₀ e₁ : Bool) : Matrix Bool Bool K :=
  fun a b=>B (Bool.xor a e₀) (Bool.xor b e₁)^2

theorem square_value (B : Matrix Bool Bool K) (e₀ e₁ : Bool) (x : Fin 4→Bool) :
    (∑u : Bool,∑v : Bool,row B e₀ e₁ ![u,x 0,v,x 2]*row B e₀ e₁ ![u,x 1,v,x 3])=
      row (square B e₀ e₁) false false x := by
  cases e₀ <;>cases e₁ <;>cases h0 : x 0 <;>cases h1 : x 1 <;>
    cases h2 : x 2 <;>cases h3 : x 3 <;>simp [row,square,Fintype.sum_bool,h0,h1,h2,h3,pow_two]

theorem square_det (B : Matrix Bool Bool K) (e₀ e₁ : Bool) :
    (square B e₀ e₁).det=(if e₀=e₁ then 1 else -1)*B.det*
      (B false false*B true true+B false true*B true false) := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries,Holant.Complexity.BinaryInterpolation.det_entries]
  cases e₀ <;>cases e₁ <;>simp [square] <;>ring

theorem square_nonsingular (B : Matrix Bool Bool K) (e₀ e₁ : Bool)
    (det : B.det≠0) (sum : B false false*B true true+B false true*B true false≠0) :
    (square B e₀ e₁).det≠0 := by
  rw [square_det]
  exact mul_ne_zero (mul_ne_zero (by split_ifs <;>simp) det) sum

theorem exception_full (B : Matrix Bool Bool K) (det : B.det≠0)
    (sum : B false false*B true true+B false true*B true false=0) : ∀a b,B a b≠0 := by
  have ad : B false false*B true true≠0 := by
    intro zero
    have bc : B false true*B true false=0 := by simpa [zero] using sum
    exact det (by rw [Holant.Complexity.BinaryInterpolation.det_entries,zero,bc,sub_self])
  have bc : B false true*B true false≠0 := by
    intro zero
    exact ad (by simpa [zero] using sum)
  intro a b
  cases a <;>cases b
  · exact (mul_ne_zero_iff.mp ad).1
  · exact (mul_ne_zero_iff.mp bc).1
  · exact (mul_ne_zero_iff.mp bc).2
  · exact (mul_ne_zero_iff.mp ad).2

def anti (q : Bool→K) : Signature K 2 := fun x=>if x 1= !(x 0) then q (x 0) else 0

def flipSite (f : Signature K 4) (q : Bool→K) (i : Fin 4) : Signature K 4 :=
  fun x=>q (x i)*f (Function.update x i (!(x i)))
def corrected (B : Matrix Bool Bool K) (q : Bool→K) (e₀ e₁ : Bool) : Matrix Bool Bool K :=
  fun a b=>(if e₀ then q a else 1)*(if e₁ then q b else 1)*B a b

theorem corrected_value (B : Matrix Bool Bool K) (q : Bool→K) (e₀ e₁ : Bool) :
    (if e₁ then flipSite (if e₀ then flipSite (row B e₀ e₁) q 1 else row B e₀ e₁) q 3
      else if e₀ then flipSite (row B e₀ e₁) q 1 else row B e₀ e₁)=
      row (corrected B q e₀ e₁) false false := by
  funext x
  cases e₀ <;>cases e₁ <;>cases h0 : x 0 <;>cases h1 : x 1 <;>
    cases h2 : x 2 <;>cases h3 : x 3 <;>
      simp [row,flipSite,corrected,Function.update,h0,h1,h2,h3] <;>ring

theorem corrected_det (B : Matrix Bool Bool K) (q : Bool→K) (e₀ e₁ : Bool) :
    (corrected B q e₀ e₁).det=(if e₀ then q false*q true else 1)*
      (if e₁ then q false*q true else 1)*B.det := by
  rw [Holant.Complexity.BinaryInterpolation.det_entries,Holant.Complexity.BinaryInterpolation.det_entries]
  cases e₀ <;>cases e₁ <;>simp [corrected] <;>ring

theorem corrected_nonsingular (B : Matrix Bool Bool K) (q : Bool→K) (e₀ e₁ : Bool)
    (det : B.det≠0) (hq : ∀b,q b≠0) : (corrected B q e₀ e₁).det≠0 := by
  rw [corrected_det]
  apply mul_ne_zero _ det
  apply mul_ne_zero <;>split_ifs <;>simp [mul_ne_zero (hq false) (hq true)]


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnarySignedPairAlgebra
end
