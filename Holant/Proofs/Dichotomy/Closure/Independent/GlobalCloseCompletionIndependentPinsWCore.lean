import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZCore
import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCoordinates
import Holant.Tractable.SymmetricBinaryPullback.Basic

/-! A symmetric W tensor has a GHZ triangle whenever its repeated vector
has nonzero norm for the chosen bilinear edge. Either equality or retained Z
always has this property. All formulas use ordinary transpose, with no complex
conjugation. The roots here describe the output; they are not physical gates. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWCore
open Holant Holant.Tractable
open scoped BigOperators
namespace T
export GlobalCloseCompletionTernaryGHZCore (triangle action)
end T
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (ghz ghz_value)
end C
namespace B
export Holant.Tractable.SymmetricBinaryPullback (determinant determinant_ne_zero invertibleOfDeterminant)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option maxRecDepth 16384
set_option Elab.async false
variable {K : Type} [Field K]

private def words : Bool×Bool×Bool ≃ (Fin 3→Bool) where
  toFun x:=![x.1,x.2.1,x.2.2]
  invFun x:=(x 0,x 1,x 2)
  left_inv:=by intro x;rcases x with ⟨a,b,c⟩;rfl
  right_inv:=by intro x;funext i;fin_cases i <;> rfl

theorem coordinate (A : Kernel K) (f : Signature K 3) :
    Signature.coordinateAction (fun _=>A) f=T.action (Matrix.of A) f := by
  funext x
  unfold Signature.coordinateAction
  rw [←words.sum_comp]
  simp only [Fintype.sum_prod_type,words,Equiv.coe_fn_mk,T.action]
  simp [Fin.prod_univ_three,mul_assoc]

def w : Signature K 3 := fun x=>
  if x 0 then (if x 1 then 0 else if x 2 then 0 else 1)
  else if x 1 then (if x 2 then 0 else 1) else (if x 2 then 1 else 0)

def image (A : Kernel K) : Signature K 3 := fun x=>
  A (x 0) true*A (x 1) false*A (x 2) false+
  A (x 0) false*A (x 1) true*A (x 2) false+
  A (x 0) false*A (x 1) false*A (x 2) true

theorem image_eq (A : Kernel K) : image A=Signature.coordinateAction (fun _=>A) w := by
  funext x
  rw [coordinate]
  simp [image,w,T.action,Fintype.sum_bool]
  ring

def sign (t : K) (v : Bool) : K := if v then t else 1
def twist (t : K) (f : Signature K 3) : Signature K 3 := fun x=>sign t (x 1)*f x
def gram (t : K) (A : Kernel K) (i j : Bool) : K := A false i*A false j+t*A true i*A true j

def core (p q r : K) : Signature K 3 := fun x=>
  if x 0 then
    if x 1 then (if x 2 then p^3 else 2*p^2*q) else (if x 2 then 2*p^2*q else p*(p*r+3*q^2))
  else if x 1 then (if x 2 then 2*p^2*q else p*(p*r+3*q^2))
    else (if x 2 then p*(p*r+3*q^2) else 2*q*(3*p*r+q^2))

/-- One diagonal phase at each of the three internal triangle edges. -/
theorem triangle_image (t : K) (A : Kernel K) :
    T.triangle (twist t (image A))=T.action (Matrix.of A)
      (core (gram t A false false) (gram t A false true) (gram t A true true)) := by
  funext x
  simp [T.triangle,twist,sign,image,T.action,core,gram,Fintype.sum_bool]
  ring

theorem gram_determinant (t : K) (A : Kernel K) :
    gram t A false false*gram t A true true-gram t A false true^2=
      t*(A false false*A true true-A false true*A true false)^2 := by
  simp only [gram]
  ring

def columns (p q d c : K) : Kernel K
  | false,false=>c*(2*q+d)
  | false,true=>c*(2*q-d)
  | true,_=>c*p

theorem columns_determinant (p q d c : K) :
    columns p q d c false false*columns p q d c true true-
      columns p q d c false true*columns p q d c true false=2*c^2*p*d := by
  simp only [columns]
  ring

theorem core_ghz [CharZero K] (p q r d c : K)
    (square : d^2=p*r-q^2) (cube : c^3=(2:K)⁻¹) : core p q r=C.ghz (columns p q d c) := by
  funext x
  rw [C.ghz_value]
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;>
    simp only [core,columns,h0,h1,h2,Bool.false_eq_true,ite_false,ite_true]
  all_goals ring_nf
  all_goals rw [cube]
  all_goals try rw [square]
  all_goals ring

theorem choose_phase [CharZero K] (A : Kernel K)
    (det : A false false*A true true-A false true*A true false≠0) :
    ∃v : Bool,gram (if v then -1 else 1) A false false≠0 := by
  by_cases h : gram (1:K) A false false≠0
  · exact ⟨false,h⟩
  · refine ⟨true,?_⟩
    intro hz
    change gram (-1:K) A false false=0 at hz
    have hp : A false false^2=0 := by
      have h0 := not_not.mp h
      simp only [gram,one_mul,neg_one_mul] at h0 hz
      linear_combination (h0+hz)/2
    have hq : A true false^2=0 := by
      have h0 := not_not.mp h
      simp only [gram,one_mul,neg_one_mul] at h0 hz
      linear_combination (h0-hz)/2
    exact det (by rw [sq_eq_zero_iff.mp hp,sq_eq_zero_iff.mp hq];ring)

section Algebraic
variable (A : InvertibleKernel)

theorem roots (t : AlgebraicComplex) (ht : t≠0)
    (hp : gram t A.matrix false false≠0) :
    ∃d c : AlgebraicComplex,d≠0 ∧ c≠0 ∧
      d^2=gram t A.matrix false false*gram t A.matrix true true-gram t A.matrix false true^2 ∧
      c^3=(2:AlgebraicComplex)⁻¹ := by
  letI : IsAlgClosed AlgebraicComplex := IsAlgClosure.isAlgClosed ℚ
  obtain ⟨d,hd⟩:=IsAlgClosed.exists_pow_nat_eq
    (gram t A.matrix false false*gram t A.matrix true true-gram t A.matrix false true^2) (by decide : 0<2)
  obtain ⟨c,hc⟩:=IsAlgClosed.exists_pow_nat_eq ((2:AlgebraicComplex)⁻¹) (by decide : 0<3)
  refine ⟨d,c,?_,?_,hd,hc⟩
  · intro zero
    have determinant : gram t A.matrix false false*gram t A.matrix true true-gram t A.matrix false true^2≠0 := by
      rw [gram_determinant]
      exact mul_ne_zero ht (pow_ne_zero _ (B.determinant_ne_zero A))
    apply determinant
    rw [←hd,zero,zero_pow (by decide : 2≠0)]
  · intro zero
    rw [zero,zero_pow (by decide : 3≠0)] at hc
    exact (inv_ne_zero (by norm_num : (2:AlgebraicComplex)≠0)) hc.symm


end Algebraic
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsWCore
end
