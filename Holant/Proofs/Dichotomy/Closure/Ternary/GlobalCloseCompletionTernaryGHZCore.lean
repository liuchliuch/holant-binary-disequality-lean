import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeCubicGadgets
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryProductTopPrime
import Mathlib.Tactic.LinearCombination

/-! Exact three-copy GHZ triangle coefficients. Local matrices are only a
semantic decomposition; the triangle itself uses three original vertices. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZCore
open Holant
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 400000
set_option Elab.async false
variable {K : Type} [Field K]

def ghz (A B C : Matrix Bool Bool K) : Signature K 3 := fun x=>
  ∑t : Bool,A (x 0) t*B (x 1) t*C (x 2) t

def triangle (f : Signature K 3) : Signature K 3 := fun x=>
  ∑i : Bool,∑j : Bool,∑k : Bool,f ![x 0,i,k]*f ![x 1,j,i]*f ![x 2,k,j]

def core (a b c d : K) : Signature K 3 := fun x=>
  if x 0 then
    if x 1 then (if x 2 then d^3 else b*c*d) else (if x 2 then b*c*d else a*b*c)
  else if x 1 then (if x 2 then b*c*d else a*b*c) else (if x 2 then a*b*c else a^3)

def action (A : Matrix Bool Bool K) (f : Signature K 3) : Signature K 3 := fun x=>
  ∑i : Bool,∑j : Bool,∑k : Bool,A (x 0) i*A (x 1) j*A (x 2) k*f ![i,j,k]

theorem ghz_value (A B C : Matrix Bool Bool K) (x : Fin 3→Bool) :
    ghz A B C x=A (x 0) false*B (x 1) false*C (x 2) false+
      A (x 0) true*B (x 1) true*C (x 2) true := by
  simp only [ghz,Fintype.sum_bool]
  ring

theorem triangle_value (A B C : Matrix Bool Bool K) :
    triangle (ghz A B C)=action A
      (core ((B.transpose*C) false false) ((B.transpose*C) false true)
        ((B.transpose*C) true false) ((B.transpose*C) true true)) := by
  funext x
  simp [triangle,action,ghz,core,Matrix.mul_apply,Fintype.sum_bool]
  ring

def cyclic (x : Fin 3→Bool) : Fin 3→Bool := ![x 1,x 2,x 0]

theorem triangle_cyclic (f : Signature K 3) (x : Fin 3→Bool) :
    triangle f (cyclic x)=triangle f x := by
  simp [triangle,cyclic,Fintype.sum_bool]
  ring

theorem triangle_swap (f : Signature K 3) (x : Fin 3→Bool) :
    triangle f ![x 1,x 0,x 2]=triangle f x := by
  have word : x=![x 0,x 1,x 2] := by funext i;fin_cases i <;> rfl
  rw [word]
  cases x 0 <;> cases x 1 <;> cases x 2 <;>
    simp [triangle,Fintype.sum_bool] <;> ring

theorem core_minors (a b c d : K) (det : a*d-b*c≠0)
    (first : a^3*(b*c*d)=(a*b*c)^2)
    (second : (a*b*c)*d^3=(b*c*d)^2)
    (outer : a^3*d^3=(a*b*c)*(b*c*d)) : a=0 ∧ d=0 := by
  have h1 : a^2*b*c*(a*d-b*c)=0 := by linear_combination first
  have h2 : b*c*d^2*(a*d-b*c)=0 := by linear_combination second
  have h3 : a*d*(a*d+b*c)*(a*d-b*c)=0 := by linear_combination outer
  have z1 : a^2*b*c=0 := (mul_eq_zero.mp h1).resolve_right det
  have z2 : b*c*d^2=0 := (mul_eq_zero.mp h2).resolve_right det
  by_cases bc : b*c=0
  · have ad : a*d≠0 := by intro zero;exact det (by rw [zero,bc,sub_self])
    have bad : a*d*(a*d)=0 := by
      have h: a*d*(a*d+b*c)=0 := (mul_eq_zero.mp h3).resolve_right det
      simpa only [bc,add_zero] using h
    exact False.elim ((mul_ne_zero ad ad) bad)
  · constructor
    · have : a^2=0 := (mul_eq_zero.mp (show a^2*(b*c)=0 by simpa only [mul_assoc] using z1)).resolve_right bc
      by_contra hn
      exact pow_ne_zero 2 hn this
    · have : d^2=0 := (mul_eq_zero.mp (show (b*c)*d^2=0 by exact z2)).resolve_left bc
      by_contra hn
      exact pow_ne_zero 2 hn this


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZCore
end
