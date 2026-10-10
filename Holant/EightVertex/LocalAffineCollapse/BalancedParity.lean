import Holant.EightVertex.LocalAffineCollapse.MatrixReduction
import Holant.Tractable.Conformal.MatrixSupport

/-! Exact complex parity/complement transport through a balanced Hadamard
matrix. All actions remain the original full ordered tensor-product sums. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false

theorem complex_diagonal_action {n : ℕ} (a b : ℂ) (f : Signature ℂ n) :
    Signature.coordinateAction (fun _ => complexDiagonal a b) f =
      fun x => (∏ j,if x j then b else a)*f x := by
  classical
  funext x
  unfold Signature.coordinateAction
  have hp (y : Fin n → Bool) :
      (∏ j,complexDiagonal a b (x j) (y j)) =
        (∏ j,if x j then b else a)*(if x=y then 1 else 0) := by
    calc
      _ = ∏ j,(if x j then b else a)*Signature.equality (x j) (y j) := by
        apply Finset.prod_congr rfl
        intro j _
        simp only [complexDiagonal,Signature.equality]
        split <;> simp_all
      _ = _ := by rw [Finset.prod_mul_distrib,Signature.prod_equality]
  simp only [hp]
  simp

theorem complex_flip_action {n : ℕ} (f : Signature ℂ n) :
    Signature.coordinateAction (fun _ => Signature.disequality) f =
      fun x => f (complementWord x) := by
  classical
  funext x
  unfold Signature.coordinateAction
  have hp (y : Fin n → Bool) :
      (∏ j,Signature.disequality (K:=ℂ) (x j) (y j)) =
        if complementWord x=y then 1 else 0 := by
    convert Signature.prod_equality (K:=ℂ) (complementWord x) y using 1
    apply Finset.prod_congr rfl
    intro j _
    cases hx : x j <;> cases y j <;>
      simp [Signature.disequality,Signature.equality,complementWord,hx]
  simp only [hp]
  simp

theorem complex_sign_action {n : ℕ} (f : Signature ℂ n) (x : Fin n → Bool) :
    Signature.coordinateAction (fun _ => complexDiagonal 1 (-1)) f x =
      (-1 : ℂ)^(Holant.weight x)*f x := by
  rw [complex_diagonal_action]
  congr 1
  have h (j : Fin n) : (if x j then (-1 : ℂ) else 1)=(-1)^(if x j then 1 else 0 : ℕ) := by
    cases x j <;> simp
  simp_rw [h]
  rw [Finset.prod_pow_eq_pow_sum]
  rfl

theorem even_sign_fixed {n : ℕ} (f : Signature ℂ n)
    (he : ∀x,Holant.weight x%2=1 → f x=0) :
    Signature.coordinateAction (fun _ => complexDiagonal 1 (-1)) f=f := by
  funext x
  rw [complex_sign_action,neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one (Holant.weight x) with h|h
  · rw [h]; simp
  · rw [h,he x h]; simp

theorem balanced_flip (a c : ℂ) :
    Kernel.mul (complexBalanced a c 1) Signature.disequality =
      Kernel.mul (complexDiagonal 1 (-1)) (complexBalanced a c 1) := by
  funext x y
  cases x <;> cases y <;>
    simp [Kernel.mul_apply,complexBalanced,complexMatrix,complexDiagonal,Signature.disequality]

theorem balanced_inverse_complement (T : ComplexBasis) (a c : ℂ)
    (hT : T.matrix=complexBalanced a c 1) (M : Signature ℂ 4)
    (hM : ∀x,Holant.weight x%2=1 → M x=0) :
    ∀x,T.symm.action M (complementWord x)=T.symm.action M x := by
  let H := T.symm.action M
  have hc : T.action (Signature.coordinateAction (fun _ => Signature.disequality) H)=M := by
    change Signature.coordinateAction (fun _ => T.matrix)
      (Signature.coordinateAction (fun _ => Signature.disequality) H)=M
    rw [Signature.coordinateAction_comp,hT,balanced_flip,←Signature.coordinateAction_comp]
    rw [←hT]
    change Signature.coordinateAction (fun _ => complexDiagonal 1 (-1))
      (T.action (T.symm.action M))=M
    rw [T.action_symm_action,even_sign_fixed M hM]
  have h := congrArg T.symm.action hc
  rw [T.symm_action_action] at h
  rw [complex_flip_action] at h
  exact congrFun h

end
end Holant.EightVertex.LocalAffineCollapse
