import Holant.Tractable.AffineOperations
import Mathlib.Algebra.BigOperators.Ring.Finset

/-! Affine closure under a literal finite block sum. Every summed Boolean
coordinate is eliminated by the previously proved semantic summation rule. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

 def insertWord (m : ℕ) : (n : ℕ) → Word n → Word m → Word (m+n)
  | 0,_,x => x
  | n+1,y,x => Fin.cons (y 0) (insertWord m n (Fin.tail y) x)

 def sumVariables (m : ℕ) : (n : ℕ) → Signature AlgebraicComplex (m+n) → Signature AlgebraicComplex m
  | 0,f => f
  | n+1,f => sumVariables m n (fun x => f (Fin.cons false x)+f (Fin.cons true x))

 theorem sumVariables_affine (m n : ℕ) (f : Signature AlgebraicComplex (m+n))
    (hf : Affine f) : Affine (sumVariables m n f) := by
  induction n with
  | zero => exact hf
  | succ n ih => exact ih _ hf.sum_first

 def headTail (n : ℕ) : Word (n+1) ≃ Bool × Word n where
  toFun y := (y 0,Fin.tail y)
  invFun y := Fin.cons y.1 y.2
  left_inv y := by funext i;refine Fin.cases ?_ (fun j => ?_) i <;> rfl
  right_inv y := rfl

 theorem sumVariables_eq (m n : ℕ) (f : Signature AlgebraicComplex (m+n)) (x : Word m) :
    sumVariables m n f x=∑ y : Word n,f (insertWord m n y x) := by
  induction n with
  | zero => simp [sumVariables,insertWord]
  | succ n ih =>
    rw [sumVariables,ih]
    rw [←(headTail n).symm.sum_comp,Fintype.sum_prod_type,Fintype.sum_bool]
    simp only [headTail,Equiv.coe_fn_symm_mk,insertWord,Fin.cons_zero,Fin.tail_cons]
    simp only [Finset.sum_add_distrib]
    ac_rfl

 theorem affine_finset_prod {I : Type*} (s : Finset I) {n : ℕ}
    (f : I → Signature AlgebraicComplex n) (hf : ∀ i∈s,Affine (f i)) :
    Affine (fun x => ∏ i∈s,f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using affine_constant n 1
  | @insert i s hi ih =>
    have h := (hf i (Finset.mem_insert_self _ _)).mul
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))
    simpa [hi] using h

end
end Holant.ReedMuller.AffinePatching
