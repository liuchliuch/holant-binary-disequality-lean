import Holant.Tractable.SymmetricBinaryPullback.LocalAffine

/-! Genuine class information for the squared-row CSP source. A local-affine
row always has an affine pointwise square. This implication keeps the original
local-affine possibility; it never infers Affine for the unsquared row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentSquareClass
open Holant Holant.Tractable Holant.Tractable.SymmetricBinaryPullback
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000

theorem affine_coordinate_phase {n : ℕ} (j : Fin n) (q : ZMod 4) :
    Affine (fun x : Fin n → Bool=>if x j then fourthRootPhase q else 1) := by
  let Q : QuadraticPhase n := ⟨0,fun k=>if k=j then q else 0,
    fun _ _=>0,fun _ _ _=>Or.inl rfl⟩
  convert TwoTranslate.affine_quadratic_phase Q using 1
  funext x
  simp only [QuadraticPhase.eval,Q,zero_add,ite_mul,zero_mul,Finset.sum_ite_eq',
    Finset.mem_univ,ite_true,Finset.sum_const_zero,add_zero]
  cases x j <;> simp

theorem affine_inverse_twist_square {n : ℕ} (alpha : Fin n → Bool) :
    Affine (fun x : Fin n → Bool=>∏j,if alpha j && x j then -imaginaryUnit else 1) := by
  have h (s : Finset (Fin n)) :
      Affine (fun x : Fin n → Bool=>∏j∈s,if alpha j && x j then -imaginaryUnit else 1) := by
    induction s using Finset.induction_on with
    | empty => simpa using affine_constant n 1
    | @insert j s hj ih =>
        have hjphase : Affine (fun x : Fin n → Bool=>if alpha j && x j then -imaginaryUnit else 1) := by
          cases ha : alpha j
          · simpa using affine_constant n 1
          · simpa only [Bool.true_and,fourthRootPhase_three] using affine_coordinate_phase j 3
        simpa only [Finset.prod_insert hj] using hjphase.mul ih
  exact h Finset.univ

theorem localAffine_square {n : ℕ} {f : Signature AlgebraicComplex n} (hf : LocalAffine f) :
    Affine (fun x=>f x*f x) := by
  classical
  by_cases hz : f=0
  · subst f
    simpa only [Pi.zero_apply,zero_mul] using affine_constant n 0
  have exists_nonzero : ∃alpha,f alpha≠0 := by
    by_contra! h
    exact hz (funext h)
  obtain ⟨alpha,ha⟩ := exists_nonzero
  have ht := (hf alpha ha).mul (hf alpha ha)
  convert (affine_inverse_twist_square alpha).mul ht using 1
  funext x
  simp only [localTwist_apply]
  have cancel : (∏j,if alpha j && x j then -imaginaryUnit else 1)*
      (∏j,if alpha j && x j then zetaEight else 1)^2=1 := by
    rw [←Finset.prod_pow,←Finset.prod_mul_distrib]
    apply Finset.prod_eq_one
    intro j _
    cases alpha j <;> cases x j <;> norm_num [zetaEight_sq,←pow_two,imaginaryUnit_sq]
  calc
    f x*f x=1*(f x*f x) := (one_mul _).symm
    _=((∏j,if alpha j && x j then -imaginaryUnit else 1)*
        (∏j,if alpha j && x j then zetaEight else 1)^2)*(f x*f x) := by rw [cancel]
    _=_ := by ring

theorem affine_square {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Affine f) :
    Affine (fun x=>f x*f x) := hf.mul hf

theorem square_support {n : ℕ} (f : Signature AlgebraicComplex n) (x : Fin n → Bool) :
    f x*f x≠0 ↔ f x≠0 := by simp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentSquareClass
end
