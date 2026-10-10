import Holant.Tractable.LocalAffine
import Holant.Tractable.AffineOperations


namespace Holant.LocalDrafts.MainChain.LocalAffineTwists
open Holant.Tractable
noncomputable section

def phaseWeight {n : ℕ} (alpha x : Fin n → Bool) : AlgebraicComplex :=
  ∏ j, if alpha j && x j then zetaEight else 1

theorem phaseWeight_ne_zero {n : ℕ} (alpha x : Fin n → Bool) : phaseWeight alpha x ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro j _
  split_ifs
  · exact zetaEight_ne_zero
  · exact one_ne_zero

theorem localTwist_formula {n : ℕ} (alpha : Fin n → Bool) (f : Signature AlgebraicComplex n)
    (x : Fin n → Bool) : localTwist alpha f x=phaseWeight alpha x*f x := by
  classical
  unfold localTwist Signature.coordinateAction
  rw [Fintype.sum_eq_single x]
  · congr 1
    apply Finset.prod_congr rfl
    intro j _
    cases ha : alpha j <;> cases hx : x j <;>
      simp [localPhaseMatrix,phaseMatrix,Signature.equality,ha,hx]
  · intro y hy
    have hn : ∃ j, x j ≠ y j := by
      by_contra h
      push_neg at h
      exact hy (funext (fun j => (h j).symm))
    obtain ⟨j,hj⟩ := hn
    have hz : (∏ k, localPhaseMatrix (alpha k) (x k) (y k))=0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ j)
      cases ha : alpha j <;> simp [localPhaseMatrix,phaseMatrix,Signature.equality,ha,hj]
    rw [hz,zero_mul]

theorem localTwist_nonzero_iff {n : ℕ} (alpha x : Fin n → Bool)
    (f : Signature AlgebraicComplex n) : localTwist alpha f x ≠ 0 ↔ f x ≠ 0 := by
  rw [localTwist_formula]
  simp [phaseWeight_ne_zero]

def correctionPhase {n : ℕ} (alpha : Fin n → Bool) : QuadraticPhase n where
  constant := 0
  linear j := if alpha j then 3 else 0
  mixed _ _ := 0
  even_mixed _ _ _ := Or.inl rfl

def correction {n : ℕ} (alpha x : Fin n → Bool) : AlgebraicComplex :=
  ∏ j, if alpha j && x j then -imaginaryUnit else 1

theorem correction_formula {n : ℕ} (alpha x : Fin n → Bool) :
    correction alpha x=fourthRootPhase ((correctionPhase alpha).eval x) := by
  simp only [QuadraticPhase.eval,correctionPhase,zero_mul,ite_self,
    Finset.sum_const_zero,zero_add,add_zero,fourthRootPhase_sum]
  apply Finset.prod_congr rfl
  intro j _
  cases ha : alpha j <;> cases hx : x j <;>
    simp [bitValue,ha,hx]

theorem correction_affine {n : ℕ} (alpha : Fin n → Bool) : Affine (correction alpha) := by
  have h := affine_formula 1 (AffineSystem.unconstrained n) (correctionPhase alpha)
  have he : affineFormula 1 (AffineSystem.unconstrained n) (correctionPhase alpha)=correction alpha := by
    funext x
    simp [affineFormula,correction_formula]
  rwa [he] at h

theorem scalar_inverse_twist : (-imaginaryUnit)*zetaEight=zetaEight⁻¹ := by
  apply mul_right_cancel₀ zetaEight_ne_zero
  rw [inv_mul_cancel₀ zetaEight_ne_zero]
  calc
    (-imaginaryUnit)*zetaEight*zetaEight=(-imaginaryUnit)*zetaEight^2 := by ring
    _=1 := by rw [zetaEight_sq]; linear_combination -imaginaryUnit_sq

theorem correction_phase {n : ℕ} (alpha x : Fin n → Bool) :
    correction alpha x*phaseWeight alpha x=(phaseWeight alpha x)⁻¹ := by
  unfold correction phaseWeight
  rw [←Finset.prod_mul_distrib,←Finset.prod_inv_distrib]
  apply Finset.prod_congr rfl
  intro j _
  cases ha : alpha j <;> cases hx : x j <;>
    simp [ha,hx]
  simpa only [neg_mul] using scalar_inverse_twist

def inverseTwist {n : ℕ} (alpha : Fin n → Bool) (f : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex n := fun x => (phaseWeight alpha x)⁻¹*f x

theorem inverseTwist_affine {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : LocalAffine f) (alpha : Fin n → Bool) (ha : f alpha ≠ 0) :
    Affine (inverseTwist alpha f) := by
  have h := (correction_affine alpha).mul (hf alpha ha)
  convert h using 1
  funext x
  rw [localTwist_formula,←mul_assoc,correction_phase]
  rfl

/-- An explicit finite GF(2) support system is obtained from one fixed local
reference word and the defining affine formula, without a support oracle. -/
theorem support_system {n : ℕ} (f : Signature AlgebraicComplex n)
    (hf : LocalAffine f) (hn : f ≠ 0) :
    ∃ S : AffineSystem n, ∀ x, f x ≠ 0 ↔ S.Holds x := by
  classical
  obtain ⟨alpha,ha⟩ : ∃ alpha, f alpha ≠ 0 := by
    by_contra h
    push_neg at h
    exact hn (funext h)
  rcases hf alpha ha with hz | ⟨c,hc,S,Q,he⟩
  · have h := (localTwist_nonzero_iff alpha alpha f).mpr ha
    exact (h (by rw [hz]; rfl)).elim
  · refine ⟨S,?_⟩
    intro x
    rw [←localTwist_nonzero_iff alpha x f,he]
    simp [affineFormula,hc,fourthRootPhase_ne_zero]

end
end Holant.LocalDrafts.MainChain.LocalAffineTwists
