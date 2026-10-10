import Holant.Tractable.TwoTranslate.Derivative

/-! Full-support phase averaging and affine-coordinate substitution. -/
namespace Holant.Tractable
noncomputable section
namespace TwoTranslate
open AffinePhase

/-- An arbitrary Z/4 exponent with vanishing third differences has the required
actual quadratic phase representation. -/
theorem affine_phase_of_thirdDifference {n : ℕ} (q : Word n → ZMod 4)
    (hq : ∀ z u v w, thirdDifference q z u v w = 0) :
    Affine (fun x => fourthRootPhase (q x)) := by
  apply affine_of_thirdTrivial (fun x => fourthRootPhase_ne_zero _)
  intro z u v w
  apply (thirdRatio_eq_one_iff (fun x => fourthRootPhase_ne_zero (q x)) z u v w).mpr
  have hh := hq z u v w
  have he : q (xor (xor (xor z u) v) w) + q (xor z u) + q (xor z v) + q (xor z w) =
      q (xor (xor z u) v) + q (xor (xor z u) w) + q (xor (xor z v) w) + q z := by
    apply sub_eq_zero.mp
    simpa only [thirdDifference, sub_add_eq_sub_sub] using hh
  simpa only [fourthRootPhase_add] using congrArg fourthRootPhase he

theorem affine_quadratic_phase {n : ℕ} (Q : QuadraticPhase n) :
    Affine (fun x => fourthRootPhase (Q.eval x)) :=
  affine_phase_of_thirdDifference Q.eval (quadratic_thirdDifference Q)

/-- The ordinary zero-or-one lift of a binary residue. -/
def bitLift (b : ZMod 2) : ZMod 4 := if b = 0 then 0 else 1

@[simp] theorem bitLift_zero : bitLift 0 = 0 := by simp [bitLift]
@[simp] theorem bitLift_one : bitLift 1 = 1 := by simp [bitLift]

theorem bitLift_dot_thirdDifference {n : ℕ} (a : Fin n → ZMod 2) (z u v w : Word n) :
    thirdDifference (fun x => bitLift (dot a x)) z u v w = 0 := by
  simp only [thirdDifference, dot_xor]
  generalize dot a z = b₀
  generalize dot a u = b₁
  generalize dot a v = b₂
  generalize dot a w = b₃
  fin_cases b₀ <;> fin_cases b₁ <;> fin_cases b₂ <;> fin_cases b₃ <;> decide

/-- Adjoining a parity phase preserves genuine affinity. -/
theorem affine_quadratic_add_parity {n : ℕ} (Q : QuadraticPhase n)
    (a : Fin n → ZMod 2) (t : ZMod 4) :
    Affine (fun x => fourthRootPhase (Q.eval x + t * bitLift (dot a x))) := by
  apply affine_phase_of_thirdDifference
  intro z u v w
  rw [thirdDifference_add, quadratic_thirdDifference, thirdDifference_mul_const,
    bitLift_dot_thirdDifference]
  simp

/-- A single, genuine affine equation over GF(2). -/
def oneEquation {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2) : AffineSystem n :=
  ⟨1, fun _ => a, fun _ => b⟩

@[simp] theorem oneEquation_holds {n : ℕ} (a : Fin n → ZMod 2) (b : ZMod 2)
    (x : Word n) : (oneEquation a b).Holds x ↔ dot a x = b := by
  simp [AffineSystem.Holds, oneEquation, dot]

theorem binary_cases (b : ZMod 2) : b = 0 ∨ b = 1 := by
  fin_cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

theorem fourth_cases (c : ZMod 4) : c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr rfl))

theorem phase_bracket_zero (b : ZMod 2) :
    (1 : AlgebraicComplex) + fourthRootPhase (evenLift b) = if b = 0 then 2 else 0 := by
  rcases binary_cases b with rfl | rfl <;> norm_num

theorem phase_bracket_two (b : ZMod 2) :
    (1 : AlgebraicComplex) + fourthRootPhase (2 + evenLift b) = if b = 1 then 2 else 0 := by
  rcases binary_cases b with rfl | rfl <;> norm_num [fourthRootPhase_add]
  change (1 : AlgebraicComplex) + fourthRootPhase 0 = 2
  norm_num

theorem phase_bracket_one (b : ZMod 2) :
    (1 : AlgebraicComplex) + fourthRootPhase (1 + evenLift b) =
      (1 + imaginaryUnit) * fourthRootPhase ((-1 : ZMod 4) * bitLift b) := by
  rcases binary_cases b with rfl | rfl <;> simp [fourthRootPhase_add]
  rw [show (-1 : ZMod 4) = 3 from rfl, fourthRootPhase_three]
  linear_combination imaginaryUnit_sq

theorem phase_bracket_three (b : ZMod 2) :
    (1 : AlgebraicComplex) + fourthRootPhase (3 + evenLift b) =
      (1 - imaginaryUnit) * fourthRootPhase (bitLift b) := by
  rcases binary_cases b with rfl | rfl <;> simp [fourthRootPhase_add]
  · ring
  · linear_combination imaginaryUnit_sq

/-- Two translates of a full-support quadratic phase are affine, with cancellation
represented by the exact GF(2) support equation. -/
theorem affine_phase_two_translate {n : ℕ} (Q : QuadraticPhase n) (w : Word n) :
    Affine (fun x => fourthRootPhase (Q.eval x) + fourthRootPhase (Q.eval (xor x w))) := by
  obtain ⟨c, a, ha⟩ := quadratic_derivative Q w
  have hval (x : Word n) :
      fourthRootPhase (Q.eval x) + fourthRootPhase (Q.eval (xor x w)) =
      fourthRootPhase (Q.eval x) * (1 + fourthRootPhase (c + evenLift (dot a x))) := by
    have he : Q.eval (xor x w) = Q.eval x + (c + evenLift (dot a x)) := by
      linear_combination ha x
    rw [he, fourthRootPhase_add]
    ring
  simp_rw [hval]
  rcases fourth_cases c with rfl | rfl | rfl | rfl
  · convert affine_formula 2 (oneEquation a 0) Q using 1
    funext x
    simp only [zero_add, phase_bracket_zero, affineFormula, oneEquation_holds]
    split <;> simp_all [mul_comm]
  · convert (affine_quadratic_add_parity Q a (-1)).scale (1 + imaginaryUnit) using 1
    funext x
    rw [phase_bracket_one, fourthRootPhase_add]
    ring
  · convert affine_formula 2 (oneEquation a 1) Q using 1
    funext x
    simp only [phase_bracket_two, affineFormula, oneEquation_holds]
    split <;> simp_all [mul_comm]
  · convert (affine_quadratic_add_parity Q a 1).scale (1 - imaginaryUnit) using 1
    funext x
    rw [phase_bracket_three, fourthRootPhase_add]
    simp only [one_mul]
    ring

/-- An affine word map is a translated homomorphism of Boolean groups. -/
def IsAffineMap {m n : ℕ} (p : Word m → Word n) : Prop :=
  ∀ x y, p (xor x y) = xor (p x) (xor (p y) (p (origin m)))

/-- Quadratic phases remain exact affine phases under affine coordinates. -/
theorem affine_quadratic_precompose {m n : ℕ} (Q : QuadraticPhase n)
    (p : Word m → Word n) (hp : IsAffineMap p) :
    Affine (fun x => fourthRootPhase (Q.eval (p x))) := by
  apply affine_phase_of_thirdDifference
  intro z u v w
  unfold IsAffineMap at hp
  have hh := quadratic_thirdDifference Q (p z)
    (xor (p u) (p (origin m))) (xor (p v) (p (origin m)))
    (xor (p w) (p (origin m)))
  simpa only [thirdDifference, hp] using hh

end TwoTranslate
end
end Holant.Tractable
