import Holant.Proofs.AlgebraicRecognition.CommonFieldCheck


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
open Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic Polynomial
open scoped BigOperators

def relationCode {d : ℕ} (c : Vector d) : RationalPolynomialCode :=
  (d + 1, 1) :: List.ofFn (fun i : Fin (d + 1) => (i.val, -c i))

theorem polynomial_ofFn {n : ℕ} (t : Fin n → ℕ × ℚ) :
    RationalPolynomialCode.polynomial (List.ofFn t) =
      ∑ i, Polynomial.monomial (t i).1 (t i).2 := by
  induction n with
  | zero => simp [RationalPolynomialCode.polynomial]
  | succ n ih =>
    rw [List.ofFn_succ, RationalPolynomialCode.polynomial, ih, Fin.sum_univ_succ]

theorem relationCode_polynomial {d : ℕ} (c : Vector d) :
    (relationCode c).polynomial = PowerArithmetic.polynomial c := by
  rw [relationCode, RationalPolynomialCode.polynomial, polynomial_ofFn]
  simp only [← Polynomial.C_mul_X_pow_eq_monomial, Polynomial.C_1, one_mul,
    map_neg, neg_mul, Finset.sum_neg_distrib, PowerArithmetic.polynomial, sub_eq_add_neg]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonPrimitive
