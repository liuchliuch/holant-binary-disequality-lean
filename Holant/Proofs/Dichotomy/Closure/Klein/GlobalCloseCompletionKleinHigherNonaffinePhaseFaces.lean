import Holant.Tractable.AffineOperations

/-! Coordinate-square phase reconstruction. Only the actual coordinate second
ratios are assumed constant; arbitrary third differences are derived by the
explicit quadratic reconstruction, not supplied by a classifier. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseFaces
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {n : ℕ}

def CoordinateConstant (f : Signature AlgebraicComplex n) : Prop :=
  ∀ z j k, secondRatio f z (basis j) (basis k) = mixedCoefficient f j k

theorem mixed_sq {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : CoordinateConstant f) (j k : Fin n) :
    mixedCoefficient f j k ^ 2 = 1 := by
  have hh := h (basis j) j k
  simp only [mixedCoefficient, secondRatio, origin_xor, AffinePhase.xor_self] at hh
  have hc := (div_eq_div_iff (mul_ne_zero (hf _) (hf _))
    (mul_ne_zero (hf _) (hf _))).mp hh
  simp only [mixedCoefficient, secondRatio, origin_xor, div_pow]
  apply (div_eq_one_iff_eq (pow_ne_zero _ (mul_ne_zero (hf _) (hf _)))).mpr
  linear_combination -hc

theorem firstRatio_translate {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : CoordinateConstant f) (z : Word n) (j k : Fin n) :
    f (xor (xor z (basis k)) (basis j)) / f (xor z (basis k)) =
      mixedCoefficient f j k * (f (xor z (basis j)) / f z) := by
  have hh := h z j k
  have hc := (div_eq_iff (mul_ne_zero (hf _) (hf _))).mp hh
  have hswap : xor (xor z (basis k)) (basis j) = xor (xor z (basis j)) (basis k) := by
    rw [xor_assoc, xor_comm (basis k) (basis j), ← xor_assoc]
  rw [hswap]
  field_simp [hf]
  linear_combination hc

/-- Hamming-weight induction reconstructs every first difference. -/
theorem firstRatio_word {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : CoordinateConstant f) (j : Fin n)
    (s : Finset (Fin n)) :
    f (xor (word s) (basis j)) / f (word s) =
      linearCoefficient f j * ∏ k ∈ s, mixedCoefficient f j k := by
  induction s using Finset.induction_on with
  | empty => simp [linearCoefficient]
  | @insert k s hk ih =>
    rw [word_insert s k hk, firstRatio_translate hf h, ih, Finset.prod_insert hk]
    simp only [mixedCoefficient]
    ring

/-- The insertion recurrence used to reconstruct the full-support normal form. -/
theorem value_insert {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : CoordinateConstant f) (j : Fin n)
    (s : Finset (Fin n)) (hj : j ∉ s) :
    f (word (insert j s)) = f (word s) * linearCoefficient f j *
      ∏ k ∈ s, mixedCoefficient f j k := by
  rw [word_insert s j hj]
  have hh := (div_eq_iff (hf (word s))).mp (firstRatio_word hf h j s)
  linear_combination hh

/-- The source's converse, including an actual `ZMod 4` quadratic witness. -/
theorem affine_of_coordinateConstant {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (h : CoordinateConstant f)
    (fourth : ∀ x, (f x / f (origin n)) ^ 4 = 1) : Affine f := by
  classical
  have ha : ∀ j : Fin n, ∃ q : ZMod 4, fourthRootPhase q = linearCoefficient f j := by
    intro j
    exact fourthRootPhase_surjective_of_pow_four (fourth (basis j))
  choose a ha using ha
  have hb : ∀ j k : Fin n, ∃ q : ZMod 4,
      (q = 0 ∨ q = 2) ∧ fourthRootPhase q = mixedCoefficient f j k := by
    intro j k
    exact evenPhase_of_sq_eq_one (mixed_sq hf h j k)
  choose b hb hphase using hb
  let Q : QuadraticPhase n := ⟨0, a, b, fun j k _ => hb j k⟩
  have hv (s : Finset (Fin n)) : f (word s) =
      f (origin n) * fourthRootPhase (Q.eval (word s)) := by
    induction s using Finset.induction_on_max with
    | empty => rw [quadratic_eval_word]; simp [Q]
    | insert j s hmax ih =>
      have hj : j ∉ s := by
        intro hj
        exact (lt_irrefl j) (hmax j hj)
      rw [value_insert hf h j s hj, ih, quadratic_eval_insert_max Q s j hj hmax,
        fourthRootPhase_add, fourthRootPhase_add, fourthRootPhase_sum]
      change _ = f (origin n) *
        (fourthRootPhase (Q.eval (word s)) * fourthRootPhase (a j) *
        ∏ k ∈ s, fourthRootPhase (b k j))
      simp_rw [ha, hphase, mixedCoefficient_comm f _ j]
      ring
  right
  refine ⟨f (origin n), hf _, AffineSystem.unconstrained n, Q, ?_⟩
  funext x
  let s : Finset (Fin n) := Finset.univ.filter (fun j => x j = true)
  have hs : word s = x := by
    funext j
    simp [word, s]
  simpa [affineFormula, hs] using hv s


theorem ratio_sq_of_squares {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (squares : ∀ x y, f x ^ 2 = f y ^ 2)
    (z u v : Word n) : secondRatio f z u v ^ 2 = 1 := by
  simp only [secondRatio,div_pow,mul_pow]
  rw [squares (xor (xor z u) v) z, squares (xor z u) z, squares (xor z v) z]
  exact div_self (mul_ne_zero (pow_ne_zero _ (hf _)) (pow_ne_zero _ (hf _)))

theorem diagonal_ratio {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (squares : ∀ x y, f x ^ 2 = f y ^ 2)
    (z u : Word n) : secondRatio f z u u = 1 := by
  simp only [secondRatio,xor_cancel_right]
  rw [← sq,← sq,squares z (xor z u)]
  exact div_self (pow_ne_zero _ (hf _))

/-- A full sign cube which is not affine has a coordinate square with even
phase parity. Its four Walsh coefficients therefore cannot have equal norms. -/
theorem positive_face {f : Signature AlgebraicComplex n}
    (hf : ∀ x, f x ≠ 0) (squares : ∀ x y, f x ^ 2 = f y ^ 2)
    (bad : ¬ Affine f) :
    ∃ z j k, j ≠ k ∧
      f (xor (xor z (basis j)) (basis k)) * f z =
        f (xor z (basis j)) * f (xor z (basis k)) := by
  classical
  by_contra none
  push_neg at none
  apply bad
  apply affine_of_coordinateConstant hf
  · intro z j k
    by_cases same : j = k
    · subst k
      rw [diagonal_ratio hf squares]
      exact (diagonal_ratio hf squares (origin n) (basis j)).symm
    · have neg (z : Word n) : secondRatio f z (basis j) (basis k) = -1 := by
        have sq := ratio_sq_of_squares hf squares z (basis j) (basis k)
        have opts := (sq_eq_sq_iff_eq_or_eq_neg.mp (show
          secondRatio f z (basis j) (basis k) ^ 2 = (1 : AlgebraicComplex)^2 by simpa using sq))
        apply opts.resolve_left
        intro one
        exact none z j k same ((div_eq_one_iff_eq (mul_ne_zero (hf _) (hf _))).mp one)
      rw [neg z]
      exact (neg (origin n)).symm
  · intro x
    have sq : (f x / f (origin n)) ^ 2 = 1 := by
      rw [div_pow,squares x (origin n)]
      exact div_self (pow_ne_zero _ (hf _))
    calc (f x / f (origin n)) ^ 4 = ((f x / f (origin n)) ^ 2)^2 := by ring
         _ = 1 := by rw [sq];norm_num


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffinePhaseFaces
end
