import Holant.Tractable.CommonTransform
import Holant.Tractable.AffineOperations

/-! Concrete binary matrix algebra used by source Lemma 6.28. -/
namespace Holant.Tractable.SymmetricBinaryPullback
noncomputable section

/-- The literal two-by-two determinant. -/
def determinant (E : Kernel AlgebraicComplex) : AlgebraicComplex :=
  E false false * E true true - E false true * E true false

@[simp] theorem determinant_equality :
    determinant (Signature.equality : Kernel AlgebraicComplex) = 1 := by
  norm_num [determinant, Signature.equality]

theorem determinant_mul (E F : Kernel AlgebraicComplex) :
    determinant (Kernel.mul E F) = determinant E * determinant F := by
  simp only [determinant, Kernel.mul_apply]
  ring

/-- The existing two-sided inverse witness implies the literal determinant is nonzero. -/
theorem determinant_ne_zero (E : InvertibleKernel) : determinant E.matrix ≠ 0 := by
  intro h
  have he := congrArg determinant E.matrix_inverse
  rw [determinant_mul, determinant_equality, h, zero_mul] at he
  exact zero_ne_one he

/-- The literal two-by-two adjugate, without any matrix-library conversion. -/
def adjugate (E : Kernel AlgebraicComplex) : Kernel AlgebraicComplex
  | false, false => E true true
  | false, true => -E false true
  | true, false => -E true false
  | true, true => E false false

/-- A nonzero determinant constructs the source's actual two-sided inverse.
Thus using `InvertibleKernel` does not strengthen the nonsingularity hypothesis. -/
def invertibleOfDeterminant (E : Kernel AlgebraicComplex) (hE : determinant E ≠ 0) :
    InvertibleKernel where
  matrix := E
  inverse := fun a b => adjugate E a b / determinant E
  matrix_inverse := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply, adjugate, Signature.equality]
    all_goals field_simp
    all_goals simp only [determinant]
    all_goals ring
  inverse_matrix := by
    funext a b
    cases a <;> cases b <;>
      simp [Kernel.mul_apply, adjugate, Signature.equality]
    all_goals field_simp
    all_goals simp only [determinant]
    all_goals ring

/-- Equivalence between the literal determinant criterion and a two-sided inverse. -/
theorem determinant_ne_zero_iff_invertible (E : Kernel AlgebraicComplex) :
    determinant E ≠ 0 ↔ ∃ B : InvertibleKernel, B.matrix = E := by
  constructor
  · intro hE
    exact ⟨invertibleOfDeterminant E hE, rfl⟩
  · rintro ⟨B, rfl⟩
    exact determinant_ne_zero B

/-- No nonsingularity or symmetry is needed for affine binary composition. -/
theorem affine_mul {E F : Kernel AlgebraicComplex}
    (hE : Affine (kernelSignature E)) (hF : Affine (kernelSignature F)) :
    Affine (kernelSignature (Kernel.mul E F)) := by
  have he := hE.precompose (fun x : Fin 3 → Bool => fun j => x ((![1, 0] : Fin 2 → Fin 3) j))
    (coordinates_isAffineMap (![1, 0] : Fin 2 → Fin 3))
  have hf := hF.precompose (fun x : Fin 3 → Bool => fun j => x ((![0, 2] : Fin 2 → Fin 3) j))
    (coordinates_isAffineMap (![0, 2] : Fin 2 → Fin 3))
  have h := (he.mul hf).sum_first
  convert h using 1
  funext x
  simp [kernelSignature, Kernel.mul_apply]
  rfl

/-- The affine part of Lemma 6.28, using genuine summation and multiplication. -/
theorem affine_pullback {E F : Kernel AlgebraicComplex}
    (hE : Affine (kernelSignature E)) (hF : Affine (kernelSignature F)) :
    Affine (kernelSignature (Kernel.mul (Kernel.mul E F) E)) :=
  affine_mul (affine_mul hE hF) hE

/-- Weighted diagonal binary matrix. -/
def diagonal (a c : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun x y => if x = y then (if x then c else a) else 0

/-- Weighted antidiagonal binary matrix. -/
def antidiagonal (b c : AlgebraicComplex) : Kernel AlgebraicComplex :=
  fun x y => if x ≠ y then (if x then c else b) else 0

end
end Holant.Tractable.SymmetricBinaryPullback
