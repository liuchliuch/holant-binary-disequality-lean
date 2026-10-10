import Holant.Tractable.SymmetricBinaryPullback.Basic
import Mathlib.Tactic.FinCases

/-! The equality/disequality normal forms for actual binary product formulas. -/
namespace Holant.Tractable.SymmetricBinaryPullback
noncomputable section

/-- The ordered binary table of a two-port signature. -/
def table (f : Signature AlgebraicComplex 2) : Kernel AlgebraicComplex :=
  fun a b => f ![a, b]

@[simp] theorem table_kernelSignature (E : Kernel AlgebraicComplex) :
    table (kernelSignature E) = E := by
  funext a b
  simp [table, kernelSignature]

/-- A binary product has diagonal support, antidiagonal support, or rank at most one. -/
def ProductShape (E : Kernel AlgebraicComplex) : Prop :=
  (E false true = 0 ∧ E true false = 0) ∨
  (E false false = 0 ∧ E true true = 0) ∨
  E false false * E true true = E false true * E true false

/-- Pointwise products preserve this concrete three-way alternative. -/
theorem productShape_mul {E F : Kernel AlgebraicComplex}
    (hE : ProductShape E) (hF : ProductShape F) :
    ProductShape (fun a b => E a b * F a b) := by
  rcases hE with hE | hE | hE
  · exact Or.inl ⟨by simp [hE.1], by simp [hE.2]⟩
  · exact Or.inr (Or.inl ⟨by simp [hE.1], by simp [hE.2]⟩)
  · rcases hF with hF | hF | hF
    · exact Or.inl ⟨by simp [hF.1], by simp [hF.2]⟩
    · exact Or.inr (Or.inl ⟨by simp [hF.1], by simp [hF.2]⟩)
    · right; right
      calc
        (E false false * F false false) * (E true true * F true true) =
            (E false false * E true true) * (F false false * F true true) := by ring
        _ = (E false true * E true false) * (F false true * F true false) := by rw [hE, hF]
        _ = (E false true * F false true) * (E true false * F true false) := by ring

/-- Every allowed factor is classified, including repeated ports. -/
theorem productFactor_shape (p : ProductFactor 2) : ProductShape (table p.eval) := by
  cases p with
  | unary j u hu =>
    right; right
    fin_cases j <;> simp [table, ProductFactor.eval, mul_comm]
  | equality j k =>
    fin_cases j <;> fin_cases k <;>
      simp [ProductShape, table, ProductFactor.eval, Signature.equality]
  | disequality j k =>
    fin_cases j <;> fin_cases k <;>
      simp [ProductShape, table, ProductFactor.eval, Signature.disequality]

/-- Induction on the actual finite list gives the binary product normal-form alternative. -/
theorem productFormula_shape (s : AlgebraicComplex) (ps : List (ProductFactor 2)) :
    ProductShape (table (productFormula s ps)) := by
  induction ps with
  | nil => right; right; simp [table, productFormula]
  | cons p ps ih =>
    have h := productShape_mul (productFactor_shape p) ih
    convert h using 1
    funext a b
    simp [table, productFormula]
    ring

theorem product_shape {E : Kernel AlgebraicComplex} (hE : Product (kernelSignature E)) :
    ProductShape E := by
  rcases hE with hz | ⟨s, hs, ps, he⟩
  · have he : E = fun _ _ => 0 := by
      have h := congrArg table hz
      rw [table_kernelSignature] at h
      exact h
    rw [he]
    left
    exact ⟨rfl, rfl⟩
  · have h := productFormula_shape s ps
    rw [← he, table_kernelSignature] at h
    exact h

/-- Nonsingularity removes the rank-one alternative. No symmetry is needed. -/
theorem product_monomial {E : Kernel AlgebraicComplex} (hE : Product (kernelSignature E))
    (hdet : determinant E ≠ 0) :
    (E false true = 0 ∧ E true false = 0) ∨
      (E false false = 0 ∧ E true true = 0) := by
  rcases product_shape hE with h | h | h
  · exact Or.inl h
  · exact Or.inr h
  · exact False.elim (hdet (sub_eq_zero.mpr h))

theorem product_diagonal (a c : AlgebraicComplex) : Product (kernelSignature (diagonal a c)) := by
  have h := (product_unary (0 : Fin 2) (fun b => if b then c else a)).mul
    (product_equality (0 : Fin 2) 1)
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature, diagonal, Signature.equality, h0, h1]

theorem product_antidiagonal (b c : AlgebraicComplex) :
    Product (kernelSignature (antidiagonal b c)) := by
  have h := (product_unary (0 : Fin 2) (fun x => if x then c else b)).mul
    (product_disequality (0 : Fin 2) 1)
  convert h using 1
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature, antidiagonal, Signature.disequality, h0, h1]

/-- Conversely the two support forms have actual unary/equality factor witnesses. -/
theorem product_of_monomial {E : Kernel AlgebraicComplex}
    (hE : (E false true = 0 ∧ E true false = 0) ∨
      (E false false = 0 ∧ E true true = 0)) : Product (kernelSignature E) := by
  rcases hE with hE | hE
  · have he : E = diagonal (E false false) (E true true) := by
      funext a b
      cases a <;> cases b <;> simp [diagonal, hE.1, hE.2]
    rw [he]
    exact product_diagonal _ _
  · have he : E = antidiagonal (E false true) (E true false) := by
      funext a b
      cases a <;> cases b <;> simp [antidiagonal, hE.1, hE.2]
    rw [he]
    exact product_antidiagonal _ _

/-- Actual matrix multiplication preserves diagonal/antidiagonal support. -/
theorem monomial_mul {E F : Kernel AlgebraicComplex}
    (hE : (E false true = 0 ∧ E true false = 0) ∨
      (E false false = 0 ∧ E true true = 0))
    (hF : (F false true = 0 ∧ F true false = 0) ∨
      (F false false = 0 ∧ F true true = 0)) :
    ((Kernel.mul E F) false true = 0 ∧ (Kernel.mul E F) true false = 0) ∨
      ((Kernel.mul E F) false false = 0 ∧ (Kernel.mul E F) true true = 0) := by
  rcases hE with hE | hE <;> rcases hF with hF | hF
  · left; simp [Kernel.mul_apply, hE.1, hE.2, hF.1, hF.2]
  · right; simp [Kernel.mul_apply, hE.1, hE.2, hF.1, hF.2]
  · right; simp [Kernel.mul_apply, hE.1, hE.2, hF.1, hF.2]
  · left; simp [Kernel.mul_apply, hE.1, hE.2, hF.1, hF.2]

/-- The product case of Lemma 6.28, stronger in not requiring symmetry. -/
theorem product_pullback (E F : InvertibleKernel)
    (hE : Product (kernelSignature E.matrix)) (hF : Product (kernelSignature F.matrix)) :
    Product (kernelSignature (Kernel.mul (Kernel.mul E.matrix F.matrix) E.matrix)) := by
  have he := product_monomial hE (determinant_ne_zero E)
  have hf := product_monomial hF (determinant_ne_zero F)
  exact product_of_monomial (monomial_mul (monomial_mul he hf) he)

end
end Holant.Tractable.SymmetricBinaryPullback
