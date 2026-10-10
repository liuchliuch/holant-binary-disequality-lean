import Holant.Tractable.Scalars
import Holant.Kernel
import Mathlib.Data.List.Basic

/-!
Exact source-level product class, manuscript standard classes (lines 2073–2079).
A finite list records designated variables, allowing repeated variables and factors;
the empty list evaluates to one. Unary factors are nonzero as functions, but may
vanish on either bit. An inconsistent equality/disequality product evaluates to
zero. Zero is also explicitly included. No recognition or tractability is claimed.
-/

namespace Holant.Tractable

noncomputable section

inductive ProductFactor (n : ℕ) where
  | unary (port : Fin n) (values : Bool → AlgebraicComplex) (nonzero : values ≠ 0)
  | equality (left right : Fin n)
  | disequality (left right : Fin n)

namespace ProductFactor

variable {n : ℕ}

def eval : ProductFactor n → Signature AlgebraicComplex n
  | .unary j u _ => fun x => u (x j)
  | .equality j k => fun x => Signature.equality (x j) (x k)
  | .disequality j k => fun x => Signature.disequality (x j) (x k)

@[simp] theorem equality_repeated (j : Fin n) (x : Fin n → Bool) :
    (equality j j).eval x = 1 := by simp [eval, Signature.equality]

@[simp] theorem disequality_repeated (j : Fin n) (x : Fin n → Bool) :
    (disequality j j).eval x = 0 := by simp [eval, Signature.disequality]

end ProductFactor

/-- A literal finite product; list order is immaterial to its value but repetitions remain. -/
def productFormula {n : ℕ} (scale : AlgebraicComplex) (factors : List (ProductFactor n)) :
    Signature AlgebraicComplex n := fun x => scale * (factors.map (fun h => h.eval x)).prod

/-- The manuscript's product class `𝒫`, including zero and empty products. -/
def Product {n : ℕ} (f : Signature AlgebraicComplex n) : Prop :=
  f = 0 ∨ ∃ scale : AlgebraicComplex, scale ≠ 0 ∧
    ∃ factors : List (ProductFactor n), f = productFormula scale factors

@[simp] theorem product_zero (n : ℕ) : Product (0 : Signature AlgebraicComplex n) :=
  Or.inl rfl

theorem product_formula {n : ℕ} (c : AlgebraicComplex) (factors : List (ProductFactor n)) :
    Product (productFormula c factors) := by
  by_cases hc : c = 0
  · left
    subst c
    funext x
    simp [productFormula]
  · exact Or.inr ⟨c, hc, factors, rfl⟩

@[simp] theorem productFormula_nil (n : ℕ) (c : AlgebraicComplex) :
    productFormula c ([] : List (ProductFactor n)) = fun _ => c := by
  funext x
  simp [productFormula]

theorem product_constant (n : ℕ) (c : AlgebraicComplex) :
    Product (fun _ : Fin n → Bool => c) := by
  simpa using product_formula c ([] : List (ProductFactor n))

theorem product_factor {n : ℕ} (h : ProductFactor n) : Product h.eval := by
  convert product_formula 1 [h] using 1
  funext x
  simp [productFormula]

/-- Arbitrary unary factors, including zero, are genuinely in the product class. -/
theorem product_unary {n : ℕ} (j : Fin n) (u : Bool → AlgebraicComplex) :
    Product (fun x => u (x j)) := by
  by_cases hu : u = 0
  · subst u
    exact product_zero n
  · exact product_factor (.unary j u hu)

theorem product_equality {n : ℕ} (j k : Fin n) :
    Product (fun x => Signature.equality (K := AlgebraicComplex) (x j) (x k)) :=
  product_factor (.equality j k)

theorem product_disequality {n : ℕ} (j k : Fin n) :
    Product (fun x => Signature.disequality (K := AlgebraicComplex) (x j) (x k)) :=
  product_factor (.disequality j k)

theorem Product.scale {n : ℕ} {f : Signature AlgebraicComplex n} (hf : Product f)
    (c : AlgebraicComplex) : Product (fun x => c * f x) := by
  rcases hf with rfl | ⟨s, hs, factors, rfl⟩
  · left
    funext x
    simp
  · convert product_formula (c * s) factors using 1
    funext x
    simp [productFormula, mul_assoc]

/-- Shared variables across factors are permitted: pointwise products concatenate lists. -/
theorem Product.mul {n : ℕ} {f g : Signature AlgebraicComplex n}
    (hf : Product f) (hg : Product g) : Product (fun x => f x * g x) := by
  rcases hf with rfl | ⟨s, hs, fs, rfl⟩
  · left
    funext x
    simp
  rcases hg with rfl | ⟨t, ht, gs, rfl⟩
  · left
    funext x
    simp
  convert product_formula (s * t) (fs ++ gs) using 1
  funext x
  simp [productFormula, List.prod_append]
  ring

end
end Holant.Tractable
