import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.Sparse
import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonPrimitive.Checker


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
open Holant.LocalDrafts.EffectiveAlgebraic PowerArithmetic MvPolynomial
open scoped BigOperators
variable {n d m : ℕ}

abbrev Poly (n d : ℕ) := Sparse.Poly n (d + 1)

noncomputable def value (θ : ℂ) (p : Poly n d) : MvPolynomial (Fin n) ℂ :=
  (p.map (fun t => monomial (Sparse.exponent t.1) (decode θ t.2))).sum

@[simp] theorem value_nil (θ : ℂ) : value θ ([] : Poly n d) = 0 := rfl
@[simp] theorem value_cons (θ : ℂ) (t : Sparse.Term n (d+1)) (p : Poly n d) :
    value θ (t :: p) = monomial (Sparse.exponent t.1) (decode θ t.2) + value θ p := rfl
@[simp] theorem value_add (θ : ℂ) (p q : Poly n d) :
    value θ (Sparse.add p q) = value θ p + value θ q := by simp [value, Sparse.add]
@[simp] theorem value_neg (θ : ℂ) (p : Poly n d) :
    value θ (Sparse.neg p) = -value θ p := by
  induction p with
  | nil => simp [Sparse.neg]
  | cons t p ih =>
    change monomial (Sparse.exponent t.1) (decode θ (-t.2)) + value θ (Sparse.neg p) = _
    rw [map_neg, map_neg, ih, value_cons, neg_add]
@[simp] theorem value_sub (θ : ℂ) (p q : Poly n d) :
    value θ (Sparse.sub p q) = value θ p - value θ q := by
  simp [Sparse.sub, sub_eq_add_neg]

theorem value_termMul (θ : ℂ) (c : Vector d) (hr : θ^(d+1) = decode θ c)
    (t : Sparse.Term n (d+1)) (p : Poly n d) :
    value θ (Sparse.termMul (data c) t p) =
      monomial (Sparse.exponent t.1) (decode θ t.2) * value θ p := by
  induction p with
  | nil => simp [Sparse.termMul]
  | cons u p ih =>
    simp only [Sparse.termMul, List.map_cons, value_cons] at *
    rw [ih, Sparse.exponent_add, decode_mul θ c _ _ hr, mul_add, monomial_mul_monomial]

theorem value_mul (θ : ℂ) (c : Vector d) (hr : θ^(d+1) = decode θ c) (p q : Poly n d) :
    value θ (Sparse.mul (data c) p q) = value θ p * value θ q := by
  induction p with
  | nil => simp [Sparse.mul]
  | cons t p ih =>
    change value θ (Sparse.add (Sparse.termMul (data c) t q) (Sparse.mul (data c) p q)) = _
    rw [value_add, value_termMul θ c hr, ih, value_cons, add_mul]

@[simp] theorem value_one (θ : ℂ) (c : Vector d) :
    value θ (Sparse.one (v := n) (data c)) = 1 := by simp [Sparse.one, data]

theorem coefficient_value (θ : ℂ) (p : Poly n d) (a : Sparse.Exponent n) :
    (value θ p).coeff (Sparse.exponent a) = decode θ (Sparse.coefficient p a) := by
  induction p with
  | nil => simp [Sparse.coefficient_nil]
  | cons t p ih =>
    rw [value_cons, MvPolynomial.coeff_add, ih, Sparse.coefficient_cons, map_add]
    by_cases h : t.1 = a <;> simp [coeff_monomial, h, Sparse.exponent_eq]

/-- Check collected coefficient vectors at every literal support key. Repeated
keys and cancellation are allowed; testing raw records separately would be wrong. -/
def zeroCoefficients (p : Poly n d) : Bool :=
  p.all (fun t => CommonFieldCheck.zero (Sparse.coefficient p t.1))

theorem zeroCoefficients_iff (p : Poly n d) :
    zeroCoefficients p = true ↔ ∀ a, Sparse.coefficient p a = 0 := by
  simp only [zeroCoefficients, List.all_eq_true, CommonFieldCheck.zero, decide_eq_true_eq]
  constructor
  · intro h a
    by_cases ha : a ∈ p.map Prod.fst
    · obtain ⟨t, ht, rfl⟩ := List.mem_map.mp ha
      exact funext (h t ht)
    · exact Sparse.coefficient_of_not_mem p a ha
  · intro h t ht j
    exact congrFun (h t.1) j

theorem zeroCoefficients_sound (θ : ℂ) (p : Poly n d) (hp : zeroCoefficients p = true) :
    value θ p = 0 := by
  apply MvPolynomial.ext
  intro a
  have h := coefficient_value θ p (fun i => a i)
  simpa only [Sparse.exponent_coe, (zeroCoefficients_iff p).mp hp _, map_zero,
    AddMonoidAlgebra.coeff_zero,Finsupp.zero_apply] using h

/-- This converse is confined to a minimal-relation completeness witness. -/
theorem zeroCoefficients_complete (θ : ℂ) (c : Vector d)
    (hmin : PowerArithmetic.polynomial c = minpoly ℚ θ) (p : Poly n d) (hp : value θ p = 0) :
    zeroCoefficients p = true := by
  apply (zeroCoefficients_iff p).mpr
  intro a
  apply decode_injective θ c hmin
  rw [map_zero, ← coefficient_value, hp, AddMonoidAlgebra.coeff_zero]
  rfl

/-- Generic semantic interpretation, used also over AlgebraicComplex. -/
noncomputable def equation {K : Type*} [CommSemiring K] (w : Fin m → K) :
    EncodedSystem.Equation m n → MvPolynomial (Fin n) K
  | [] => 0
  | t :: ts => C (w t.1) * (∏ j, X j ^ t.2 j) + equation w ts

theorem equation_complex (w : Fin m → ℂ) (e : EncodedSystem.Equation m n) :
    equation w e = EncodedSystem.polynomial w e := by
  induction e with
  | nil => rfl
  | cons t ts ih => simp only [equation, EncodedSystem.polynomial, ih]

theorem map_equation {K L : Type*} [CommSemiring K] [CommSemiring L]
    (f : K →+* L) (w : Fin m → K) (e : EncodedSystem.Equation m n) :
    MvPolynomial.map f (equation w e) = equation (fun i => f (w i)) e := by
  induction e with
  | nil => simp [equation]
  | cons t ts ih => simp [equation, ih]

def materialize (a : Fin m → Vector d) (e : EncodedSystem.Equation m n) : Poly n d :=
  e.map (fun t => (t.2, a t.1))

theorem value_materialize (θ : ℂ) (a : Fin m → Vector d) (e : EncodedSystem.Equation m n) :
    value θ (materialize a e) = equation (fun i => decode θ (a i)) e := by
  have ht (t : EncodedSystem.Term m n) :
      monomial (Sparse.exponent t.2) (decode θ (a t.1)) =
        C (decode θ (a t.1)) * ∏ j, X j ^ t.2 j := by
    rw [MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (fun _ => pow_zero _)]
    rfl
  induction e with
  | nil => rfl
  | cons t ts ih =>
    change monomial (Sparse.exponent t.2) (decode θ (a t.1)) +
      value θ (materialize a ts) = _
    rw [ht,ih,equation]

def defect (c : Vector d) (e : Fin m → RationalPolynomialCode)
    (S : EncodedSystem.System m n) (H : Fin S.length → Poly n d) : Poly n d :=
  Sparse.sub ((List.ofFn (fun i : Fin S.length =>
    Sparse.mul (data c) (H i) (materialize (CommonFieldCheck.familyCoordinates c e) (S.get i)))).flatten)
    (Sparse.one (data c))

theorem value_flatten (θ : ℂ) (ps : List (Poly n d)) :
    value θ ps.flatten = (ps.map (value θ)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih =>
    change value θ (Sparse.add p ps.flatten) = value θ p + (ps.map (value θ)).sum
    rw [value_add, ih]

theorem value_defect (θ : ℂ) (c : Vector d) (hr : θ^(d+1) = decode θ c)
    (e : Fin m → RationalPolynomialCode) (w : Fin m → ℂ)
    (hw : ∀ i, decode θ (CommonFieldCheck.familyCoordinates c e i) = w i)
    (S : EncodedSystem.System m n) (H : Fin S.length → Poly n d) :
    value θ (defect c e S H) =
      (∑ i, value θ (H i) * equation w (S.get i)) - 1 := by
  rw [defect, value_sub, value_one, value_flatten]
  simp only [List.map_ofFn,List.sum_ofFn,Function.comp_def,
    value_mul θ c hr,value_materialize,funext hw]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NullstellensatzSearch
