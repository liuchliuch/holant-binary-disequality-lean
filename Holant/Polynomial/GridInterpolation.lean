import Mathlib.Combinatorics.Nullstellensatz
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Grid interpolation for bounded multivariate Laurent degree

This file formalizes manuscript Lemma 6.21 (`lem:nd-grid-interpolation`).
Laurent polynomials are the additive monoid algebra on finitely supported
integer exponent vectors, with their usual convolution multiplication.
A monomial shift is actual multiplication by a Laurent monomial; its being an
ordinary polynomial of coordinate degree at most two is an explicit hypothesis.
The nonzero complex parameters are represented by `ℂˣ`.
-/

noncomputable section

namespace Holant
namespace Laurent

/-- The ring of multivariate Laurent polynomials in `r` variables over `ℂ`. -/
abbrev Polynomial (r : ℕ) := AddMonoidAlgebra ℂ (Fin r →₀ ℤ)

/-- The natural inclusion of ordinary exponent vectors into integer exponent vectors. -/
def exponentInclusion (r : ℕ) : (Fin r →₀ ℕ) →+ (Fin r →₀ ℤ) :=
  Finsupp.mapRange.addMonoidHom Int.ofNatHom

/-- The ordinary polynomial ring embeds in the Laurent polynomial ring by preserving
coefficients and casting each exponent to an integer. -/
def ofPolynomial (r : ℕ) : MvPolynomial (Fin r) ℂ →+* Polynomial r :=
  AddMonoidAlgebra.mapDomainRingHom ℂ (exponentInclusion r)

/-- The exponent inclusion is injective. -/
theorem exponentInclusion_injective (r : ℕ) : Function.Injective (exponentInclusion r) := by
  intro a b h
  ext i
  exact Int.ofNat_injective (congrArg (fun d : Fin r →₀ ℤ => d i) h)

/-- Embedding ordinary polynomials preserves their coefficient information. -/
theorem ofPolynomial_injective (r : ℕ) : Function.Injective (ofPolynomial r) :=
  AddMonoidAlgebra.mapDomain_injective (exponentInclusion_injective r)

@[simp] theorem ofPolynomial_C (r : ℕ) (a : ℂ) :
    ofPolynomial r (MvPolynomial.C a) = AddMonoidAlgebra.single 0 a := by
  simp [ofPolynomial, MvPolynomial.C, MvPolynomial.monomial]

@[simp] theorem ofPolynomial_X (r : ℕ) (i : Fin r) :
    ofPolynomial r (MvPolynomial.X i) = AddMonoidAlgebra.single (Finsupp.single i 1) 1 := by
  simp [ofPolynomial, MvPolynomial.X, MvPolynomial.monomial, exponentInclusion]

/-- A Laurent monomial with coefficient one, allowing negative exponents. -/
def monomial {r : ℕ} (s : Fin r →₀ ℤ) : Polynomial r :=
  AddMonoidAlgebra.single s 1

/-- Evaluation of an integer exponent vector at nonzero complex coordinates. -/
def monomialCharacter {r : ℕ} (x : Fin r → ℂˣ) :
    Multiplicative (Fin r →₀ ℤ) →* ℂ where
  toFun s := ↑(∏ i, x i ^ s.toAdd i)
  map_one' := by simp
  map_mul' s t := by
    simp [zpow_add, Finset.prod_mul_distrib]

/-- Laurent evaluation is the algebra homomorphism sending each exponent vector
`s` to the finite product `∏ i, x i ^ s i`. -/
def eval {r : ℕ} (x : Fin r → ℂˣ) : Polynomial r →ₐ[ℂ] ℂ :=
  AddMonoidAlgebra.lift ℂ ℂ (Fin r →₀ ℤ) (monomialCharacter x)

/-- The finite Laurent sum at a complex tuple. On nonzero coordinates this
is the usual Laurent evaluation. The formula also uses Lean's totalized integer
powers at zero, but no such zero coordinate occurs in the interpolation grid. -/
def evalAt {r : ℕ} (x : Fin r → ℂ) (P : Polynomial r) : ℂ :=
  P.coeff.sum fun s a => a * ∏ i, x i ^ s i

/-- The algebra-homomorphism evaluation and the explicit finite Laurent sum agree. -/
theorem eval_eq_evalAt {r : ℕ} (x : Fin r → ℂˣ) (P : Polynomial r) :
    eval x P = evalAt (fun i => (x i : ℂ)) P := by
  simp [eval, AddMonoidAlgebra.lift_apply', evalAt, monomialCharacter]

@[simp] theorem eval_monomial {r : ℕ} (x : Fin r → ℂˣ) (s : Fin r →₀ ℤ) :
    eval x (monomial s) = ↑(∏ i, x i ^ s i) := by
  simp [eval, monomial, monomialCharacter]

/-- A Laurent monomial evaluates to a nonzero number on the algebraic torus. -/
theorem eval_monomial_ne_zero {r : ℕ} (x : Fin r → ℂˣ) (s : Fin r →₀ ℤ) :
    eval x (monomial s) ≠ 0 := by
  rw [eval_monomial]
  exact Units.ne_zero _

/-- Multiplying by a monomial preserves precisely the vanishing locus on nonzero
coordinates. -/
theorem eval_monomial_mul_eq_zero_iff {r : ℕ} (x : Fin r → ℂˣ)
    (s : Fin r →₀ ℤ) (P : Polynomial r) :
    eval x (monomial s * P) = 0 ↔ eval x P = 0 := by
  simp only [map_mul, mul_eq_zero, eval_monomial_ne_zero, false_or]

/-- The Laurent evaluation agrees with ordinary polynomial evaluation on
nonnegative exponents. -/
@[simp] theorem eval_ofPolynomial {r : ℕ} (x : Fin r → ℂˣ)
    (Q : MvPolynomial (Fin r) ℂ) :
    eval x (ofPolynomial r Q) = MvPolynomial.eval (fun i => (x i : ℂ)) Q := by
  have h : (eval x).toRingHom.comp (ofPolynomial r) =
      MvPolynomial.eval (fun i => (x i : ℂ)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [eval, monomialCharacter]
    · intro i
      simp [eval, monomialCharacter, Finsupp.single_apply]
  exact RingHom.congr_fun h Q

/-- Every coefficient-one Laurent monomial is invertible. -/
@[simp] theorem monomial_neg_mul {r : ℕ} (s : Fin r →₀ ℤ) :
    monomial (-s) * monomial s = 1 := by
  simp [monomial, ← AddMonoidAlgebra.one_def]

/-- A monomial shift does not destroy a nonzero Laurent polynomial. -/
theorem eq_zero_of_monomial_mul_eq_zero {r : ℕ} (s : Fin r →₀ ℤ)
    (P : Polynomial r) (h : monomial s * P = 0) : P = 0 := by
  have h' := congrArg (fun Q => monomial (-s) * Q) h
  simpa [← mul_assoc] using h'

/-- The coset `c μ_m`, considered as a finite set of complex numbers. -/
def rootCoset (m : ℕ) [NeZero m] (c : ℂˣ) : Finset ℂ := by
  letI := Fintype.ofFinite (rootsOfUnity m ℂ)
  exact Finset.univ.image fun z : rootsOfUnity m ℂ => (↑(c * z.val) : ℂ)

@[simp] theorem mem_rootCoset (m : ℕ) [NeZero m] (c : ℂˣ) (x : ℂ) :
    x ∈ rootCoset m c ↔ ∃ z : rootsOfUnity m ℂ, (↑(c * z.val) : ℂ) = x := by
  classical
  simp [rootCoset]

/-- Scaling the complex `m`-th roots of unity by a nonzero number preserves
all `m` distinct points. -/
@[simp] theorem card_rootCoset (m : ℕ) [NeZero m] (c : ℂˣ) :
    (rootCoset m c).card = m := by
  classical
  let := Fintype.ofFinite (rootsOfUnity m ℂ)
  have hinj : Function.Injective (fun z : rootsOfUnity m ℂ => (↑(c * z.val) : ℂ)) := by
    intro a b h
    apply Subtype.ext
    exact mul_left_cancel (Units.val_injective h)
  rw [rootCoset, Finset.card_image_of_injective _ hinj, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, Complex.card_rootsOfUnity]

/-- The ordinary polynomial interpolation core, with the complete complex
root-of-unity coset grid rather than an abstract cardinality assumption. -/
theorem polynomial_eq_zero_of_coset_grid {r m : ℕ} (hm : 3 ≤ m)
    (c : Fin r → ℂˣ) (Q : MvPolynomial (Fin r) ℂ)
    (hdeg : ∀ i, Q.degreeOf i ≤ 2)
    (hvanish : ∀ z : Fin r → rootsOfUnity m ℂ,
      MvPolynomial.eval (fun i => (↑(c i * (z i).val) : ℂ)) Q = 0) : Q = 0 := by
  classical
  let : NeZero m := ⟨by omega⟩
  apply MvPolynomial.eq_zero_of_eval_zero_at_prod_finset Q (fun i => rootCoset m (c i))
  · intro i
    rw [card_rootCoset]
    exact lt_of_le_of_lt (hdeg i) (by omega)
  · intro x hx
    have hx' : ∀ i, ∃ z : rootsOfUnity m ℂ, (↑(c i * z.val) : ℂ) = x i := by
      intro i
      exact (mem_rootCoset m (c i) (x i)).mp (hx i)
    choose z hz using hx'
    simpa only [hz] using hvanish z

/-- **Manuscript Lemma 6.21** (`lem:nd-grid-interpolation`), with an explicit
monomial shift into an ordinary polynomial of coordinate degree at most two.
No positivity assumption on the number `r` of variables is required. -/
theorem eq_zero_of_coset_grid {r m : ℕ} (hm : 3 ≤ m)
    (c : Fin r → ℂˣ) (P : Polynomial r)
    (hbounded : ∃ (s : Fin r →₀ ℤ) (Q : MvPolynomial (Fin r) ℂ),
      monomial s * P = ofPolynomial r Q ∧ ∀ i, Q.degreeOf i ≤ 2)
    (hvanish : ∀ z : Fin r → rootsOfUnity m ℂ,
      eval (fun i => c i * (z i).val) P = 0) : P = 0 := by
  obtain ⟨s, Q, hshift, hdeg⟩ := hbounded
  have hQ : Q = 0 := polynomial_eq_zero_of_coset_grid hm c Q hdeg (by
    intro z
    rw [← eval_ofPolynomial]
    rw [← hshift, map_mul, hvanish z, mul_zero])
  apply eq_zero_of_monomial_mul_eq_zero s P
  simpa [hQ] using hshift

/-- A literal complex-coordinate version of manuscript Lemma 6.21. Coset
membership is expressed by an `m`-th root `z` satisfying `z ^ m = 1`, and
all coset scales are assumed nonzero explicitly. -/
theorem eq_zero_of_complex_coset_grid {r m : ℕ} (hm : 3 ≤ m)
    (c : Fin r → ℂ) (hc : ∀ i, c i ≠ 0) (P : Polynomial r)
    (hbounded : ∃ (s : Fin r →₀ ℤ) (Q : MvPolynomial (Fin r) ℂ),
      monomial s * P = ofPolynomial r Q ∧ ∀ i, Q.degreeOf i ≤ 2)
    (hvanish : ∀ x : Fin r → ℂ,
      (∀ i, ∃ z : ℂ, z ^ m = 1 ∧ x i = c i * z) → evalAt x P = 0) : P = 0 := by
  apply eq_zero_of_coset_grid hm (fun i => Units.mk0 (c i) (hc i)) P hbounded
  intro z
  rw [eval_eq_evalAt]
  apply hvanish
  intro i
  refine ⟨↑((z i).val), ?_, by simp⟩
  have hz := (z i).property
  rw [mem_rootsOfUnity] at hz
  exact congrArg Units.val hz

end Laurent
end Holant
