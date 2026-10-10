import Holant.Projective.RootPolygon
import Holant.Kernel
import Mathlib.Tactic.LinearCombination

/-!
# Classification of actual complex binary pencils

Manuscript Lemma 6.10 (`lem:nd-root-pencil`). Matrices are literal ordered
Boolean kernels over `ℂ`. The sampled predicate inspects their four entries;
no common parity plane or endpoint normal form is assumed. Degree-two
interpolation derives the common plane from the sampled supports.

The dependent branch uses a genuine nontrivial linear relation, including
both possible zero endpoints. The complementary-axis identities hold for
all complex parameters. They make no gadget-realizability claim about the
analytic endpoints.
-/

noncomputable section
namespace Holant.Projective
open Polynomial

abbrev BinaryMat := Kernel ℂ

/-- The actual affine matrix pencil, with its scalar retained. -/
def binaryPencil (A B : BinaryMat) (t : ℂ) : BinaryMat := A + t • B

@[simp] theorem binaryPencil_apply (A B : BinaryMat) (t : ℂ) (i j : Bool) :
    binaryPencil A B t i j = A i j + t * B i j := rfl

/-- Ordered matrix units: `false` selects the first axis and `true` the second.
For even parity these are `E₀₀,E₁₁`; for odd parity they are `E₀₁,E₁₀`. -/
def parityAxis (p r : Bool) : BinaryMat :=
  fun i j => if i = r ∧ j = Bool.xor r p then 1 else 0

/-- Literal coordinates in one of the two monomial parity planes. -/
def parityCoordinates (p : Bool) (u v : ℂ) : BinaryMat :=
  u • parityAxis p false + v • parityAxis p true

/-- The four-entry source hypothesis: a nonsingular monomial matrix, with
second displayed axis divided by first in the fixed port orientation. -/
def IsRootMonomial (m : ℕ) (T : BinaryMat) : Prop :=
  (T false true = 0 ∧ T true false = 0 ∧
    T false false ≠ 0 ∧ T true true ≠ 0 ∧
    (T true true / T false false) ^ m = 1) ∨
  (T false false = 0 ∧ T true true = 0 ∧
    T false true ≠ 0 ∧ T true false ≠ 0 ∧
    (T true false / T false true) ^ m = 1)

/-- Genuine linear dependence; in particular either zero endpoint is covered. -/
def BinaryProportional (A B : BinaryMat) : Prop :=
  ∃ x y : ℂ, (x ≠ 0 ∨ y ≠ 0) ∧ x • A + y • B = 0

/-- A zero sampled matrix already supplies a nontrivial endpoint relation. -/
theorem binaryProportional_of_zero_sample {A B : BinaryMat} {t : ℂ}
    (h : binaryPencil A B t = 0) : BinaryProportional A B := by
  exact ⟨1, t, Or.inl one_ne_zero, by simpa [binaryPencil] using h⟩

/-- The dependence predicate is symmetric, including degenerate endpoints. -/
theorem binaryProportional_symm {A B : BinaryMat} (h : BinaryProportional A B) :
    BinaryProportional B A := by
  obtain ⟨x, y, hxy, h⟩ := h
  exact ⟨y, x, hxy.symm, by simpa [add_comm] using h⟩

/-- Equivalent familiar scalar-multiple formulation, with both directions
required so that a zero first endpoint is not accidentally excluded. -/
theorem binaryProportional_iff (A B : BinaryMat) :
    BinaryProportional A B ↔ (∃ s : ℂ, B = s • A) ∨ ∃ s : ℂ, A = s • B := by
  constructor
  · rintro ⟨x, y, hx | hy, h⟩
    · right
      refine ⟨-y / x, ?_⟩
      funext i j
      have hij := congrFun (congrFun h i) j
      change x * A i j + y * B i j = 0 at hij
      change A i j = (-y / x) * B i j
      field_simp
      linear_combination hij
    · left
      refine ⟨-x / y, ?_⟩
      funext i j
      have hij := congrFun (congrFun h i) j
      change x * A i j + y * B i j = 0 at hij
      change B i j = (-x / y) * A i j
      field_simp
      linear_combination hij
  · rintro (⟨s, rfl⟩ | ⟨s, rfl⟩)
    · refine ⟨-s, 1, Or.inr one_ne_zero, ?_⟩
      simp
    · refine ⟨1, -s, Or.inl one_ne_zero, ?_⟩
      simp

/-- Degree-two interpolation on the actual `m`-th roots, not on an assumed
set of three samples. -/
theorem quadratic_eq_zero_on_rootPolygon {m : ℕ} (hm : 3 ≤ m) (q : ℂ[X])
    (hdeg : q.natDegree ≤ 2)
    (hzero : ∀ t : ℂ, t ^ m = 1 → q.eval t = 0) : q = 0 := by
  classical
  let : NeZero m := ⟨by omega⟩
  apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q
    (Holant.Laurent.rootCoset m 1)
  · intro t ht
    obtain ⟨u, hu⟩ := (Holant.Laurent.mem_rootCoset m 1 t).mp ht
    have hu' : (↑u.val : ℂ) ^ m = 1 := by
      have h := u.property
      rw [mem_rootsOfUnity] at h
      exact congrArg Units.val h
    have hut : (↑u.val : ℂ) = t := by simpa using hu
    exact hzero t (hut ▸ hu')
  · rw [Holant.Laurent.card_rootCoset]
    omega

/-- Two affine entries whose product vanishes at every sample cannot both
be nonzero polynomials. This extracts fixed support from sampled support. -/
theorem affine_product_zero_on_rootPolygon {m : ℕ} (hm : 3 ≤ m)
    (a b c d : ℂ)
    (h : ∀ t : ℂ, t ^ m = 1 → (a + t * b) * (c + t * d) = 0) :
    (a = 0 ∧ b = 0) ∨ (c = 0 ∧ d = 0) := by
  have hlin (u v : ℂ) : (C u + C v * X : ℂ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa using natDegree_C_mul_X_pow_le v 1
  have hprod : ((C a + C b * X) * (C c + C d * X) : ℂ[X]) = 0 := by
    apply quadratic_eq_zero_on_rootPolygon hm
    · exact natDegree_mul_le.trans (by have := hlin a b; have := hlin c d; omega)
    · intro t ht
      simpa only [eval_mul, eval_add, eval_C, eval_X, mul_comm b t, mul_comm d t]
        using h t ht
  rcases mul_eq_zero.mp hprod with hzero | hzero
  · left
    have h0 := congrArg (fun q : ℂ[X] => q.coeff 0) hzero
    have h1 := congrArg (fun q : ℂ[X] => q.coeff 1) hzero
    simpa using And.intro h0 h1
  · right
    have h0 := congrArg (fun q : ℂ[X] => q.coeff 0) hzero
    have h1 := congrArg (fun q : ℂ[X] => q.coeff 1) hzero
    simpa using And.intro h0 h1

/-- Samples have no product between an even and an odd support entry. -/
theorem IsRootMonomial.cross_parity {m : ℕ} {T : BinaryMat}
    (h : IsRootMonomial m T) (i j : Bool) : T i i * T j (!j) = 0 := by
  rcases h with ⟨h01, h10, _⟩ | ⟨h00, h11, _⟩ <;>
    cases i <;> cases j <;> simp_all

/-- The common parity plane is a conclusion derived from all sampled supports.
This even includes proportional and identically zero pencils. -/
theorem binaryPencil_fixed_parity {m : ℕ} (hm : 3 ≤ m) (A B : BinaryMat)
    (hsamples : ∀ t : ℂ, t ^ m = 1 →
      binaryPencil A B t = 0 ∨ IsRootMonomial m (binaryPencil A B t)) :
    ∃ p : Bool, ∃ a b c d : ℂ,
      A = parityCoordinates p a c ∧ B = parityCoordinates p b d := by
  have hcross (i j : Bool) :
      (A i i = 0 ∧ B i i = 0) ∨ (A j (!j) = 0 ∧ B j (!j) = 0) := by
    apply affine_product_zero_on_rootPolygon hm
    intro t ht
    rcases hsamples t ht with hzero | hmono
    · have hi := congrFun (congrFun hzero i) i
      simp only [binaryPencil_apply, Pi.zero_apply] at hi
      rw [hi, zero_mul]
    · exact hmono.cross_parity i j
  by_cases hdiag : (A false false = 0 ∧ B false false = 0) ∧
      (A true true = 0 ∧ B true true = 0)
  · refine ⟨true, A false true, B false true, A true false, B true false, ?_, ?_⟩ <;>
      funext i j <;> cases i <;> cases j <;>
      simp_all [parityCoordinates, parityAxis]
  · have hoff (j : Bool) : A j (!j) = 0 ∧ B j (!j) = 0 := by
      rcases hcross false j with h0 | h
      · rcases hcross true j with h1 | h
        · exact (hdiag ⟨h0, h1⟩).elim
        · exact h
      · exact h
    have h01 := hoff false
    have h10 := hoff true
    refine ⟨false, A false false, B false false, A true true, B true true, ?_, ?_⟩ <;>
      funext i j <;> cases i <;> cases j <;>
      simp_all [parityCoordinates, parityAxis]

/-- The coordinates use the literal linear structure on matrices. -/
theorem parityCoordinates_linear_combination (p : Bool) (x y a b c d : ℂ) :
    x • parityCoordinates p a c + y • parityCoordinates p b d =
      parityCoordinates p (x * a + y * b) (x * c + y * d) := by
  funext i j
  cases p <;> cases i <;> cases j <;>
    simp [parityCoordinates, parityAxis]

/-- Exact endpoint dependence when the two coordinate columns have zero determinant. -/
theorem parityCoordinates_proportional_of_det_zero (p : Bool) (a b c d : ℂ)
    (hdet : a * d - b * c = 0) :
    BinaryProportional (parityCoordinates p a c) (parityCoordinates p b d) := by
  by_cases ha : a = 0
  · by_cases hc : c = 0
    · refine ⟨1, 0, Or.inl one_ne_zero, ?_⟩
      simp [parityCoordinates, ha, hc]
    · refine ⟨d, -c, Or.inr (neg_ne_zero.mpr hc), ?_⟩
      rw [parityCoordinates_linear_combination]
      have hfirst : d * a + -c * b = 0 := by linear_combination hdet
      have hsecond : d * c + -c * d = 0 := by ring
      rw [hfirst, hsecond]
      simp [parityCoordinates]
  · refine ⟨b, -a, Or.inr (neg_ne_zero.mpr ha), ?_⟩
    rw [parityCoordinates_linear_combination]
    have hfirst : b * a + -a * b = 0 := by ring
    have hsecond : b * c + -a * d = 0 := by linear_combination -hdet
    rw [hfirst, hsecond]
    simp [parityCoordinates]

/-- The fixed-plane coordinates of a sample are the actual affine endpoint
coefficients, with no projective rescaling at individual samples. -/
theorem binaryPencil_parityCoordinates (p : Bool) (a b c d t : ℂ) :
    binaryPencil (parityCoordinates p a c) (parityCoordinates p b d) t =
      parityCoordinates p (a + t * b) (c + t * d) := by
  funext i j
  cases p <;> cases i <;> cases j <;>
    simp [binaryPencil, parityCoordinates, parityAxis]

/-- A nonsingular sampled monomial in a fixed plane has precisely the ordered
ratio used by the source, rather than its reciprocal or a switched orientation. -/
theorem isRootMonomial_parityCoordinates_iff (m : ℕ) (p : Bool) (u v : ℂ) :
    IsRootMonomial m (parityCoordinates p u v) ↔
      u ≠ 0 ∧ v ≠ 0 ∧ (v / u) ^ m = 1 := by
  cases p <;> simp [IsRootMonomial, parityCoordinates, parityAxis]

/-- **Manuscript Lemma 6.10**, exact endpoint form. The source's hypothesis
alone derives a fixed plane and complementary rank-one analytic endpoints.
The first alternative is genuine linear dependence, including zero endpoints. -/
theorem binary_pencil_classification_endpoints {m : ℕ} (hm : 3 ≤ m)
    (A B : BinaryMat)
    (hsamples : ∀ t : ℂ, t ^ m = 1 →
      binaryPencil A B t = 0 ∨ IsRootMonomial m (binaryPencil A B t)) :
    BinaryProportional A B ∨
      ∃ p : Bool, ∃ lam α : ℂ, lam ≠ 0 ∧ α ^ m = 1 ∧
        ((A = lam • parityAxis p false ∧ B = (lam * α) • parityAxis p true) ∨
          (A = (lam * α) • parityAxis p true ∧ B = lam • parityAxis p false)) := by
  by_cases hprop : BinaryProportional A B
  · exact Or.inl hprop
  right
  obtain ⟨p, a, b, c, d, rfl, rfl⟩ := binaryPencil_fixed_parity hm A B hsamples
  have hmono (t : ℂ) (ht : t ^ m = 1) :
      a + t * b ≠ 0 ∧ c + t * d ≠ 0 ∧
        ((c + t * d) / (a + t * b)) ^ m = 1 := by
    rcases hsamples t ht with hzero | hmono
    · exact (hprop (binaryProportional_of_zero_sample hzero)).elim
    · rw [binaryPencil_parityCoordinates] at hmono
      exact (isRootMonomial_parityCoordinates_iff m p _ _).mp hmono
  have hdet : a * d - b * c ≠ 0 := by
    intro hd
    exact hprop (parityCoordinates_proportional_of_det_zero p a b c d hd)
  obtain ⟨α, hα, h | h⟩ := root_polygon_coefficients hm a b c d hdet
    (fun t ht => by simpa only [mul_comm b t] using (hmono t ht).1)
    (fun t ht => by
      simpa only [rootPolygon, Set.mem_ofPred_eq, mul_comm b t, mul_comm d t]
        using (hmono t ht).2.2)
  · obtain ⟨hb, hc, ha, hd⟩ := h
    refine ⟨p, a, α, ha, hα, Or.inl ⟨?_, ?_⟩⟩
    · simp [parityCoordinates, hc]
    · simp [parityCoordinates, hb, hd, mul_comm α a]
  · obtain ⟨ha, hd, hb, hc⟩ := h
    refine ⟨p, b, α, hb, hα, Or.inr ⟨?_, ?_⟩⟩
    · simp [parityCoordinates, ha, hc, mul_comm α b]
    · simp [parityCoordinates, hd]

/-- **Manuscript Lemma 6.10** (`lem:nd-root-pencil`). All actual root samples
are zero or nonsingular monomial binaries with the specified ordered ratio.
Then the endpoints are proportional, or the entire affine pencil has one
of the two exact complementary-axis forms with one fixed nonzero scalar.
The universal identity includes all analytic parameters, not only samples. -/
theorem binary_pencil_classification {m : ℕ} (hm : 3 ≤ m) (A B : BinaryMat)
    (hsamples : ∀ t : ℂ, t ^ m = 1 →
      binaryPencil A B t = 0 ∨ IsRootMonomial m (binaryPencil A B t)) :
    BinaryProportional A B ∨
      ∃ p : Bool, ∃ lam α : ℂ, lam ≠ 0 ∧ α ^ m = 1 ∧
        ((∀ t : ℂ, binaryPencil A B t =
          lam • (parityAxis p false + (α * t) • parityAxis p true)) ∨
        (∀ t : ℂ, binaryPencil A B t =
          lam • (t • parityAxis p false + α • parityAxis p true))) := by
  rcases binary_pencil_classification_endpoints hm A B hsamples with h | h
  · exact Or.inl h
  right
  obtain ⟨p, lam, α, hlam, hα, h | h⟩ := h
  · refine ⟨p, lam, α, hlam, hα, Or.inl ?_⟩
    obtain ⟨rfl, rfl⟩ := h
    intro t
    funext i j
    simp only [binaryPencil_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  · refine ⟨p, lam, α, hlam, hα, Or.inr ?_⟩
    obtain ⟨rfl, rfl⟩ := h
    intro t
    funext i j
    simp only [binaryPencil_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

end Holant.Projective
