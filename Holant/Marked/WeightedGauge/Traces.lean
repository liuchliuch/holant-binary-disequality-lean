import Holant.Marked.WeightedGauge.Flattening

/-! Literal trace pencils and protected-minor weights for the weighted kernels. -/
noncomputable section
namespace Holant.Marked.WeightedGauge
open scoped BigOperators
variable {K : Type*} [Field K]

def standardKernel (p : Bool) (t : K) : Kernel K :=
  fun a b => if (a ^^ b) = p then bitWeight t b else 0

def effectiveKernel (d : K) (p : Bool) (t : K) : Kernel K := Kernel.mul (diagonal d) (standardKernel p t)

theorem effectiveKernel_apply (d : K) (p : Bool) (t : K) (a b : Bool) :
    effectiveKernel d p t a b = if (a ^^ b) = p then bitWeight d a * bitWeight t b else 0 := by
  rw [effectiveKernel, diagonal_mul]
  simp [standardKernel]

theorem diagonal_substitution (d t : K) : effectiveKernel d false t = standardKernel false (d*t) := by
  funext a b; cases a <;> cases b <;> simp [effectiveKernel_apply, standardKernel, bitWeight]

theorem reflection_substitution (d t : K) (hd : d ≠ 0) :
    effectiveKernel d true t = d • standardKernel true (t/d) := by
  funext a b; cases a <;> cases b <;>
    simp [effectiveKernel_apply, standardKernel, bitWeight] <;> field_simp

/-- An ordered monomial factor retains both of its actual, possibly zero, coefficients. -/
def factor (p : Bool) (u v : K) : Kernel K :=
  fun a b => if (a ^^ b) = p then (if a then v else u) else 0

def traceConstant (d : K) (p reverse : Bool) (u v : K) : K :=
  if p then (if reverse then d*u else d*v) else u

def traceSlope (d : K) (p reverse : Bool) (u v : K) : K :=
  if p then (if reverse then v else u) else d*v

def phase (inverse : Bool) (t : K) : K := if inverse then t⁻¹ else t

/-- Actual Frobenius trace, including the reversed kernel and either phase orientation. -/
theorem trace_formula (d : K) (p reverse inverse : Bool) (u v t : K) :
    pairing (if reverse then Kernel.transpose (effectiveKernel d p (phase inverse t))
      else effectiveKernel d p (phase inverse t)) (factor p u v) =
      traceConstant d p reverse u v + traceSlope d p reverse u v * phase inverse t := by
  cases p <;> cases reverse <;>
    simp [pairing, Kernel.transpose, effectiveKernel_apply, factor, traceConstant, traceSlope, bitWeight] <;>
    ring

theorem traceCoefficients_ne_zero {d u v : K} (hd : d ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (p reverse : Bool) : traceConstant d p reverse u v ≠ 0 ∧ traceSlope d p reverse u v ≠ 0 := by
  cases p <;> cases reverse <;> simp [traceConstant, traceSlope, hd, hu, hv]

/-- The source's nonzero two-term trace form is derived from the actual two entries. -/
theorem trace_normal_form {d u v : K} (hd : d ≠ 0) (hu : u ≠ 0) (hv : v ≠ 0)
    (p reverse inverse : Bool) : ∃ k theta : K, k * theta ≠ 0 ∧ ∀ t : K,
      pairing (if reverse then Kernel.transpose (effectiveKernel d p (phase inverse t))
        else effectiveKernel d p (phase inverse t)) (factor p u v) = k * (1 + theta * phase inverse t) := by
  let A := traceConstant d p reverse u v
  let B := traceSlope d p reverse u v
  have ha : A ≠ 0 := (traceCoefficients_ne_zero hd hu hv p reverse).1
  have hb : B ≠ 0 := (traceCoefficients_ne_zero hd hu hv p reverse).2
  refine ⟨A, B/A, mul_ne_zero ha (div_ne_zero hb ha), ?_⟩
  intro t
  rw [trace_formula]
  change A + B * phase inverse t = A * (1 + B/A * phase inverse t)
  field_simp

/-- One supported monomial cannot introduce a forbidden nonzero phase. -/
theorem one_term_nonzero {A B t : K} (ht : t ≠ 0) (inverse : Bool) :
    ((A ≠ 0 ∧ B = 0) ∨ (A = 0 ∧ B ≠ 0)) → A + B * phase inverse t ≠ 0 := by
  rintro (⟨hA,rfl⟩ | ⟨rfl,hB⟩)
  · simpa using hA
  · cases inverse <;> simp [phase, hB, ht]

/-- An identically zero coefficient pair stays zero, independently of the other product. -/
theorem zero_trace (inverse : Bool) (t : K) : (0 : K) + 0 * phase inverse t = 0 := by simp

theorem at_most_one_forbidden {A B t u : K} (hB : B ≠ 0) (inverse : Bool)
    (ht : A+B*phase inverse t=0) (hu : A+B*phase inverse u=0) : t = u := by
  have hh : phase inverse t = phase inverse u :=
    mul_left_cancel₀ hB (add_left_cancel (ht.trans hu.symm))
  cases inverse
  · exact hh
  · exact inv_injective hh

/-- Equal-exponent terms either cancel identically or become a one-term trace. -/
theorem equal_exponent_trace (a b : K) (t : Kˣ) (e : ℤ) :
    a * (↑(t^e) : K) + b * (↑(t^e) : K) = (a+b) * (↑(t^e) : K) := by ring

theorem equal_exponent_zero_iff (a b : K) (t : Kˣ) (e : ℤ) :
    a * (↑(t^e) : K) + b * (↑(t^e) : K) = 0 ↔ a+b=0 := by
  rw [equal_exponent_trace]
  simp only [mul_eq_zero, Units.ne_zero (t^e), or_false]

/-- Literal supported edge entries are monomials in the gauge and phase units. -/
theorem supported_entry (d t : Kˣ) (p a b : Bool) (h : (a ^^ b) = p) :
    effectiveKernel (d : K) p (t : K) a b =
      (↑(d^(if a then 1 else 0 : ℤ) * t^(if b then 1 else 0 : ℤ)) : K) := by
  cases a <;> cases b <;> simp_all [effectiveKernel_apply, bitWeight]

def monomial (d t c : Kˣ) (a b : ℤ) : Kˣ := c*d^a*t^b

/-- The transported protected determinant has an explicit nonzero monomial multiplier. -/
theorem protected_minor_monomial (d t : Kˣ) (c0 c1 k0 k1 : Kˣ)
    (a0 a1 b0 b1 r0 r1 s0 s1 : ℤ) (M : Matrix Bool Bool K) :
    minor (fun i j =>
      (↑(if i then monomial d t c1 a1 b1 else monomial d t c0 a0 b0) : K) * M i j *
      (↑(if j then monomial d t k1 r1 s1 else monomial d t k0 r0 s0) : K)) false true false true =
      (↑(monomial d t (c0*c1*k0*k1) (a0+a1+r0+r1) (b0+b1+s0+s1)) : K) *
        minor M false true false true := by
  rw [minor_row_column]
  simp only [Bool.false_eq_true, ↓reduceIte]
  congr 1
  rw [← Units.val_mul, ← Units.val_mul, ← Units.val_mul]
  apply congrArg Units.val
  simp only [monomial, zpow_add]
  ac_rfl

end Holant.Marked.WeightedGauge
