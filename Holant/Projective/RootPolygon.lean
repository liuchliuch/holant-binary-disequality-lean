import Holant.Polynomial.GridInterpolation
import Mathlib.Algebra.Polynomial.Eval.Degree
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Möbius stabilizers of complex root polygons

Manuscript Lemma 6.9 (`lem:nd-root-mobius`). The proof uses actual complex
roots of unity and polynomial interpolation, rather than a classification
assumption. The sphere is represented by `Option ℂ`, with `none` the point
at infinity; poles are therefore never interpreted as totalized division.
-/

noncomputable section

namespace Holant.Projective

open Polynomial

/-- A degree-at-most-`m` polynomial vanishing on all `m` complex roots of unity
has no interior coefficients. -/
theorem root_polygon_interior_coeff {m : ℕ} (hm : 0 < m) (p : ℂ[X])
    (hdeg : p.natDegree ≤ m)
    (hvanish : ∀ z : ℂ, z ^ m = 1 → p.eval z = 0)
    {k : ℕ} (hk0 : 0 < k) (hkm : k < m) : p.coeff k = 0 := by
  classical
  let : NeZero m := ⟨by omega⟩
  let q : ℂ[X] := p - C (p.coeff m) * (X ^ m - 1)
  have hqdeg : q.degree < m := by
    rw [degree_lt_iff_coeff_zero]
    intro n hn
    by_cases hnm : n = m
    · subst n
      simp [q, coeff_C_mul, coeff_X_pow, coeff_one, Nat.ne_of_gt hm]
    · have hmn : m < n := by omega
      have hn0 : n ≠ 0 := by omega
      simp [q, coeff_C_mul, coeff_X_pow, coeff_one, hnm, hn0,
        coeff_eq_zero_of_natDegree_lt (hdeg.trans_lt hmn)]
  have hq : q = 0 := by
    by_cases hq0 : q = 0
    · exact hq0
    apply Polynomial.eq_zero_of_natDegree_lt_card_of_eval_eq_zero' q
      (Holant.Laurent.rootCoset m 1)
    · intro z hz
      obtain ⟨u, hu⟩ := (Holant.Laurent.mem_rootCoset m 1 z).mp hz
      have hu' : (↑u.val : ℂ) ^ m = 1 := by
        have h := u.property
        rw [mem_rootsOfUnity] at h
        exact congrArg Units.val h
      have hu'' : (↑u.val : ℂ) = z := by simpa using hu
      have hz' : z ^ m = 1 := hu'' ▸ hu'
      simp [q, hvanish z hz', hz']
    · rw [Holant.Laurent.card_rootCoset]
      exact (natDegree_lt_iff_degree_lt hq0).mpr hqdeg
  have h := congrArg (fun r : ℂ[X] => r.coeff k) hq
  simpa [q, coeff_C_mul, coeff_X_pow, coeff_one,
    Nat.ne_of_lt hkm, Nat.ne_of_gt hk0] using h

/-- The binomial coefficient of a powered affine linear polynomial. -/
theorem coeff_affine_pow (u v : ℂ) (m k : ℕ) :
    ((C u + C v * X) ^ m : ℂ[X]).coeff k =
      u ^ (m - k) * (m.choose k : ℂ) * v ^ k := by
  have h : ((X + C u) ^ m).comp (C v * X) = (C u + C v * X) ^ m := by
    simp [add_comm]
  rw [← h, comp_C_mul_X_coeff, coeff_X_add_C_pow]

/-- Polynomial rigidity gives the two possible zero patterns of an invertible
matrix whose associated fractional linear map preserves the root polygon. -/
theorem root_polygon_matrix_form {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hroots : ∀ z : ℂ, z ^ m = 1 → ((c + d * z) / (a + b * z)) ^ m = 1) :
    (b = 0 ∧ c = 0 ∧ a ≠ 0 ∧ d ≠ 0) ∨
      (a = 0 ∧ d = 0 ∧ b ≠ 0 ∧ c ≠ 0) := by
  let p : ℂ[X] := (C c + C d * X) ^ m - (C a + C b * X) ^ m
  have hlin (u v : ℂ) : (C u + C v * X : ℂ[X]).natDegree ≤ 1 := by
    apply natDegree_add_le_of_degree_le
    · simp
    · simpa using natDegree_C_mul_X_pow_le v 1
  have hdeg : p.natDegree ≤ m := by
    apply (natDegree_sub_le _ _).trans
    apply max_le
    · exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left m (hlin c d))
    · exact natDegree_pow_le.trans (by simpa using Nat.mul_le_mul_left m (hlin a b))
  have hvanish (z : ℂ) (hz : z ^ m = 1) : p.eval z = 0 := by
    have h := hroots z hz
    rw [div_pow, div_eq_one_iff_eq (pow_ne_zero m (hpole z hz))] at h
    simpa [p, sub_eq_zero] using h
  have hcoeff (k : ℕ) (hk0 : 0 < k) (hkm : k < m) :
      c ^ (m - k) * d ^ k = a ^ (m - k) * b ^ k := by
    have h := root_polygon_interior_coeff (by omega) p hdeg hvanish hk0 hkm
    simp only [p, coeff_sub, coeff_affine_pow, sub_eq_zero] at h
    have hn : (m.choose k : ℂ) ≠ 0 := by
      exact_mod_cast (Nat.choose_pos (by omega : k ≤ m)).ne'
    apply mul_right_cancel₀ hn
    calc
      c ^ (m - k) * d ^ k * (m.choose k : ℂ) =
          c ^ (m - k) * (m.choose k : ℂ) * d ^ k := by ring
      _ = a ^ (m - k) * (m.choose k : ℂ) * b ^ k := h
      _ = a ^ (m - k) * b ^ k * (m.choose k : ℂ) := by ring
  have h1 := hcoeff 1 (by omega) (by omega)
  have h2 := hcoeff 2 (by omega) (by omega)
  simp only [pow_one] at h1
  have hpow : m - 1 = (m - 2) + 1 := by omega
  rw [hpow, pow_succ, pow_succ] at h1
  have heq : a ^ (m - 2) * b * (a * d - b * c) = 0 := by
    calc
      a ^ (m - 2) * b * (a * d - b * c) =
          (c ^ (m - 2) * c * d - a ^ (m - 2) * a * b) * (-d) +
            (c ^ (m - 2) * d ^ 2 - a ^ (m - 2) * b ^ 2) * c := by ring
      _ = 0 := by rw [h1, h2]; ring
  have hab : a = 0 ∨ b = 0 := by
    have hprod := (mul_eq_zero.mp heq).resolve_right hdet
    rcases mul_eq_zero.mp hprod with ha | hb
    · exact Or.inl (eq_zero_of_pow_eq_zero ha)
    · exact Or.inr hb
  rcases hab with ha | hb
  · right
    have hbc : b * c ≠ 0 := by simpa [ha] using hdet
    have hb := (mul_ne_zero_iff.mp hbc).1
    have hc := (mul_ne_zero_iff.mp hbc).2
    have hm2 : m - 2 ≠ 0 := by omega
    have hd : d = 0 := by
      simp only [ha, zero_pow hm2, zero_mul] at h1
      exact (mul_eq_zero.mp h1).resolve_left (mul_ne_zero (pow_ne_zero _ hc) hc)
    exact ⟨ha, hd, hb, hc⟩
  · left
    have had : a * d ≠ 0 := by simpa [hb] using hdet
    have ha := (mul_ne_zero_iff.mp had).1
    have hd := (mul_ne_zero_iff.mp had).2
    have hc : c = 0 := by
      simp only [hb, mul_zero] at h1
      have hc' := (mul_eq_zero.mp h1).resolve_right hd
      rcases mul_eq_zero.mp hc' with h | h
      · exact eq_zero_of_pow_eq_zero h
      · exact h
    exact ⟨hb, hc, ha, hd⟩

/-- The extended complex plane, with `none` the point at infinity. -/
abbrev ComplexSphere := Option ℂ

/-- The fractional linear map `(c + d z) / (a + b z)` on the extended
complex plane. Its finite poles and its value at infinity are explicit. -/
def mobius (a b c d : ℂ) : ComplexSphere → ComplexSphere
  | none => if b = 0 then none else some (d / b)
  | some z => if a + b * z = 0 then none else some ((c + d * z) / (a + b * z))

/-- The sphere map `z ↦ α z`, fixing infinity. -/
def rootRotation (α : ℂ) : ComplexSphere → ComplexSphere
  | none => none
  | some z => some (α * z)

/-- The sphere map `z ↦ α / z`, interchanging zero and infinity. -/
def rootReflection (α : ℂ) : ComplexSphere → ComplexSphere
  | none => some 0
  | some z => if z = 0 then none else some (α / z)

/-- A diagonal coefficient matrix is a rotation/dilation on the entire sphere. -/
theorem mobius_diagonal (a d : ℂ) (ha : a ≠ 0) :
    mobius a 0 0 d = rootRotation (d / a) := by
  funext z
  cases z with
  | none => simp [mobius, rootRotation]
  | some z => simp [mobius, rootRotation, ha, div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc]

/-- An antidiagonal coefficient matrix is scaled inversion on the entire sphere,
including its pole at zero and its value at infinity. -/
theorem mobius_antidiagonal (b c : ℂ) (hb : b ≠ 0) :
    mobius 0 b c 0 = rootReflection (c / b) := by
  funext z
  cases z with
  | none => simp [mobius, rootReflection, hb]
  | some z =>
    by_cases hz : z = 0
    · simp [mobius, rootReflection, hz]
    · simp [mobius, rootReflection, hb, hz, div_mul_eq_div_div]

/-- The literal complex root polygon `μ_m`. -/
def rootPolygon (m : ℕ) : Set ℂ := {z | z ^ m = 1}

/-- A coefficient form of manuscript Lemma 6.9, with the actual multiplier
in `μ_m`. Root preservation already suffices; no assumed normal form or
surjectivity is used in the algebraic proof. -/
theorem root_polygon_coefficients {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hroots : Set.MapsTo (fun z : ℂ => (c + d * z) / (a + b * z))
      (rootPolygon m) (rootPolygon m)) :
    ∃ α : ℂ, α ^ m = 1 ∧
      ((b = 0 ∧ c = 0 ∧ a ≠ 0 ∧ d = α * a) ∨
        (a = 0 ∧ d = 0 ∧ b ≠ 0 ∧ c = α * b)) := by
  rcases root_polygon_matrix_form hm a b c d hdet hpole hroots with h | h
  · obtain ⟨hb, hc, ha, _⟩ := h
    refine ⟨d / a, ?_, Or.inl ⟨hb, hc, ha, ?_⟩⟩
    · simpa [rootPolygon, hb, hc] using hroots (by simp [rootPolygon] : (1 : ℂ) ∈ rootPolygon m)
    · exact (div_mul_cancel₀ d ha).symm
  · obtain ⟨ha, hd, hb, _⟩ := h
    refine ⟨c / b, ?_, Or.inr ⟨ha, hd, hb, ?_⟩⟩
    · simpa [rootPolygon, ha, hd] using hroots (by simp [rootPolygon] : (1 : ℂ) ∈ rootPolygon m)
    · exact (div_mul_cancel₀ c hb).symm

/-- Root preservation and absence of poles already give the sphere normal form. -/
theorem root_polygon_stabilizer_of_mapsTo {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hroots : Set.MapsTo (fun z : ℂ => (c + d * z) / (a + b * z))
      (rootPolygon m) (rootPolygon m)) :
    ∃ α : ℂ, α ^ m = 1 ∧
      (mobius a b c d = rootRotation α ∨ mobius a b c d = rootReflection α) := by
  obtain ⟨α, hα, h | h⟩ := root_polygon_coefficients hm a b c d hdet hpole hroots
  · obtain ⟨hb, hc, ha, hd⟩ := h
    refine ⟨α, hα, Or.inl ?_⟩
    rw [hb, hc, mobius_diagonal a d ha, hd, mul_div_cancel_right₀ α ha]
  · obtain ⟨ha, hd, hb, hc⟩ := h
    refine ⟨α, hα, Or.inr ?_⟩
    rw [ha, hd, mobius_antidiagonal b c hb, hc, mul_div_cancel_right₀ α hb]

/-- **Manuscript Lemma 6.9** (`lem:nd-root-mobius`). A nonsingular Möbius
map with no pole on the complex root polygon which permutes that polygon
is multiplication by a root of unity or a root of unity times inversion.
Equality here is equality of maps on the whole extended complex plane,
not merely equality of totalized complex-valued fractions. -/
theorem root_polygon_stabilizer {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hperm : Set.BijOn (fun z : ℂ => (c + d * z) / (a + b * z))
      (rootPolygon m) (rootPolygon m)) :
    ∃ α : ℂ, α ^ m = 1 ∧
      (mobius a b c d = rootRotation α ∨ mobius a b c d = rootReflection α) :=
  root_polygon_stabilizer_of_mapsTo hm a b c d hdet hpole hperm.mapsTo

/-- The actual root polygon embedded in the extended complex plane. -/
def sphereRootPolygon (m : ℕ) : Set ComplexSphere := Option.some '' rootPolygon m

@[simp] theorem some_mem_sphereRootPolygon (m : ℕ) (z : ℂ) :
    some z ∈ sphereRootPolygon m ↔ z ^ m = 1 := by
  simp [sphereRootPolygon, rootPolygon]

@[simp] theorem none_not_mem_sphereRootPolygon (m : ℕ) :
    none ∉ sphereRootPolygon m := by
  simp [sphereRootPolygon]

/-- The source statement with the permutation hypothesis itself expressed on
the whole sphere. The no-pole hypothesis identifies its restriction with the
ordinary fractional linear formula, without assigning any finite value to a pole. -/
theorem root_polygon_stabilizer_sphere {m : ℕ} (hm : 3 ≤ m) (a b c d : ℂ)
    (hdet : a * d - b * c ≠ 0)
    (hpole : ∀ z : ℂ, z ^ m = 1 → a + b * z ≠ 0)
    (hperm : Set.BijOn (mobius a b c d) (sphereRootPolygon m) (sphereRootPolygon m)) :
    ∃ α : ℂ, α ^ m = 1 ∧
      (mobius a b c d = rootRotation α ∨ mobius a b c d = rootReflection α) := by
  apply root_polygon_stabilizer_of_mapsTo hm a b c d hdet hpole
  intro z hz
  have hz' : some z ∈ sphereRootPolygon m := ⟨z, hz, rfl⟩
  obtain ⟨w, hw, heq⟩ := hperm.mapsTo hz'
  change some w = (if a + b * z = 0 then none else
    some ((c + d * z) / (a + b * z))) at heq
  rw [ite_eq_right (hpole z hz)] at heq
  change (c + d * z) / (a + b * z) ∈ rootPolygon m
  rw [← Option.some.inj heq]
  exact hw

/-- Multiplication by a genuine `m`-th root permutes the actual root polygon. -/
theorem rootPolygon_mul_bijOn {m : ℕ} (hm : 0 < m) {α : ℂ} (hα : α ^ m = 1) :
    Set.BijOn (fun z : ℂ => α * z) (rootPolygon m) (rootPolygon m) := by
  have hα0 : α ≠ 0 := by
    intro h
    simp [h, Nat.ne_of_gt hm] at hα
  refine ⟨?_, ?_, ?_⟩
  · intro z hz
    change (α * z) ^ m = 1
    rw [mul_pow, hα, hz, one_mul]
  · intro z hz w hw h
    exact mul_left_cancel₀ hα0 h
  · intro z hz
    refine ⟨z / α, ?_, ?_⟩
    · change (z / α) ^ m = 1
      rw [div_pow, hα, hz, div_one]
    · exact mul_div_cancel₀ z hα0

/-- Scaled inversion by a genuine `m`-th root permutes the actual root polygon. -/
theorem rootPolygon_div_bijOn {m : ℕ} (hm : 0 < m) {α : ℂ} (hα : α ^ m = 1) :
    Set.BijOn (fun z : ℂ => α / z) (rootPolygon m) (rootPolygon m) := by
  have hα0 : α ≠ 0 := by
    intro h
    simp [h, Nat.ne_of_gt hm] at hα
  have hmap : Set.MapsTo (fun z : ℂ => α / z) (rootPolygon m) (rootPolygon m) := by
    intro z hz
    change (α / z) ^ m = 1
    rw [div_pow, hα, hz, div_self one_ne_zero]
  refine ⟨hmap, ?_, ?_⟩
  · intro z hz w hw h
    have h' := congrArg (fun x : ℂ => α / x) h
    simpa only [div_div_cancel₀ hα0] using h'
  · intro z hz
    exact ⟨α / z, hmap hz, div_div_cancel₀ hα0⟩

end Holant.Projective
