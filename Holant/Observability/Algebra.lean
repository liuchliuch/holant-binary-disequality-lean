import Holant.Kernel
import Mathlib.Analysis.Complex.Basic
import Mathlib.LinearAlgebra.Span.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination

/-!
The algebraic part of source Theorem 5.17. All scalar spans are over `ℂ`,
and the kernel pairing is bilinear (there is no complex conjugation).
The classification is stronger than needed: any transpose-stable complex
subspace closed under actual kernel multiplication and containing literal
`I` and `X` has one of the two stated values.
-/

namespace Holant.Observability

noncomputable section

abbrev Mat := Kernel ℂ

/-- The literal two-generator complex span. -/
def ixSpan : Submodule ℂ Mat :=
  Submodule.span ℂ {Signature.equality, Signature.disequality}

@[simp] theorem equality_mem_ixSpan : (Signature.equality : Mat) ∈ ixSpan :=
  Submodule.subset_span (by simp)

@[simp] theorem disequality_mem_ixSpan : (Signature.disequality : Mat) ∈ ixSpan :=
  Submodule.subset_span (by simp)

theorem mem_ixSpan_iff (A : Mat) :
    A ∈ ixSpan ↔ A false false = A true true ∧ A false true = A true false := by
  constructor
  · intro h
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp h
    simp [Signature.equality, Signature.disequality]
  · rintro ⟨h₁, h₂⟩
    apply Submodule.mem_span_pair.mpr
    refine ⟨A false false, A false true, ?_⟩
    funext a b
    cases a <;> cases b <;> simp [Signature.equality, Signature.disequality, h₁, h₂]

/-- Rank-one off-diagonal matrix unit in the unnormalized Walsh basis. -/
def walshUnit : Mat := fun _ b => if b then -1 else 1

/-- The extraction coefficient of `(I+X) A (I-X)`. -/
def offCoefficient (A : Mat) : ℂ :=
  A false false - A false true + A true false - A true true

theorem extract_walshUnit (A : Mat) :
    Kernel.mul (Kernel.mul ((Signature.equality : Mat) + Signature.disequality) A)
      ((Signature.equality : Mat) - Signature.disequality) =
        offCoefficient A • walshUnit := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.mul_apply, Signature.equality, Signature.disequality,
      offCoefficient, walshUnit] <;> ring

theorem offCoefficients_zero (A : Mat)
    (h : offCoefficient A = 0) (ht : offCoefficient (Kernel.transpose A) = 0) :
    A ∈ ixSpan := by
  apply (mem_ixSpan_iff A).mpr
  dsimp [offCoefficient, Kernel.transpose] at h ht
  constructor
  · linear_combination (h + ht) / 2
  · linear_combination (ht - h) / 2

/-- Literal coordinate reconstruction from four fixed matrices. -/
theorem walsh_decomposition (A : Mat) :
    A = ((A false false + A true true) / 2) • (Signature.equality : Mat) +
      ((A false true + A true false) / 2) • (Signature.disequality : Mat) +
      ((A false false - A true true + A true false - A false true) / 4) • walshUnit +
      ((A false false - A true true - A true false + A false true) / 4) •
        Kernel.transpose walshUnit := by
  funext a b
  cases a <;> cases b <;>
    simp [Signature.equality, Signature.disequality, walshUnit, Kernel.transpose] <;> ring

/-- A nonzero extracted coefficient produces the actual rank-one Walsh unit
by a scalar multiple inside the subspace. -/
theorem walshUnit_mem_of_coefficient
    (V : Submodule ℂ Mat)
    (hI : (Signature.equality : Mat) ∈ V)
    (hX : (Signature.disequality : Mat) ∈ V)
    (hMul : ∀ A ∈ V, ∀ B ∈ V, Kernel.mul A B ∈ V)
    (A : Mat) (hA : A ∈ V) (hc : offCoefficient A ≠ 0) : walshUnit ∈ V := by
  have he := hMul _ (hMul _ (V.add_mem hI hX) _ hA) _ (V.sub_mem hI hX)
  rw [extract_walshUnit] at he
  have hs := V.smul_mem (offCoefficient A)⁻¹ he
  simpa only [smul_smul, inv_mul_cancel₀ hc, one_smul] using hs

/-- The binary-kernel algebra dichotomy, without any group classification
or gadget-availability hypothesis. -/
theorem transpose_stable_algebra_dichotomy
    (V : Submodule ℂ Mat)
    (hI : (Signature.equality : Mat) ∈ V)
    (hX : (Signature.disequality : Mat) ∈ V)
    (hMul : ∀ A ∈ V, ∀ B ∈ V, Kernel.mul A B ∈ V)
    (hTranspose : ∀ A ∈ V, Kernel.transpose A ∈ V) :
    V = ixSpan ∨ V = ⊤ := by
  classical
  have hSmall : ixSpan ≤ V := by
    apply Submodule.span_le.mpr
    intro A hA
    rcases Set.mem_insert_iff.mp hA with rfl | hA
    · exact hI
    · simpa only [Set.mem_singleton_iff] using hA ▸ hX
  by_cases h : V ≤ ixSpan
  · exact Or.inl (le_antisymm h hSmall)
  · have hw : ∃ A ∈ V, A ∉ ixSpan := by
      by_contra hn
      apply h
      intro A hA
      by_contra hx
      exact hn ⟨A, hA, hx⟩
    obtain ⟨A, hA, hn⟩ := hw
    have hU : walshUnit ∈ V := by
      by_cases hc : offCoefficient A = 0
      · have hct : offCoefficient (Kernel.transpose A) ≠ 0 := by
          intro ht
          exact hn (offCoefficients_zero A hc ht)
        exact walshUnit_mem_of_coefficient V hI hX hMul _ (hTranspose A hA) hct
      · exact walshUnit_mem_of_coefficient V hI hX hMul A hA hc
    apply Or.inr
    apply top_unique
    intro B _
    rw [walsh_decomposition B]
    exact V.add_mem (V.add_mem (V.add_mem (V.smul_mem _ hI)
      (V.smul_mem _ hX)) (V.smul_mem _ hU))
      (V.smul_mem _ (hTranspose walshUnit hU))

/-- Bilinear Frobenius orthogonality to a subspace of ordered kernels. -/
def frobeniusOrthogonal (V : Submodule ℂ Mat) : Set Mat :=
  {A | ∀ B ∈ V, Kernel.pair B A = 0}

theorem pair_equality (A : Mat) :
    Kernel.pair Signature.equality A = A false false + A true true := by
  simp [Kernel.pair, Signature.equality, add_comm]

theorem pair_disequality (A : Mat) :
    Kernel.pair Signature.disequality A = A false true + A true false := by
  simp [Kernel.pair, Signature.disequality, add_comm]

/-- Exact coordinate equations for the proper-algebra annihilator. -/
theorem mem_ixSpan_orthogonal_iff (A : Mat) :
    A ∈ frobeniusOrthogonal ixSpan ↔
      A false false + A true true = 0 ∧ A false true + A true false = 0 := by
  constructor
  · intro h
    exact ⟨by simpa only [pair_equality] using h _ equality_mem_ixSpan,
      by simpa only [pair_disequality] using h _ disequality_mem_ixSpan⟩
  · rintro ⟨hI, hX⟩ B hB
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.mp hB
    simp only [Kernel.pair, Fintype.sum_bool, Pi.add_apply, Pi.smul_apply,
      smul_eq_mul, Signature.equality, Signature.disequality]
    simp only [Bool.false_eq_true, Bool.true_eq_false, ne_eq, not_false_eq_true,
      not_true_eq_false, ↓reduceIte, mul_zero, mul_one, add_zero, zero_add]
    linear_combination a * hI + b * hX

/-- The displayed source complement `[[u,v],[-v,-u]]`. -/
def invisible (u v : ℂ) : Mat := fun a b =>
  if a then (if b then -u else -v) else (if b then v else u)

theorem ixSpan_frobenius_complement :
    frobeniusOrthogonal ixSpan = {A | ∃ u v : ℂ, A = invisible u v} := by
  ext A
  rw [mem_ixSpan_orthogonal_iff]
  constructor
  · rintro ⟨hI, hX⟩
    refine ⟨A false false, A false true, ?_⟩
    funext a b
    cases a <;> cases b <;> simp [invisible]
    · linear_combination hX
    · linear_combination hI
  · rintro ⟨u, v, rfl⟩
    simp [invisible]

end
end Holant.Observability
