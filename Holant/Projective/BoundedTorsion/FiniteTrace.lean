import Holant.Projective.BoundedTorsion.Adjoint
import Mathlib.LinearAlgebra.Dimension.StrongRankCondition
import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-! A finite-trace criterion for torsion subgroups of two-by-two matrices.
The finite trace hypothesis is explicit; no bounded-order or number-field
finiteness conclusion is assumed. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K] [CharZero K]

/-- In dimension two, vanishing of the first two power traces forces square zero. -/
theorem square_zero_of_trace_eq_zero {N : Binary (K := K)}
    (h₁ : Matrix.trace N = 0) (h₂ : Matrix.trace (N * N) = 0) : N * N = 0 := by
  have hd : N true true = -N false false := by
    have hs : N true true + N false false = 0 := by simpa [Matrix.trace] using h₁
    exact add_eq_zero_iff_eq_neg.mp hs
  have hscale : (2 : K) • (N * N) = Matrix.trace (N * N) • (1 : Binary) := by
    ext i j
    cases i <;> cases j <;>
      simp [Matrix.trace, Matrix.mul_apply, hd] <;> ring
  rw [h₂, zero_smul] at hscale
  exact (smul_eq_zero.mp hscale).resolve_left (by norm_num)

/-- The binomial expansion for a square-zero matrix has just two terms. -/
theorem one_add_pow_of_square_zero {N : Binary (K := K)} (hN : N * N = 0) (n : ℕ) :
    (1 + N) ^ n = 1 + (n : K) • N := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, ih, add_mul, one_mul, mul_add, Matrix.mul_one,
      Matrix.smul_mul, hN, smul_zero, add_zero]
    simp only [Nat.cast_add, Nat.cast_one, add_smul, one_smul]
    abel

/-- A unipotent matrix of finite order in characteristic zero is the identity. -/
theorem eq_one_of_square_zero_sub_one_of_finite_order {T : Binary (K := K)}
    (hN : (T - 1) * (T - 1) = 0) (hT : IsOfFinOrder T) : T = 1 := by
  obtain ⟨n, hn, hpow⟩ := isOfFinOrder_iff_pow_eq_one.mp hT
  have h := one_add_pow_of_square_zero hN n
  rw [add_sub_cancel, hpow] at h
  have hz : (n : K) • (T - 1) = 0 := by
    exact (add_eq_left.mp h.symm)
  have hnK : (n : K) ≠ 0 := by exact_mod_cast hn.ne'
  exact sub_eq_zero.mp ((smul_eq_zero.mp hz).resolve_left hnK)

/-- Two power traces detect the identity among torsion two-by-two matrices. -/
theorem eq_one_of_power_traces {T : Binary (K := K)} (hT : IsOfFinOrder T)
    (h₁ : Matrix.trace T = 2) (h₂ : Matrix.trace (T * T) = 2) : T = 1 := by
  apply eq_one_of_square_zero_sub_one_of_finite_order _ hT
  apply square_zero_of_trace_eq_zero
  · rw [Matrix.trace_sub, h₁]
    norm_num [Matrix.trace]
  · rw [sub_mul, mul_sub, mul_sub]
    simp only [Matrix.one_mul, Matrix.mul_one, Matrix.trace_sub, h₁, h₂]
    simp [Matrix.trace]

/-- The right translates of trace separate a faithful torsion representation. -/
theorem eq_of_trace_right_translates {G : Type*} [Group G]
    (ρ : G →* Binary (K := K)) (hρ : Function.Injective ρ)
    (htorsion : ∀ g, IsOfFinOrder (ρ g)) {g h : G}
    (heq : ∀ a, Matrix.trace (ρ (g * a)) = Matrix.trace (ρ (h * a))) : g = h := by
  let q := g * h⁻¹
  have h₁ : Matrix.trace (ρ q) = 2 := by
    have he := heq h⁻¹
    simpa [q, Matrix.trace] using he
  have h₂ : Matrix.trace (ρ q * ρ q) = 2 := by
    calc
      Matrix.trace (ρ q * ρ q) = Matrix.trace (ρ (g * (h⁻¹ * g * h⁻¹))) := by
        rw [← map_mul]
        simp only [q, mul_assoc]
      _ = Matrix.trace (ρ (h * (h⁻¹ * g * h⁻¹))) := heq _
      _ = Matrix.trace (ρ q) := by simp [q, mul_assoc]
      _ = 2 := h₁
  have hq : q = 1 := hρ (by simpa using eq_one_of_power_traces (htorsion q) h₁ h₂)
  exact mul_inv_eq_one.mp hq

omit [CharZero K] in
/-- Equality of trace pairings on generators extends to their linear span. -/
theorem trace_mul_eq_of_mem_span {S : Set (Binary (K := K))}
    {U V A : Binary (K := K)}
    (h : ∀ B ∈ S, Matrix.trace (U * B) = Matrix.trace (V * B))
    (hA : A ∈ Submodule.span K S) : Matrix.trace (U * A) = Matrix.trace (V * A) := by
  induction hA using Submodule.span_induction with
  | mem B hB => exact h B hB
  | zero => simp
  | add B C hB hC ihB ihC => simp only [mul_add, Matrix.trace_add, ihB, ihC]
  | smul r B hB ih => simp only [Matrix.mul_smul, Matrix.trace_smul, ih]

/-- A faithful torsion representation in dimension two with finite trace range
has a finite source group.  Finite trace range is a genuine separate assumption. -/
theorem finite_of_finite_trace_range {G : Type*} [Group G]
    (ρ : G →* Binary (K := K)) (hρ : Function.Injective ρ)
    (htorsion : ∀ g, IsOfFinOrder (ρ g))
    (htrace : (Set.range (fun g => Matrix.trace (ρ g))).Finite) : Finite G := by
  classical
  obtain ⟨f, hf, hspan, _⟩ :=
    Submodule.exists_fun_fin_finrank_span_eq K (Set.range ρ)
  let R := Set.range (fun g => Matrix.trace (ρ g))
  let : Fintype R := htrace.fintype
  let tuple : G → (Fin (Module.finrank K (Submodule.span K (Set.range ρ))) → R) :=
    fun g i => ⟨Matrix.trace (ρ g * f i), by
      obtain ⟨a, ha⟩ := hf i
      exact ⟨g * a, by simp only [map_mul, ha]⟩⟩
  apply Finite.of_injective tuple
  intro g h he
  apply eq_of_trace_right_translates ρ hρ htorsion
  intro a
  rw [map_mul, map_mul]
  apply trace_mul_eq_of_mem_span (S := Set.range f)
  · rintro B ⟨i, rfl⟩
    exact congrArg Subtype.val (congrFun he i)
  · rw [hspan]
    exact Submodule.subset_span ⟨a, rfl⟩

/-- The same criterion for an ordinary matrix submonoid: torsion itself supplies
all inverses, so a separately supplied group structure is unnecessary. -/
theorem finite_submonoid_of_finite_trace_range (S : Submonoid (Binary (K := K)))
    (htorsion : ∀ T : S, IsOfFinOrder (T : Binary (K := K)))
    (htrace : (Set.range (fun T : S => Matrix.trace (T : Binary (K := K)))).Finite) : Finite S := by
  have ht : ∀ T : S, IsOfFinOrder T := by
    intro T
    obtain ⟨n, hn, hp⟩ := (htorsion T).exists_pow_eq_one
    apply isOfFinOrder_iff_pow_eq_one.mpr
    exact ⟨n, hn, Subtype.ext hp⟩
  let : Group S := groupOfIsUnit (fun T => (ht T).isUnit)
  exact finite_of_finite_trace_range S.subtype Subtype.val_injective htorsion htrace

/-- A multiplicatively closed set of torsion two-by-two matrices with finitely
many traces is finite, including the empty set. -/
theorem finite_matrix_set_of_finite_traces {S : Set (Binary (K := K))}
    (hmul : ∀ U ∈ S, ∀ V ∈ S, U * V ∈ S)
    (htorsion : ∀ T ∈ S, IsOfFinOrder T)
    (htrace : (Matrix.trace '' S).Finite) : S.Finite := by
  classical
  by_cases hne : S.Nonempty
  · have hone : (1 : Binary (K := K)) ∈ S := by
      obtain ⟨T, hT⟩ := hne
      obtain ⟨n, hn, hp⟩ := (htorsion T hT).exists_pow_eq_one
      rw [← hp]
      exact positive_power_mem hmul hT hn
    let M : Submonoid (Binary (K := K)) :=
      { carrier := S, one_mem' := hone, mul_mem' := fun hU hV => hmul _ hU _ hV }
    have hmtrace : (Set.range (fun T : M => Matrix.trace (T : Binary (K := K)))).Finite := by
      apply htrace.subset
      rintro _ ⟨T, rfl⟩
      exact ⟨T, T.property, rfl⟩
    have : Finite M := finite_submonoid_of_finite_trace_range M
      (fun T => htorsion T T.property) hmtrace
    exact Set.finite_coe_iff.mp this
  · exact Set.finite_empty.subset (Set.not_nonempty_iff_eq_empty.mp hne ▸ Set.Subset.rfl)

/-- The GL₂ formulation, using invertible matrices as units of the matrix ring. -/
theorem finite_subgroup_of_finite_trace_range (S : Subgroup (Binary (K := K))ˣ)
    (htorsion : ∀ T : S, IsOfFinOrder T)
    (htrace : (Set.range (fun T : S =>
      Matrix.trace ((T : (Binary (K := K))ˣ) : Binary (K := K)))).Finite) : Finite S := by
  let ρ : S →* Binary (K := K) := (Units.coeHom _).comp S.subtype
  apply finite_of_finite_trace_range ρ
    (Units.val_injective.comp Subtype.val_injective) _ htrace
  intro T
  obtain ⟨n, hn, hp⟩ := (htorsion T).exists_pow_eq_one
  exact isOfFinOrder_iff_pow_eq_one.mpr ⟨n, hn, by rw [← map_pow, hp, map_one]⟩

end
end Holant.Projective.BoundedTorsion
