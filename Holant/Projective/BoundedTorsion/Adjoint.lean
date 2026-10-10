import Holant.Projective.BoundedTorsion.Group
import Mathlib.LinearAlgebra.Matrix.Trace

/-! The elementary kernel calculation in source Lemma 5.2: commuting with
all trace-zero two-by-two matrices forces a matrix to be scalar.
Consequently conjugation on the trace-zero space detects projective scalars. -/

namespace Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
noncomputable section
variable {K : Type*} [Field K]

private def upperUnit : Binary (K := K) := fun i j => if i = false ∧ j = true then 1 else 0
private def lowerUnit : Binary (K := K) := fun i j => if i = true ∧ j = false then 1 else 0

theorem scalar_of_commutes_traceZero (T : Binary (K := K))
    (hT : ∀ A : Binary (K := K), Matrix.trace A = 0 → T * A = A * T) :
    ∃ c : K, T = c • (1 : Binary) := by
  have hu := hT upperUnit (by simp [Matrix.trace, upperUnit])
  have hl := hT lowerUnit (by simp [Matrix.trace, lowerUnit])
  have h10 := congrArg (fun M : Binary (K := K) => M false false) hu
  have h01 := congrArg (fun M : Binary (K := K) => M true true) hl
  have hdiag := congrArg (fun M : Binary (K := K) => M false true) hu
  simp [Matrix.mul_apply, upperUnit, lowerUnit] at h10 h01 hdiag
  refine ⟨T false false, ?_⟩
  ext i j
  cases i <;> cases j <;> simp [Matrix.one_apply, ← h10, ← h01, hdiag]

theorem commutes_traceZero_iff_scalar (T : Binary (K := K)) :
    (∀ A : Binary (K := K), Matrix.trace A = 0 → T * A = A * T) ↔
      ∃ c : K, T = c • (1 : Binary) := by
  refine ⟨scalar_of_commutes_traceZero T, ?_⟩
  rintro ⟨c, rfl⟩ A _
  simp [Matrix.smul_mul, Matrix.mul_smul]

theorem scalar_of_adjoint_trivial {T V : Binary (K := K)} (hVT : V * T = 1)
    (h : ∀ A : Binary (K := K), Matrix.trace A = 0 → T * A * V = A) :
    ∃ c : K, T = c • (1 : Binary) := by
  apply scalar_of_commutes_traceZero
  intro A hA
  have he := congrArg (fun M : Binary (K := K) => M * T) (h A hA)
  simpa only [Matrix.mul_assoc, hVT, Matrix.mul_one] using he

/-- The adjoint kernel consists exactly of nonzero scalar matrices. -/
theorem adjoint_trivial_iff_scalar {T V : Binary (K := K)}
    (hTV : T * V = 1) (hVT : V * T = 1) :
    (∀ A : Binary (K := K), Matrix.trace A = 0 → T * A * V = A) ↔
      ∃ c : K, c ≠ 0 ∧ T = c • (1 : Binary) := by
  constructor
  · intro h
    obtain ⟨c, hc⟩ := scalar_of_adjoint_trivial hVT h
    refine ⟨c, ?_, hc⟩
    intro hz
    rw [hz, zero_smul] at hc
    have he := hTV
    rw [hc, Matrix.zero_mul] at he
    exact zero_ne_one he
  · rintro ⟨c, _, hc⟩ A _
    have hcomm : T * A = A * T := by rw [hc]; simp [Matrix.smul_mul, Matrix.mul_smul]
    rw [hcomm, Matrix.mul_assoc, hTV, Matrix.mul_one]

theorem adjoint_preserves_trace {T V : Binary (K := K)} (hVT : V * T = 1)
    (A : Binary (K := K)) : Matrix.trace (T * A * V) = Matrix.trace A := by
  rw [Matrix.trace_mul_cycle, hVT, Matrix.one_mul]

end
end Holant.Projective.BoundedTorsion
