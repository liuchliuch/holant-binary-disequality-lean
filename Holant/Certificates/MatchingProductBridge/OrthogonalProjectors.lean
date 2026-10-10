import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.FinCases

/-! The square-matrix step in the orthogonal-frame argument of Lemma A.15.
This proves the projector sum criterion for actual unit real columns; the
quaternion tensor embedding and complete bridge-triple classification are separate. -/
namespace Holant.Certificates.MatchingProductBridge
set_option backward.isDefEq.respectTransparency false

abbrev RealFrame := Matrix (Fin 3) (Fin 3) ℝ

def UnitColumns (E : RealFrame) : Prop := ∀ j, ∑ k : Fin 3, E k j * E k j = 1

def OrthogonalColumns (E : RealFrame) : Prop :=
  ∀ i j, i ≠ j → ∑ k : Fin 3, E k i * E k j = 0

def columnProjector (E : RealFrame) (k : Fin 3) : RealFrame :=
  Matrix.vecMulVec (fun i => E i k) (fun j => E j k)

/-- The sum of the three literal rank-one projectors is E E-transpose. -/
theorem columnProjector_sum (E : RealFrame) :
    (∑ k : Fin 3, columnProjector E k) = E * E.transpose := by
  ext i j
  simp only [Matrix.sum_apply,columnProjector,Matrix.vecMulVec_apply,Matrix.mul_apply,Matrix.transpose_apply]

theorem transpose_mul_identity_iff (E : RealFrame) (h : UnitColumns E) :
    E.transpose * E = 1 ↔ OrthogonalColumns E := by
  constructor
  · intro he i j hij
    have hv := congrFun (congrFun he i) j
    simpa [Matrix.mul_apply,Matrix.one_apply,hij] using hv
  · intro ho
    ext i j
    by_cases hij : i = j
    · subst j
      simpa [Matrix.mul_apply,Matrix.one_apply] using h i
    · simpa [Matrix.mul_apply,Matrix.one_apply,hij] using ho i j hij

/-- Three unit real columns sum to the identity projector exactly when pairwise orthogonal. -/
theorem projector_sum_identity_iff (E : RealFrame) (h : UnitColumns E) :
    (∑ k : Fin 3, columnProjector E k) = 1 ↔ OrthogonalColumns E := by
  rw [columnProjector_sum]
  exact (mul_eq_one_comm).trans (transpose_mul_identity_iff E h)

end Holant.Certificates.MatchingProductBridge
