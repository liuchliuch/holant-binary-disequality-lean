import Holant.Certificates.MatchingProductBridge.PlatonicModels
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Nonsingularity is derived from the literal quaternion representative families,
including the golden-ratio family. It is not postulated as an extra group axiom. -/
namespace Holant.Certificates.MatchingProductBridge
noncomputable section
set_option backward.isDefEq.respectTransparency false

def axisVector (i : Fin 4) : Fin 4 → ℝ := fun j => if j = i then 1 else 0

def quaternionNorm (v : Fin 4 → ℝ) : ℝ := (v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2

def quaternionConjugate (v : Fin 4 → ℝ) : Binary := fun a b =>
  (v 0 : ℂ)*Q0 a b-(v 1 : ℂ)*Q1 a b-(v 2 : ℂ)*Q2 a b-(v 3 : ℂ)*Q3 a b

theorem quaternion_axis (i : Fin 4) : quaternion (axisVector i) = quaternionBasis i := by
  fin_cases i <;> funext a b <;> simp [quaternion,quaternionBasis,axisVector]

theorem axisVector_ne_zero (i : Fin 4) : axisVector i ≠ 0 := by
  intro h
  have hi := congrFun h i
  simp [axisVector] at hi

theorem quaternion_add (u v : Fin 4 → ℝ) : quaternion (u+v) = quaternion u + quaternion v := by
  funext a b
  simp [quaternion,Complex.ofReal_add]
  ring

theorem quaternion_real_smul (r : ℝ) (v : Fin 4 → ℝ) :
    quaternion (r • v) = (r : ℂ) • quaternion v := by
  funext a b
  simp [quaternion,smul_eq_mul,Complex.ofReal_mul]
  ring

theorem quaternionNorm_pos (v : Fin 4 → ℝ) (hv : v ≠ 0) : 0 < quaternionNorm v := by
  have h0 := sq_nonneg (v 0)
  have h1 := sq_nonneg (v 1)
  have h2 := sq_nonneg (v 2)
  have h3 := sq_nonneg (v 3)
  by_contra hn
  have hh : (v 0)^2+(v 1)^2+(v 2)^2+(v 3)^2 ≤ 0 := le_of_not_gt hn
  have e0 : (v 0)^2 = 0 := by linarith
  have e1 : (v 1)^2 = 0 := by linarith
  have e2 : (v 2)^2 = 0 := by linarith
  have e3 : (v 3)^2 = 0 := by linarith
  apply hv
  funext i
  fin_cases i
  · exact sq_eq_zero_iff.mp e0
  · exact sq_eq_zero_iff.mp e1
  · exact sq_eq_zero_iff.mp e2
  · exact sq_eq_zero_iff.mp e3

theorem multiply_eq_matrix_mul (U V : Binary) :
    Matrix.of (multiply U V) = Matrix.of U * Matrix.of V := by
  ext a b
  simp [multiply,Matrix.mul_apply,Matrix.of_apply,add_comm]

theorem quaternion_mul_conjugate_four (v : Fin 4 → ℝ) :
    multiply (quaternion v) (quaternionConjugate v) = (quaternionNorm v : ℂ) • Q0 := by
  funext a b
  cases a <;> cases b <;>
    simp [multiply,quaternion,quaternionConjugate,quaternionNorm,Q0,Q1,Q2,Q3,
      Holant.Signature.equality,smul_eq_mul,Complex.ofReal_add,Complex.ofReal_pow] <;>
    ring_nf <;> simp [Complex.I_sq] <;> ring

theorem Q0_eq_matrix_one : Matrix.of Q0 = (1 : Matrix Bool Bool ℂ) := by
  funext a b
  simp [Q0,Holant.Signature.equality,Matrix.one_apply]

theorem quaternion_det_ne_zero (v : Fin 4 → ℝ) (hv : v ≠ 0) :
    Matrix.det (Matrix.of (quaternion v)) ≠ 0 := by
  have hn : (quaternionNorm v : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (quaternionNorm_pos v hv))
  have hp : Matrix.of (quaternion v) * Matrix.of (quaternionConjugate v) =
      (quaternionNorm v : ℂ) • (1 : Matrix Bool Bool ℂ) := by
    rw [← multiply_eq_matrix_mul]
    have he := quaternion_mul_conjugate_four v
    rw [he]
    change (quaternionNorm v : ℂ) • Matrix.of Q0 = _
    rw [Q0_eq_matrix_one]
  have hh := congrArg Matrix.det hp
  rw [Matrix.det_mul,Matrix.det_smul,Matrix.det_one] at hh
  intro hd
  rw [hd,zero_mul,mul_one] at hh
  exact (pow_ne_zero _ hn) hh.symm

/-- Every literal base matrix has a nonzero real quaternion coefficient vector. -/
theorem tetrahedralBase_quaternion {U : Binary} (h : tetrahedralBase U) :
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ U = quaternion v := by
  rcases h with ⟨i,rfl⟩ | ⟨ε,rfl⟩
  · exact ⟨axisVector i,axisVector_ne_zero i,(quaternion_axis i).symm⟩
  · refine ⟨![1,signBit (ε 0),signBit (ε 1),signBit (ε 2)],?_,rfl⟩
    intro hz
    have hh := congrFun hz 0
    norm_num at hh

theorem octahedralBase_quaternion {U : Binary} (h : octahedralBase U) :
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ U = quaternion v := by
  rcases h with h | ⟨i,j,hij,ε,rfl⟩
  · exact tetrahedralBase_quaternion h
  · refine ⟨axisVector i+signBit ε • axisVector j,?_,?_⟩
    · intro hz
      have hh := congrFun hz i
      simp [axisVector,ne_of_lt hij] at hh
    · rw [quaternion_add,quaternion_real_smul,quaternion_axis,quaternion_axis]

theorem icosahedralBase_quaternion {U : Binary} (h : icosahedralBase U) :
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ U = quaternion v := by
  rcases h with h | ⟨π,_,ε,rfl⟩
  · exact tetrahedralBase_quaternion h
  · refine ⟨fun i => goldenVector ε (π.symm i),?_,rfl⟩
    intro hz
    have hh := congrFun hz (π 1)
    simp only [Equiv.symm_apply_apply,Pi.zero_apply] at hh
    change signBit (ε 0) = 0 at hh
    cases he : ε 0 <;> simp [signBit,he] at hh

theorem modelBase_quaternion (g : PlatonicModel) {U : Binary} (h : modelBase g U) :
    ∃ v : Fin 4 → ℝ, v ≠ 0 ∧ U = quaternion v := by
  cases g
  · exact tetrahedralBase_quaternion h
  · exact octahedralBase_quaternion h
  · exact icosahedralBase_quaternion h

/-- Every projective group direction is nonsingular, derived from its actual source family. -/
theorem groupDirection_det_ne_zero (g : PlatonicModel) {U : Binary} (h : groupDirection g U) :
    Matrix.det (Matrix.of U) ≠ 0 := by
  rcases h with ⟨c,hc,V,hV,rfl⟩
  rcases modelBase_quaternion g hV with ⟨v,hv,rfl⟩
  change Matrix.det (c • Matrix.of (quaternion v)) ≠ 0
  rw [Matrix.det_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) (quaternion_det_ne_zero v hv)

end
end Holant.Certificates.MatchingProductBridge
