import Holant.Certificates.OctahedralSeparator.Arithmetic

/-! The four-coordinate algebra is an actual field: sqrt2 has no Gaussian
rational square root. Its executable inverses therefore embed exactly in ℂ. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant.Algebraic
open scoped QuadraticAlgebra

instance scalar_no_root : Fact (∀ r : GaussianRational, r^2 ≠ (2 : GaussianRational)+0*r) := by
  constructor
  intro r h
  have hr := congrArg QuadraticAlgebra.re h
  have hi := congrArg QuadraticAlgebra.im h
  simp [pow_two] at hr hi
  have hh : r.re*r.im=0 := by linarith
  rcases mul_eq_zero.mp hh with ha | hb
  · rw [ha] at hr
    nlinarith [sq_nonneg r.im]
  · rw [hb] at hr
    have hs : (r.re : ℝ)^2=(Real.sqrt 2)^2 := by
      rw [Real.sq_sqrt (by norm_num)]
      exact_mod_cast (by nlinarith [hr] : r.re^2=2)
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hs with he | he
    · exact (irrational_sqrt_two.ne_rat r.re) he.symm
    · apply (irrational_sqrt_two.ne_rat (-r.re))
      push_cast
      linarith

noncomputable def fieldEmbedding : Scalar →+* ℂ := embedding

theorem embed_inv (z : Scalar) : embed z⁻¹=(embed z)⁻¹ := map_inv₀ fieldEmbedding z

theorem embed_div (z w : Scalar) : embed (z/w)=embed z/embed w := map_div₀ fieldEmbedding z w

example : (root+1)⁻¹=root-1 := by decide +kernel
example : imag⁻¹= -imag := by decide +kernel

end Holant.Certificates.OctahedralSeparator
