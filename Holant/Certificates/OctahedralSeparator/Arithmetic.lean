import Holant.Algebraic.GaussianEmbedding
import Mathlib.NumberTheory.Real.Irrational

/-! Exact four-rational arithmetic for Q(sqrt2,i), using an actual quadratic
algebra and a proved faithful embedding into the original complex numbers. -/
namespace Holant.Certificates.OctahedralSeparator
open Holant.Algebraic
open scoped QuadraticAlgebra

abbrev Scalar := QuadraticAlgebra GaussianRational 2 0

/-- (a+b sqrt2)+i(c+d sqrt2), with all four coefficients exact rationals. -/
def coeff (a b c d : ℚ) : Scalar := ⟨⟨a,c⟩,⟨b,d⟩⟩
def rat (q : ℚ) : Scalar := coeff q 0 0 0
def root : Scalar := coeff 0 1 0 0
def imag : Scalar := coeff 0 0 1 0

noncomputable def rootTwo : ℂ := (Real.sqrt 2 : ℂ)

theorem rootTwo_sq : rootTwo^2=2 := by
  unfold rootTwo
  norm_cast
  exact Real.sq_sqrt (by norm_num)

noncomputable def embed (z : Scalar) : ℂ := gaussianToComplex z.re+gaussianToComplex z.im*rootTwo

theorem embed_zero : embed 0=0 := by simp [embed]
theorem embed_one : embed 1=1 := by simp [embed]
theorem embed_add (z w : Scalar) : embed (z+w)=embed z+embed w := by simp [embed]; ring

theorem embed_mul (z w : Scalar) : embed (z*w)=embed z*embed w := by
  simp [embed]
  ring_nf
  simp [rootTwo_sq]
  ring

noncomputable def embedding : Scalar →+* ℂ where
  toFun := embed
  map_zero' := embed_zero
  map_one' := embed_one
  map_add' := embed_add
  map_mul' := embed_mul

theorem embed_coeff (a b c d : ℚ) :
    embed (coeff a b c d) = (a : ℂ)+(b : ℂ)*rootTwo+((c : ℂ)+(d : ℂ)*rootTwo)*Complex.I := by
  simp [embed,coeff,gaussianToComplex_apply]
  ring

theorem embed_re (z : Scalar) : (embed z).re=(z.re.re : ℝ)+(z.im.re : ℝ)*Real.sqrt 2 := by
  simp [embed,gaussianToComplex_apply,rootTwo]

theorem embed_im (z : Scalar) : (embed z).im=(z.re.im : ℝ)+(z.im.im : ℝ)*Real.sqrt 2 := by
  simp [embed,gaussianToComplex_apply,rootTwo]

theorem sqrt_linear_zero (a b : ℚ) (h : (a : ℝ)+(b : ℝ)*Real.sqrt 2=0) : a=0 ∧ b=0 := by
  by_cases hb : b=0
  · refine ⟨?_,hb⟩
    exact_mod_cast (by simpa [hb] using h : (a : ℝ)=0)
  · have hb' : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    have hs : Real.sqrt 2 = ((-a/b : ℚ) : ℝ) := by
      push_cast
      apply (eq_div_iff hb').mpr
      linarith
    exact False.elim ((irrational_sqrt_two.ne_rat (-a/b)) hs)

theorem embed_injective : Function.Injective embed := by
  intro z w h
  have hr := congrArg Complex.re h
  have hi := congrArg Complex.im h
  simp only [embed_re] at hr
  simp only [embed_im] at hi
  have hrr : ((z.re.re-w.re.re : ℚ) : ℝ)+((z.im.re-w.im.re : ℚ) : ℝ)*Real.sqrt 2=0 := by
    push_cast
    linarith
  have hii : ((z.re.im-w.re.im : ℚ) : ℝ)+((z.im.im-w.im.im : ℚ) : ℝ)*Real.sqrt 2=0 := by
    push_cast
    linarith
  obtain ⟨har,hbr⟩ := sqrt_linear_zero _ _ hrr
  obtain ⟨hai,hbi⟩ := sqrt_linear_zero _ _ hii
  ext <;> linarith

theorem embed_ne_zero {z : Scalar} (h : z ≠ 0) : embed z ≠ 0 := by
  intro he
  apply h
  exact embed_injective (he.trans embed_zero.symm)

example : root*root=rat 2 := by decide +kernel
example : imag*imag=rat (-1) := by decide +kernel

end Holant.Certificates.OctahedralSeparator
