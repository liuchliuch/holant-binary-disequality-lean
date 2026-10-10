import Holant.Algebraic.QuadraticField
import Holant.NetworkAlgebra
import Mathlib.Analysis.Complex.Basic

/-! A concrete bridge from executable Gaussian-rational arithmetic to the
complex-valued finite-network semantics. There is no runtime claim for the
exponential enumeration in the generic network definition. -/

namespace Holant.Algebraic

/-- Interpret the Gaussian generator as the actual complex imaginary unit. -/
noncomputable def gaussianToComplex : GaussianRational →+* ℂ :=
  (QuadraticAlgebra.lift
    (show { u : ℂ // u * u = (-1 : ℚ) • 1 + (0 : ℚ) • u } from
      ⟨Complex.I, by simp⟩)).toRingHom

/-- The embedding does not identify distinct exact Gaussian rational values. -/
theorem gaussianToComplex_injective : Function.Injective gaussianToComplex :=
  gaussianToComplex.injective

@[simp] theorem gaussianToComplex_apply (z : GaussianRational) :
    gaussianToComplex z = (z.re : ℂ) + (z.im : ℂ) * Complex.I := by
  simp [gaussianToComplex, QuadraticAlgebra.lift, Algebra.smul_def]

/-- Exact finite-network evaluation over Gaussian rational arithmetic agrees
with evaluation of its interpreted algebraic complex coefficients. -/
theorem gaussianNetwork_denote {n : ℕ} (N : Holant.Network GaussianRational n)
    (x : Fin n → Bool) :
    (N.map gaussianToComplex).denote x = gaussianToComplex (N.denote x) :=
  Holant.Network.denote_map gaussianToComplex N x

/-- The computed exact Gaussian answer has a faithful binary encoding. -/
def gaussianNetworkBits {n : ℕ} (N : Holant.Network GaussianRational n)
    (x : Fin n → Bool) : List Bool := gaussianEncoding.encode (N.denote x)

@[simp] theorem gaussianNetworkBits_decode {n : ℕ} (N : Holant.Network GaussianRational n)
    (x : Fin n → Bool) :
    gaussianEncoding.decode (gaussianNetworkBits N x) = some (N.denote x) :=
  gaussianEncoding.decode_encode _

end Holant.Algebraic
