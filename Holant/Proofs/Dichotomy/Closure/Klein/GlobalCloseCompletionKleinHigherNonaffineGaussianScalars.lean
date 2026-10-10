import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHigherNonaffineRecoupling

/-! Exact Gaussian-rational units for every scalar in the Pauli Klein
Gram, dual, transpose, fusion, and four-port recoupling identities. -/

namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
noncomputable section

/-- The literal nonzero Gram scalar, equal to two or four. -/
def gaussianD (a : Label) : Algebraic.GaussianRational := dOver a

/-- The actual reciprocal Gram scalar used to normalize the dual basis. -/
def gaussianDualScalar (a : Label) : Algebraic.GaussianRational := (gaussianD a)⁻¹

def gaussianTransposeScalar (a : Label) : Algebraic.GaussianRational :=
  if a = zLabel then -1 else 1

/-- The literal fusion table, with the exact Gaussian generator in place of
the complex imaginary unit. -/
def gaussianOmega (a b : Label) : Algebraic.GaussianRational :=
  if a.2 = 1 ∧ b.1 = 1 then -1 else 1

@[simp] theorem map_gaussianD (a : Label) :
    Algebraic.gaussianToComplex (gaussianD a) = d a := by
  unfold gaussianD d dOver
  exact map_ofNat _ _

@[simp] theorem map_gaussianDualScalar (a : Label) :
    Algebraic.gaussianToComplex (gaussianDualScalar a) = (d a)⁻¹ := by
  rw [gaussianDualScalar, map_inv₀, map_gaussianD]

@[simp] theorem map_gaussianTransposeScalar (a : Label) :
    Algebraic.gaussianToComplex (gaussianTransposeScalar a) = transposeScalar a := by
  unfold gaussianTransposeScalar transposeScalar
  split_ifs <;> simp only [map_one, map_neg]

@[simp] theorem map_gaussianOmega (a b : Label) :
    Algebraic.gaussianToComplex (gaussianOmega a b) = omega a b := by
  unfold gaussianOmega omega
  split_ifs <;> simp only [map_one, map_neg, map_ofNat, map_mul, map_gaussianI]

@[simp] theorem gaussianD_ne_zero (a : Label) : gaussianD a ≠ 0 := by
  intro h
  exact d_ne_zero a (by rw [← map_gaussianD, h, map_zero])

@[simp] theorem gaussianDualScalar_ne_zero (a : Label) : gaussianDualScalar a ≠ 0 :=
  inv_ne_zero (gaussianD_ne_zero a)

@[simp] theorem gaussianTransposeScalar_ne_zero (a : Label) : gaussianTransposeScalar a ≠ 0 := by
  intro h
  exact transposeScalar_ne_zero a (by rw [← map_gaussianTransposeScalar, h, map_zero])

@[simp] theorem gaussianOmega_ne_zero (a b : Label) : gaussianOmega a b ≠ 0 := by
  intro h
  exact omega_ne_zero a b (by rw [← map_gaussianOmega, h, map_zero])

@[simp] theorem gaussianRhoCross_ne_zero (a b g : Label) : gaussianRhoCross a b g ≠ 0 := by
  intro h
  exact rhoCross_ne_zero a b g (by rw [← map_gaussianRhoCross, h, map_zero])

@[simp] theorem gaussianRhoParallel_ne_zero (a b g : Label) : gaussianRhoParallel a b g ≠ 0 := by
  intro h
  exact rhoParallel_ne_zero a b g (by rw [← map_gaussianRhoParallel, h, map_zero])

/-- The Gram formula itself holds over the exact Gaussian-rational field. -/
theorem gaussian_gram (a b : Label) :
    Kernel.pair (gaussianE a) (gaussianE b) =
      gaussianD a * (if b = theta a then 1 else 0) := by
  apply Algebraic.gaussianToComplex_injective
  by_cases hab : b = theta a <;>
    simp only [Kernel.pair, map_sum, map_mul, map_gaussianE, map_gaussianD,
      hab, ite_true, ite_false, map_one, map_zero] <;>
    simpa only [Kernel.pair, hab, ite_true, ite_false] using gram a b

/-- The recorded unit is the literal normalization scalar in every entry
of the exact dual matrix. -/
theorem gaussian_dual_normalization (a : Label) (x y : Bool) :
    gaussianDual a x y = gaussianDualScalar a * gaussianE (theta a) x y := rfl

theorem gaussian_transpose_E (a : Label) :
    Kernel.transpose (gaussianE a) =
      fun x y => gaussianTransposeScalar a * gaussianE (theta a) x y := by
  funext x y
  apply Algebraic.gaussianToComplex_injective
  simp only [Kernel.transpose_apply, map_mul, map_gaussianE, map_gaussianTransposeScalar]
  exact congrFun (congrFun (transpose_E a) x) y

theorem gaussian_fusion (a b : Label) :
    Kernel.mul (gaussianE a) (gaussianE b) =
      fun x y => gaussianOmega a b * gaussianE (a + b) x y := by
  funext x y
  apply Algebraic.gaussianToComplex_injective
  simp only [Kernel.mul, map_sum, map_mul, map_gaussianE, map_gaussianOmega]
  exact congrFun (congrFun (fusion a b) x) y

/-- These units retain the actual scalar values, rather than merely
asserting that unspecified Gaussian-rational witnesses exist. -/
def gaussianDUnit (a : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianD a) (gaussianD_ne_zero a)

def gaussianDualScalarUnit (a : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianDualScalar a) (gaussianDualScalar_ne_zero a)

def gaussianTransposeScalarUnit (a : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianTransposeScalar a) (gaussianTransposeScalar_ne_zero a)

def gaussianOmegaUnit (a b : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianOmega a b) (gaussianOmega_ne_zero a b)

def gaussianRhoCrossUnit (a b g : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianRhoCross a b g) (gaussianRhoCross_ne_zero a b g)

def gaussianRhoParallelUnit (a b g : Label) : (Algebraic.GaussianRational)ˣ :=
  Units.mk0 (gaussianRhoParallel a b g) (gaussianRhoParallel_ne_zero a b g)

@[simp] theorem map_gaussianDUnit (a : Label) :
    Algebraic.gaussianToComplex (gaussianDUnit a) = d a := map_gaussianD a

@[simp] theorem map_gaussianDualScalarUnit (a : Label) :
    Algebraic.gaussianToComplex (gaussianDualScalarUnit a) = (d a)⁻¹ := map_gaussianDualScalar a

@[simp] theorem map_gaussianTransposeScalarUnit (a : Label) :
    Algebraic.gaussianToComplex (gaussianTransposeScalarUnit a) = transposeScalar a :=
  map_gaussianTransposeScalar a

@[simp] theorem map_gaussianOmegaUnit (a b : Label) :
    Algebraic.gaussianToComplex (gaussianOmegaUnit a b) = omega a b := map_gaussianOmega a b

@[simp] theorem map_gaussianRhoCrossUnit (a b g : Label) :
    Algebraic.gaussianToComplex (gaussianRhoCrossUnit a b g) = rhoCross a b g :=
  map_gaussianRhoCross a b g

@[simp] theorem map_gaussianRhoParallelUnit (a b g : Label) :
    Algebraic.gaussianToComplex (gaussianRhoParallelUnit a b g) = rhoParallel a b g :=
  map_gaussianRhoParallel a b g

theorem gaussianDualScalarUnit_eq_inv (a : Label) :
    gaussianDualScalarUnit a = (gaussianDUnit a)⁻¹ := by
  apply Units.ext
  rfl

end
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionKleinHigherNonaffine
