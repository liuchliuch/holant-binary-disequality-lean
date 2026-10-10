import Holant.Tractable.Anchor.MatrixActions

/-!
Literal matrices and projective equality for the marked-sector dictionary,
source Lemma 6.26 (`lem:marked-sector-dictionary`). Scalars are actual algebraic
complex numbers; matrix products use the existing summed Boolean kernels.
-/
namespace Holant.Marked
open Tractable
noncomputable section

abbrev Scalar := AlgebraicComplex
abbrev Mat := Kernel Scalar

def scale (c : Scalar) (A : Mat) : Mat := fun a b => c * A a b

/-- Projective equality with an explicitly nonzero multiplier. -/
def ProjectivelyEqual (A B : Mat) : Prop := ∃ c : Scalar, c ≠ 0 ∧ A = scale c B

namespace ProjectivelyEqual

theorem refl (A : Mat) : ProjectivelyEqual A A := ⟨1, one_ne_zero, by funext a b; simp [scale]⟩

theorem symm {A B : Mat} (h : ProjectivelyEqual A B) : ProjectivelyEqual B A := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨c⁻¹, inv_ne_zero hc, ?_⟩
  funext a b
  simp [scale, hc]

theorem trans {A B C : Mat} (h : ProjectivelyEqual A B)
    (k : ProjectivelyEqual B C) : ProjectivelyEqual A C := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := k
  exact ⟨c * d, mul_ne_zero hc hd, by funext a b; simp [scale, mul_assoc]⟩

end ProjectivelyEqual

theorem scale_mul (c d : Scalar) (A B : Mat) :
    Kernel.mul (scale c A) (scale d B) = scale (c * d) (Kernel.mul A B) := by
  funext a b
  simp only [scale, Kernel.mul_apply]
  ring

theorem scale_mul_left (c : Scalar) (A B : Mat) :
    Kernel.mul (scale c A) B = scale c (Kernel.mul A B) := by
  funext a b; simp only [scale, Kernel.mul_apply]; ring

theorem scale_mul_right (c : Scalar) (A B : Mat) :
    Kernel.mul A (scale c B) = scale c (Kernel.mul A B) := by
  funext a b; simp only [scale, Kernel.mul_apply]; ring

theorem ProjectivelyEqual.mul {A B C D : Mat}
    (h : ProjectivelyEqual A B) (k : ProjectivelyEqual C D) :
    ProjectivelyEqual (Kernel.mul A C) (Kernel.mul B D) := by
  obtain ⟨c, hc, rfl⟩ := h
  obtain ⟨d, hd, rfl⟩ := k
  exact ⟨c * d, mul_ne_zero hc hd, scale_mul c d B D⟩

def R (t : Scalar) : Mat := diagonalKernel 1 t

def S (t : Scalar) : Mat := Kernel.mul Signature.disequality (R t)

def Z : Mat := diagonalKernel 1 (-1)

/-- The manuscript uses the skew matrix Y = ZX, not the Hermitian Pauli Y. -/
def Y : Mat := Kernel.mul Z Signature.disequality

def C (t : Scalar) : Mat := fun a b =>
  (1 + t) * Signature.equality a b + imaginaryUnit * (1 - t) * Y a b

def A (t : Scalar) : Mat := fun a b =>
  (1 + t) * Signature.equality a b + (1 - t) * Signature.disequality a b

def ZA (t : Scalar) : Mat := Kernel.mul Z (A t)

def UB : Mat := fun a b =>
  Signature.equality a b - imaginaryUnit * Signature.disequality a b

def UBInv : Mat := fun a b =>
  (Signature.equality a b + imaginaryUnit * Signature.disequality a b) / 2

/-- H diag(1,s), with the chosen square root retained literally. -/
def UA (s : Scalar) : Mat := fun a b => if b then (if a then -s else s) else 1

def UAInv (s : Scalar) : Mat := fun a b =>
  if a then (if b then -(s⁻¹ / 2) else s⁻¹ / 2) else 1 / 2

theorem imaginaryUnit_ne_zero : imaginaryUnit ≠ 0 := by
  intro h
  have hh := imaginaryUnit_sq
  simp [h] at hh

theorem UB_inverse : Kernel.mul UB UBInv = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [UB, UBInv, Kernel.mul_apply, Signature.equality, Signature.disequality] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem UB_inverse_left : Kernel.mul UBInv UB = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [UB, UBInv, Kernel.mul_apply, Signature.equality, Signature.disequality] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

def basisB : InvertibleKernel := ⟨UB, UBInv, UB_inverse, UB_inverse_left⟩

theorem UA_inverse {s : Scalar} (hs : s ≠ 0) :
    Kernel.mul (UA s) (UAInv s) = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [UA, UAInv, Kernel.mul_apply, Signature.equality] <;> field_simp [hs] <;> ring

theorem UA_inverse_left {s : Scalar} (hs : s ≠ 0) :
    Kernel.mul (UAInv s) (UA s) = Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [UA, UAInv, Kernel.mul_apply, Signature.equality] <;> field_simp [hs] <;> ring

def basisA (s : Scalar) (hs : s ≠ 0) : InvertibleKernel :=
  ⟨UA s, UAInv s, UA_inverse hs, UA_inverse_left hs⟩

def conjugate (U : InvertibleKernel) (T : Mat) : Mat :=
  Kernel.mul (Kernel.mul U.matrix T) U.inverse

theorem conjugate_scale (U : InvertibleKernel) (c : Scalar) (T : Mat) :
    conjugate U (scale c T) = scale c (conjugate U T) := by
  simp [conjugate, scale_mul_left, scale_mul_right]

theorem conjugate_projective (U : InvertibleKernel) {T V : Mat}
    (h : ProjectivelyEqual T V) : ProjectivelyEqual (conjugate U T) (conjugate U V) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨c, hc, conjugate_scale U c V⟩

theorem conjugate_inverse (U : InvertibleKernel) (T : Mat) :
    conjugate U.symm (conjugate U T) = T := by
  simp only [conjugate, InvertibleKernel.symm]
  rw [← Kernel.mul_assoc, ← Kernel.mul_assoc, U.inverse_matrix,
    Kernel.equality_mul, Kernel.mul_assoc, U.inverse_matrix, Kernel.mul_equality]

theorem conjugate_mul (U : InvertibleKernel) (T V : Mat) :
    conjugate U (Kernel.mul T V) = Kernel.mul (conjugate U T) (conjugate U V) := by
  simp only [conjugate]
  simp only [Kernel.mul_assoc]
  rw [← Kernel.mul_assoc U.inverse U.matrix, U.inverse_matrix, Kernel.equality_mul]

theorem conjugateB_R (t : Scalar) :
    conjugate basisB (R t) = scale (1 / 2) (C t) := by
  funext a b
  cases a <;> cases b <;>
    simp [conjugate, basisB, UB, UBInv, R, C, Y, Z, diagonalKernel,
      Kernel.mul_apply, Signature.equality, Signature.disequality, scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem conjugateB_S (t : Scalar) :
    conjugate basisB (S t) = scale (1 / 2) (Kernel.mul Signature.disequality (C t)) := by
  funext a b
  cases a <;> cases b <;>
    simp [conjugate, basisB, UB, UBInv, R, S, C, Y, Z, diagonalKernel,
      Kernel.mul_apply, Signature.equality, Signature.disequality, scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem conjugateA_R {s : Scalar} (hs : s ≠ 0) (t : Scalar) :
    conjugate (basisA s hs) (R t) = scale (1 / 2) (A t) := by
  funext a b
  cases a <;> cases b <;>
    simp [conjugate, basisA, UA, UAInv, R, A, diagonalKernel,
      Kernel.mul_apply, Signature.equality, Signature.disequality, scale] <;>
    field_simp [hs] <;> ring

theorem conjugateA_S {s eta : Scalar} (hs : s ≠ 0) (heta : eta ≠ 0)
    (hsq : s ^ 2 = eta⁻¹) (t : Scalar) :
    conjugate (basisA s hs) (S t) = scale (s / 2) (ZA (eta * t)) := by
  have hsi : s⁻¹ = s * eta := by
    apply (mul_left_inj' hs).mp
    rw [inv_mul_cancel₀ hs]
    calc
      1 = eta⁻¹ * eta := (inv_mul_cancel₀ heta).symm
      _ = s ^ 2 * eta := by rw [hsq]
      _ = s * eta * s := by ring
  funext a b
  cases a <;> cases b <;>
    simp [conjugate, basisA, UA, UAInv, R, S, ZA, Z, A, diagonalKernel,
      Kernel.mul_apply, Signature.equality, Signature.disequality, scale, hsi] <;> ring

theorem edgeM : Kernel.pullback (Signature.disequality : Mat)
    InvertibleKernel.identity.matrix = Signature.disequality := by
  simp [Kernel.pullback, InvertibleKernel.identity]

theorem edgeB : Kernel.pullback Signature.disequality UB =
    scale (-2 * imaginaryUnit) Signature.equality := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.pullback, UB, Kernel.mul_apply, Kernel.transpose,
      Signature.equality, Signature.disequality, scale] <;>
    ring_nf <;> norm_num [imaginaryUnit_sq]

theorem edgeA (s : Scalar) : Kernel.pullback Signature.disequality (UA s) =
    scale 2 (diagonalKernel 1 (-(s ^ 2))) := by
  funext a b
  cases a <;> cases b <;>
    simp [Kernel.pullback, UA, Kernel.mul_apply, Kernel.transpose,
      Signature.disequality, diagonalKernel, scale] <;> ring

theorem edgeA_eta {s eta : Scalar} (hsq : s ^ 2 = eta⁻¹) :
    Kernel.pullback Signature.disequality (UA s) =
      scale 2 (diagonalKernel 1 (-eta⁻¹)) := by rw [edgeA, hsq]

theorem edgeB_multiplier_ne_zero : (-2 * imaginaryUnit : Scalar) ≠ 0 :=
  mul_ne_zero (by norm_num) imaginaryUnit_ne_zero

end
end Holant.Marked
