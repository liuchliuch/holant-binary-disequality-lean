import Holant.Certificates.OctahedralSeparator.Data
import Holant.Certificates.MatchingProductBridge.GroupInverses

/-! Faithful complex matrix semantics of the exact four-rational data.  Products
and inverses below use the actual matrix operations, not entrywise operations. -/
namespace Holant.Certificates.OctahedralSeparator
noncomputable section
set_option backward.isDefEq.respectTransparency false
open Holant.Certificates.MatchingProductBridge

@[simp] theorem embed_neg (z : Scalar) : embed (-z) = -embed z := map_neg embedding z
@[simp] theorem embed_sub (z w : Scalar) : embed (z-w) = embed z-embed w := map_sub embedding z w

/-- Entrywise faithful field embedding, with genuine matrix-valued codomain. -/
def complexMatrix (U : Mat) : Matrix Bool Bool ℂ := fun a b => embed (U a b)

@[simp] theorem complexMatrix_apply (U : Mat) (a b : Bool) :
    complexMatrix U a b = embed (U a b) := rfl

theorem complexMatrix_injective : Function.Injective complexMatrix := by
  intro U V h
  funext a b
  exact embed_injective (congrFun (congrFun h a) b)

@[simp] theorem complexMatrix_add (U V : Mat) :
    complexMatrix (U+V) = complexMatrix U+complexMatrix V := by
  ext a b
  exact embed_add _ _

@[simp] theorem complexMatrix_sub (U V : Mat) :
    complexMatrix (U-V) = complexMatrix U-complexMatrix V := by
  ext a b
  exact map_sub embedding _ _

@[simp] theorem complexMatrix_ms (c : Scalar) (U : Mat) :
    complexMatrix (ms c U) = embed c • complexMatrix U := by
  ext a b
  exact embed_mul _ _

@[simp] theorem complexMatrix_mm (U V : Mat) :
    complexMatrix (mm U V) = complexMatrix U * complexMatrix V := by
  ext a b
  simp [complexMatrix,mm,Matrix.mul_apply,embed_add,embed_mul]
  ring

@[simp] theorem complexMatrix_mt (U : Mat) :
    complexMatrix (mt U) = (complexMatrix U).transpose := rfl

@[simp] theorem complexMatrix_q0 : complexMatrix (q 0) = 1 := by
  ext a b
  cases a <;> cases b <;> simp [complexMatrix,q,mat,Matrix.one_apply,embed_zero,embed_one]

@[simp] theorem complexMatrix_flip : complexMatrix flip = Matrix.of X := by
  ext a b
  cases a <;> cases b <;> simp [complexMatrix,flip,mat,X,Holant.Signature.disequality,embed_zero,embed_one]

@[simp] theorem embed_determinant (U : Mat) :
    embed (determinant U) = Matrix.det (complexMatrix U) := by
  change embed (determinant U) = Matrix.det (Matrix.of (complexMatrix U))
  rw [← binaryDeterminant_eq_det]
  simp [determinant,binaryDeterminant,complexMatrix,embed_mul]

theorem mm_assoc (U V W : Mat) : mm (mm U V) W = mm U (mm V W) := by
  funext a b
  simp only [mm]
  ring

@[simp] theorem mm_q0 (U : Mat) : mm U (q 0) = U := by
  funext a b
  cases b <;> simp [mm,q,mat]

@[simp] theorem q0_mm (U : Mat) : mm (q 0) U = U := by
  funext a b
  cases a <;> simp [mm,q,mat]

theorem theta_ms (f : Form) (c : Scalar) (U : Mat) :
    theta f (ms c U) = ms c (theta f U) := by
  funext a b
  simp only [theta,mm,ms]
  ring

theorem theta_mm (f : Form) (U V : Mat) :
    theta f (mm U V) = mm (theta f U) (theta f V) := by
  simp only [theta]
  simp only [mm_assoc]
  rw [← mm_assoc (conjugator f) (inverseConjugator f),
    (conjugator_inverses f).1,q0_mm]

theorem theta_pull (f : Form) (U : Mat) : theta f (pull f U) = U := by
  simp only [theta,pull]
  rw [← mm_assoc,← mm_assoc,(conjugator_inverses f).2,q0_mm,mm_assoc,
    (conjugator_inverses f).2,mm_q0]

theorem pull_theta (f : Form) (U : Mat) : pull f (theta f U) = U := by
  simp only [theta,pull]
  rw [← mm_assoc,← mm_assoc,(conjugator_inverses f).1,q0_mm,mm_assoc,
    (conjugator_inverses f).1,mm_q0]

/-- This equality specifies the genuine nonsingular matrix inverse. -/
theorem complexMatrix_inverseConjugator (f : Form) :
    complexMatrix (inverseConjugator f) = (complexMatrix (conjugator f))⁻¹ := by
  symm
  apply Matrix.inv_eq_right_inv
  rw [← complexMatrix_mm,(conjugator_inverses f).1,complexMatrix_q0]

theorem complexMatrix_conjugator_det_ne_zero (f : Form) :
    Matrix.det (complexMatrix (conjugator f)) ≠ 0 := by
  rw [← embed_determinant]
  exact embed_ne_zero (conjugator_det_nonzero f)

def complexTheta (f : Form) (U : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  (complexMatrix (conjugator f))⁻¹ * (U * complexMatrix (conjugator f))

def complexPull (f : Form) (U : Matrix Bool Bool ℂ) : Matrix Bool Bool ℂ :=
  complexMatrix (conjugator f) * (U * (complexMatrix (conjugator f))⁻¹)

@[simp] theorem complexMatrix_theta (f : Form) (U : Mat) :
    complexMatrix (theta f U) = complexTheta f (complexMatrix U) := by
  simp [theta,complexTheta,complexMatrix_inverseConjugator]

@[simp] theorem complexMatrix_pull (f : Form) (U : Mat) :
    complexMatrix (pull f U) = complexPull f (complexMatrix U) := by
  simp [pull,complexPull,complexMatrix_inverseConjugator]

theorem complexTheta_smul (f : Form) (c : ℂ) (U : Matrix Bool Bool ℂ) :
    complexTheta f (c • U) = c • complexTheta f U := by
  simp [complexTheta,Matrix.smul_mul,Matrix.mul_smul]

theorem complexPull_smul (f : Form) (c : ℂ) (U : Matrix Bool Bool ℂ) :
    complexPull f (c • U) = c • complexPull f U := by
  simp [complexPull,Matrix.smul_mul,Matrix.mul_smul]

theorem complexTheta_complexPull (f : Form) (U : Matrix Bool Bool ℂ) :
    complexTheta f (complexPull f U) = U := by
  have hi := Matrix.nonsing_inv_mul (complexMatrix (conjugator f))
    (isUnit_iff_ne_zero.mpr (complexMatrix_conjugator_det_ne_zero f))
  simp only [complexTheta,complexPull]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hi,Matrix.one_mul,Matrix.mul_assoc,hi,Matrix.mul_one]

theorem complexPull_complexTheta (f : Form) (U : Matrix Bool Bool ℂ) :
    complexPull f (complexTheta f U) = U := by
  have hi := Matrix.mul_nonsing_inv (complexMatrix (conjugator f))
    (isUnit_iff_ne_zero.mpr (complexMatrix_conjugator_det_ne_zero f))
  simp only [complexTheta,complexPull]
  rw [← Matrix.mul_assoc,← Matrix.mul_assoc,hi,Matrix.one_mul,Matrix.mul_assoc,hi,Matrix.mul_one]

end
end Holant.Certificates.OctahedralSeparator
