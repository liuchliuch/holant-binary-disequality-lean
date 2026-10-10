import Holant.Tractable.SymmetricBinaryPullback.LocalAffine
import Holant.Tractable.Anchor.MatrixActions

/-! Actual complex bases and their exact algebraic coefficient embeddings.
These are two-sided invertible matrices, with no unitary or reality restriction. -/
namespace Holant.EightVertex.LocalAffineCollapse
open Holant.Tractable
noncomputable section
set_option backward.isDefEq.respectTransparency false

structure ComplexBasis where
  matrix : Kernel ℂ
  inverse : Kernel ℂ
  matrix_inverse : Kernel.mul matrix inverse=Signature.equality
  inverse_matrix : Kernel.mul inverse matrix=Signature.equality

namespace ComplexBasis
def symm (T : ComplexBasis) : ComplexBasis :=
  ⟨T.inverse,T.matrix,T.inverse_matrix,T.matrix_inverse⟩

def comp (T U : ComplexBasis) : ComplexBasis where
  matrix := Kernel.mul T.matrix U.matrix
  inverse := Kernel.mul U.inverse T.inverse
  matrix_inverse := by
    rw [Kernel.mul_assoc,←Kernel.mul_assoc U.matrix U.inverse T.inverse,
      U.matrix_inverse,Kernel.equality_mul,T.matrix_inverse]
  inverse_matrix := by
    rw [Kernel.mul_assoc,←Kernel.mul_assoc T.inverse T.matrix U.matrix,
      T.inverse_matrix,Kernel.equality_mul,U.inverse_matrix]

def action (T : ComplexBasis) {n : ℕ} (f : Signature ℂ n) : Signature ℂ n :=
  Signature.coordinateAction (fun _ => T.matrix) f

theorem action_symm_action (T : ComplexBasis) {n : ℕ} (f : Signature ℂ n) :
    T.action (T.symm.action f)=f :=
  Signature.coordinateAction_cancel _ _ (fun _ => T.matrix_inverse) f
theorem symm_action_action (T : ComplexBasis) {n : ℕ} (f : Signature ℂ n) :
    T.symm.action (T.action f)=f :=
  Signature.coordinateAction_cancel _ _ (fun _ => T.inverse_matrix) f
theorem comp_action (T U : ComplexBasis) {n : ℕ} (f : Signature ℂ n) :
    (T.comp U).action f=T.action (U.action f) := (Signature.coordinateAction_comp _ _ _).symm
end ComplexBasis

def complexDet (T : Kernel ℂ) : ℂ := T false false*T true true-T false true*T true false
theorem complexDet_mul (T U : Kernel ℂ) : complexDet (Kernel.mul T U)=complexDet T*complexDet U := by
  simp only [complexDet,Kernel.mul_apply]
  ring
theorem complexDet_ne_zero (T : ComplexBasis) : complexDet T.matrix≠0 := by
  intro hz
  have h := congrArg complexDet T.matrix_inverse
  rw [complexDet_mul,hz,zero_mul] at h
  norm_num [complexDet,Signature.equality] at h

def complexAdj (T : Kernel ℂ) : Kernel ℂ
  | false,false => T true true
  | false,true => -T false true
  | true,false => -T true false
  | true,true => T false false

def basisOfDet (T : Kernel ℂ) (hT : complexDet T≠0) : ComplexBasis where
  matrix := T
  inverse := fun a b => complexAdj T a b/complexDet T
  matrix_inverse := by
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply,complexAdj,Signature.equality]
    all_goals field_simp
    all_goals simp only [complexDet]
    all_goals ring
  inverse_matrix := by
    funext a b
    cases a <;> cases b <;> simp [Kernel.mul_apply,complexAdj,Signature.equality]
    all_goals field_simp
    all_goals simp only [complexDet]
    all_goals ring

def complexDiagonal (a b : ℂ) : Kernel ℂ :=
  fun x y => if x=y then (if x then b else a) else 0

def complexDiagonalBasis (a b : ℂ) (ha : a≠0) (hb : b≠0) : ComplexBasis where
  matrix := complexDiagonal a b
  inverse := complexDiagonal a⁻¹ b⁻¹
  matrix_inverse := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,complexDiagonal,Signature.equality,ha,hb]
  inverse_matrix := by
    funext x y
    cases x <;> cases y <;> simp [Kernel.mul_apply,complexDiagonal,Signature.equality,ha,hb]

def embedMatrix (T : Kernel AlgebraicComplex) : Kernel ℂ := fun a b => (T a b : ℂ)
def embedSignature {n : ℕ} (f : Signature AlgebraicComplex n) : Signature ℂ n := fun x => (f x : ℂ)

theorem embedMatrix_mul (T U : Kernel AlgebraicComplex) :
    embedMatrix (Kernel.mul T U)=Kernel.mul (embedMatrix T) (embedMatrix U) := by
  funext a b
  simp [embedMatrix,Kernel.mul_apply]
theorem embedMatrix_equality : embedMatrix Signature.equality=Signature.equality := by
  funext a b
  cases a <;> cases b <;> rfl
theorem embedMatrix_diagonal (a b : AlgebraicComplex) :
    embedMatrix (diagonalKernel a b)=complexDiagonal a b := by
  funext x y
  cases x <;> cases y <;> rfl
theorem embedMatrix_pullback (T : Kernel AlgebraicComplex) :
    embedMatrix (Kernel.pullback Signature.disequality T)=
      Kernel.pullback Signature.disequality (embedMatrix T) := by
  funext a b
  simp [embedMatrix,Kernel.pullback,Kernel.mul_apply,Kernel.transpose,Signature.disequality]

theorem embed_action {n : ℕ} (T : Fin n → Kernel AlgebraicComplex) (f : Signature AlgebraicComplex n) :
    embedSignature (Signature.coordinateAction T f)=
      Signature.coordinateAction (fun i => embedMatrix (T i)) (embedSignature f) := by
  funext x
  simp [embedSignature,embedMatrix,Signature.coordinateAction]

def ofAlgebraic (T : InvertibleKernel) : ComplexBasis where
  matrix := embedMatrix T.matrix
  inverse := embedMatrix T.inverse
  matrix_inverse := by rw [←embedMatrix_mul,T.matrix_inverse,embedMatrix_equality]
  inverse_matrix := by rw [←embedMatrix_mul,T.inverse_matrix,embedMatrix_equality]

theorem embed_action_basis {n : ℕ} (T : InvertibleKernel) (f : Signature AlgebraicComplex n) :
    embedSignature (T.action f)=(ofAlgebraic T).action (embedSignature f) := embed_action _ _

end
end Holant.EightVertex.LocalAffineCollapse
