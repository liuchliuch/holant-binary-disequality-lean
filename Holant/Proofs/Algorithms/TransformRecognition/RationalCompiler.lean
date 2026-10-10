import Holant.Proofs.Algorithms.TransformRecognition.SparseEvaluation
import Mathlib.LinearAlgebra.Basis.Basic


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalCompiler
open Holant.Algebraic Module
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse

def data : ArithmeticData 1 where
  unitCode := fun _ => 1
  mulTable := fun _ _ _ => 1

noncomputable def field : FixedField ℚ 1 where
  toArithmeticData := data
  basis := Basis.singleton (Fin 1) ℚ
  unit_spec := by
    rw [Basis.equivFun_symm_apply]
    simp [data]
  mul_spec := by
    intro i j
    rw [Basis.equivFun_symm_apply]
    simp [data]

theorem decode_eq (v : Fin 1 → ℚ) : field.decode v = v 0 := by
  change (Basis.singleton (Fin 1) ℚ).equivFun.symm v = v 0
  rw [Basis.equivFun_symm_apply]
  simp

/-- Coefficients in this representation are literal rational numbers. -/
def constant {v : ℕ} (q : ℚ) : Poly v 1 := SparseTransform.constant (fun _ => q)

@[simp] theorem constant_eval {E : Type*} [Field E] (φ : ℚ →+* E)
    {v : ℕ} (z : Fin v → E) (q : ℚ) :
    SparseEvaluation.evaluate field φ z (constant q) = φ q := by
  rw [constant,SparseEvaluation.constant_eval,decode_eq]

end Holant.LocalDrafts.MainChain.TransformRecognition.RationalCompiler
