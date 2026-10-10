import Holant.Proofs.Algorithms.TransformRecognition.SymbolicInputTable
import Holant.Proofs.Algorithms.TransformRecognition.StandardRootCodes
import Holant.Proofs.Algorithms.TransformRecognition.LocalAffineNormalForm


namespace Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicPhaseCoefficients
open Holant Holant.Tractable Holant.Algebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
variable {n v : ℕ}

def power (p : Poly v 1) : ℕ → Poly v 1
  | 0 => one RationalCompiler.data
  | k+1 => mul RationalCompiler.data (power p k) p

def supportCheck (C : AffineNormalForm.SupportCode n) (x : Fin n → Bool) : Bool :=
  decide (∀ e ∈ C, (∑ j, e.1 j * bitValue (ZMod 2) (x j))=e.2)

def phaseResidue (C : AffineNormalForm.PhaseCode n) (x : Fin n → Bool) : ZMod 4 :=
  C.1 + (∑ j, C.2.1 j * bitValue (ZMod 4) (x j)) +
    ∑ j, ∑ k, if j < k then
      (if C.2.2 j k then 2 else 0) * bitValue (ZMod 4) (x j) *
        bitValue (ZMod 4) (x k) else 0

def affineCoefficient (imaginary : Fin v) (C : AffineNormalForm.Code n)
    (x : Fin n → Bool) : Poly v 1 :=
  if supportCheck C.1 x then
    power (SparseTransform.variableCode RationalCompiler.data imaginary)
      (phaseResidue C.2 x).val
  else []

def twistCoefficient (eighthRoot : Fin v) (alpha x : Fin n → Bool) : Poly v 1 :=
  SparseTransform.product RationalCompiler.data (List.ofFn (fun j =>
    if alpha j && x j then SparseTransform.variableCode RationalCompiler.data eighthRoot
    else one RationalCompiler.data))

def eighthRootRow (imaginary positiveSqrt eighthRoot : Fin v) : Poly v 1 :=
  sub (mul RationalCompiler.data
    (SparseTransform.variableCode RationalCompiler.data eighthRoot)
    (SparseTransform.variableCode RationalCompiler.data positiveSqrt))
    (add (one RationalCompiler.data)
      (SparseTransform.variableCode RationalCompiler.data imaginary))

noncomputable section

@[simp] theorem rational_one_eval {E : Type*} [Field E] (φ : ℚ →+* E)
    (z : Fin v → E) :
    SparseEvaluation.evaluate RationalCompiler.field φ z (one RationalCompiler.data)=1 :=
  SparseEvaluation.one_eval RationalCompiler.field φ z

@[simp] theorem rational_variable_eval {E : Type*} [Field E] (φ : ℚ →+* E)
    (z : Fin v → E) (j : Fin v) :
    SparseEvaluation.evaluate RationalCompiler.field φ z
      (SparseTransform.variableCode RationalCompiler.data j)=z j :=
  SparseEvaluation.variable_eval RationalCompiler.field φ z j

@[simp] theorem power_eval {E : Type*} [Field E] (φ : ℚ →+* E)
    (z : Fin v → E) (p : Poly v 1) (k : ℕ) :
    SparseEvaluation.evaluate RationalCompiler.field φ z (power p k) =
      SparseEvaluation.evaluate RationalCompiler.field φ z p ^ k := by
  induction k with
  | zero => simp only [power,rational_one_eval,pow_zero]
  | succ k ih =>
    change SparseEvaluation.evaluate RationalCompiler.field φ z
      (mul RationalCompiler.field.toArithmeticData (power p k) p) = _
    rw [SparseEvaluation.mul_eval,ih,pow_succ]

theorem supportCheck_iff (C : AffineNormalForm.SupportCode n) (x : Fin n → Bool) :
    supportCheck C x=true ↔ AffineNormalForm.supportHolds C x := by
  simp [supportCheck,AffineNormalForm.supportHolds,AffineNormalForm.equationHolds]

theorem phaseResidue_eq (C : AffineNormalForm.PhaseCode n) (x : Fin n → Bool) :
    phaseResidue C x=(AffineNormalForm.phase C).eval x := rfl

theorem affineCoefficient_eval (imaginary : Fin v) (C : AffineNormalForm.Code n)
    (x : Fin n → Bool) (z : Fin v → ℂ) (hi : z imaginary=Complex.I) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (affineCoefficient imaginary C x) =
      (AffineNormalForm.formula C 1 x : ℂ) := by
  by_cases h : supportCheck C.1 x=true
  · have hs := (supportCheck_iff C.1 x).mp h
    rw [affineCoefficient,if_pos h,power_eval,rational_variable_eval,hi]
    simp [AffineNormalForm.formula,affineFormula,AffineNormalForm.system_holds,
      hs,fourthRootPhase,phaseResidue_eq]
  · have hs : ¬AffineNormalForm.supportHolds C.1 x :=
      fun hs => h ((supportCheck_iff C.1 x).mpr hs)
    simp [affineCoefficient,h,SparseEvaluation.evaluate,denote,
      AffineNormalForm.formula,affineFormula,AffineNormalForm.system_holds,hs]

theorem twistCoefficient_eval (eighthRoot : Fin v) (alpha x : Fin n → Bool)
    (z : Fin v → ℂ) (hu : z eighthRoot=(zetaEight : ℂ)) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (twistCoefficient eighthRoot alpha x) =
      (LocalAffineTwists.phaseWeight alpha x : ℂ) := by
  unfold twistCoefficient
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (SparseTransform.product RationalCompiler.field.toArithmeticData _) = _
  rw [SparseEvaluation.product_eval]
  simp only [List.map_ofFn,List.prod_ofFn,LocalAffineTwists.phaseWeight,IntermediateField.coe_prod]
  apply Finset.prod_congr rfl
  intro j _
  cases ha : alpha j <;> cases hx : x j <;> simp [ha,hx,hu]

theorem eighthRootRow_eval (imaginary positiveSqrt eighthRoot : Fin v) (z : Fin v → ℂ) :
    SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (eighthRootRow imaginary positiveSqrt eighthRoot) =
      z eighthRoot*z positiveSqrt-(1+z imaginary) := by
  unfold eighthRootRow
  change SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
    (sub (mul RationalCompiler.field.toArithmeticData
      (SparseTransform.variableCode RationalCompiler.field.toArithmeticData eighthRoot)
      (SparseTransform.variableCode RationalCompiler.field.toArithmeticData positiveSqrt))
      (add (one RationalCompiler.field.toArithmeticData)
        (SparseTransform.variableCode RationalCompiler.field.toArithmeticData imaginary))) = _
  simp

theorem eighthRoot_of_row (imaginary positiveSqrt eighthRoot : Fin v) (z : Fin v → ℂ)
    (hi : StandardRootCodes.imaginary.Represents (z imaginary))
    (ht : StandardRootCodes.positiveSqrtTwo.Represents (z positiveSqrt))
    (hr : SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z
      (eighthRootRow imaginary positiveSqrt eighthRoot)=0) :
    z eighthRoot=(zetaEight : ℂ) := by
  rw [eighthRootRow_eval] at hr
  exact StandardRootCodes.eighthRoot_of_bindings _ _ _ hi ht (sub_eq_zero.mp hr)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.SymbolicPhaseCoefficients
