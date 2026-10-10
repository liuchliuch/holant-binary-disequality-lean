import Holant.Proofs.Algorithms.TransformRecognition.SparseCoefficientInput
import Holant.Proofs.Algorithms.TransformRecognition.OriginalCoefficientBindings
import Holant.Proofs.Algorithms.TransformRecognition.RationalCompiler


namespace Holant.LocalDrafts.MainChain.TransformRecognition.RationalInputSystem
open Holant.Algebraic MvPolynomial
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.Sparse
variable {m n : ℕ}

abbrev count (S : List (Poly n 1)) :=
  (SparseCoefficientInput.coefficients RationalCompiler.data S).length

def rationals (S : List (Poly n 1)) : Fin (count S) → ℚ :=
  fun i => (SparseCoefficientInput.coefficients RationalCompiler.data S).get i 0

def negativeIndex (S : List (Poly n 1)) : Fin (count S) :=
  SparseCoefficientInput.negIndex RationalCompiler.data S

theorem rational_negative (S : List (Poly n 1)) : rationals S (negativeIndex S) = -1 := by
  rfl

def target (original : Fin m → RootCode) (S : List (Poly n 1)) :
    Fin (m+count S) → RootCode :=
  OriginalCoefficientBindings.target original (rationals S)

def shifted (m : ℕ) (S : List (Poly n 1))
    (e : EncodedSystem.Equation (count S) n) : EncodedSystem.Equation (m+count S) n :=
  e.map (fun t => (Fin.natAdd m t.1,t.2))

def equations (m : ℕ) (S : List (Poly n 1)) : EncodedSystem.System (m+count S) n :=
  (SparseCoefficientInput.system RationalCompiler.data S).map (shifted m S)

def system (S : List (Poly n 1)) (address : Fin m → Fin n) :
    EncodedSystem.System (m+count S) n :=
  OriginalCoefficientBindings.rows (negativeIndex S) address ++ equations m S

@[simp] theorem system_length (S : List (Poly n 1)) (address : Fin m → Fin n) :
    (system S address).length = m+S.length := by
  simp [system,OriginalCoefficientBindings.rows,equations]

noncomputable section

def values (original : Fin m → ℂ) (S : List (Poly n 1)) : Fin (m+count S) → ℂ :=
  OriginalCoefficientBindings.values original (rationals S)

theorem target_represents (original : Fin m → RootCode) (w : Fin m → ℂ)
    (hw : ∀ i, (original i).Represents (w i)) (S : List (Poly n 1)) :
    ∀ i, (target original S i).Represents (values w S i) :=
  OriginalCoefficientBindings.target_represents original w hw (rationals S)

theorem shifted_polynomial (w : Fin m → ℂ) (S : List (Poly n 1))
    (e : EncodedSystem.Equation (count S) n) :
    EncodedSystem.polynomial (values w S) (shifted m S e) =
      EncodedSystem.polynomial (fun i => (rationals S i : ℂ)) e := by
  induction e with
  | nil => simp [shifted,EncodedSystem.polynomial]
  | cons t e ih =>
    change MvPolynomial.C (values w S (Fin.natAdd m t.1)) *
      (∏ i, MvPolynomial.X i ^ t.2 i) +
      EncodedSystem.polynomial (values w S) (shifted m S e) = _
    rw [ih]
    simp only [EncodedSystem.polynomial,values,OriginalCoefficientBindings.values,
      Fin.addCases_right]

theorem rational_values (S : List (Poly n 1)) :
    SparseCoefficientInput.values RationalCompiler.field (algebraMap ℚ ℂ) S =
      fun i => (rationals S i : ℂ) := by
  funext i
  change (algebraMap ℚ ℂ) (RationalCompiler.field.decode
    ((SparseCoefficientInput.coefficients RationalCompiler.data S).get i)) = _
  rw [RationalCompiler.decode_eq]
  rfl

theorem equations_zero_iff (w : Fin m → ℂ) (S : List (Poly n 1)) (z : Fin n → ℂ) :
    (∀ e ∈ equations m S, aeval z (EncodedSystem.polynomial (values w S) e)=0) ↔
      ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  simp only [equations,List.forall_mem_map,shifted_polynomial]
  rw [←rational_values]
  exact SparseCoefficientInput.system_zero_iff RationalCompiler.field (algebraMap ℚ ℂ) S z

theorem system_zero_iff (w : Fin m → ℂ) (S : List (Poly n 1))
    (address : Fin m → Fin n) (z : Fin n → ℂ) :
    (∀ e ∈ system S address, aeval z (EncodedSystem.polynomial (values w S) e)=0) ↔
      (∀ i, z (address i)=w i) ∧
      ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0 := by
  change (∀ e ∈ OriginalCoefficientBindings.rows (negativeIndex S) address ++ equations m S,
    aeval z (EncodedSystem.polynomial (OriginalCoefficientBindings.values w (rationals S)) e)=0) ↔ _
  rw [OriginalCoefficientBindings.append_zero_iff w (rationals S) (negativeIndex S)
    (rational_negative S) address]
  exact and_congr_right (fun _ => equations_zero_iff w S z)

end
end Holant.LocalDrafts.MainChain.TransformRecognition.RationalInputSystem
