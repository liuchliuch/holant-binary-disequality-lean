import Holant.Proofs.LinearProgramming.Optimization.PrecisionProgram

/-!
A polynomially encoded radius exponent derived from the ORIGINAL LP bytes.
The resulting 2^(-B) inner-box radius is valid without a full-dimensionality
assumption on the original equality polytope. This is a geometric scale bound;
the actual iteration bound is established in Search.BudgetTermination.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.RadiusBudget
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec Thickening
noncomputable section

def exponent (d : Raw) : ℕ := 2*InputBounds.size (PhaseMatrix.value d).val^2+4*InputBounds.size d+5

theorem C_bound (d : Raw) : C d≤2^(2*InputBounds.size d+1) := by
  let L := InputBounds.size d
  have hn := InputBounds.dimension_le d
  have hp : 1≤2^L := Nat.one_le_pow _ _ (by decide)
  have hs : L+1≤2^(L+1) := (Nat.lt_two_pow_self (n := L+1)).le
  calc
    C d=1+d.dimension*2^L := rfl
    _ ≤ (d.dimension+1)*2^L := by nlinarith
    _ ≤ (L+1)*2^L := Nat.mul_le_mul_right _ (by omega)
    _ ≤ 2^(L+1)*2^L := Nat.mul_le_mul_right _ hs
    _ = _ := by rw [← pow_add]; congr 1; dsimp [L]; omega

theorem denominator_bound (d : Raw) : 8*D d*C d*C d≤2^exponent d := by
  have hc := C_bound d
  have hcc := Nat.mul_le_mul hc hc
  have h := Nat.mul_le_mul_left (8*D d) hcc
  calc
    8*D d*C d*C d ≤ 8*D d*(2^(2*InputBounds.size d+1)*2^(2*InputBounds.size d+1)) := by nlinarith
    _ = 2^exponent d := by
      change 2^3*2^(2*InputBounds.size (PhaseMatrix.value d).val^2)*
        (2^(2*InputBounds.size d+1)*2^(2*InputBounds.size d+1))=_
      simp only [← pow_add]
      congr 1
      unfold exponent
      omega

theorem radius_lower (d : Raw) : 1/((2^exponent d:ℕ):ℚ)≤radius d := by
  have hd : (0:ℚ)<D d := by exact_mod_cast D_pos d
  have hc : (0:ℚ)<C d := by exact_mod_cast C_pos d
  have he : radius d=1/((8*D d*C d*C d:ℕ):ℚ) := by
    simp only [radius,epsilon,Nat.cast_mul,Nat.cast_ofNat]
    field_simp [ne_of_gt hd,ne_of_gt hc] <;> ring
  rw [he]
  have hden : (0 : ℚ)<((8*D d*C d*C d : ℕ) : ℚ) := by
    simp only [Nat.cast_mul,Nat.cast_ofNat]
    positivity
  apply one_div_le_one_div_of_le hden
  exact_mod_cast denominator_bound d

def computes : Computes inputEncoding UnaryBinary.unaryEncoding (fun d : Input => exponent d.val) := by
  let auxiliary := PhaseCompiler.computes.andThen
    (recode DenominatorProgram.exponent Subtype.val (fun _ => rfl) (fun _ => rfl))
  let length : Computes inputEncoding UnaryBinary.unaryEncoding
      (fun d : Input => InputBounds.size d.val) :=
    recode DenominatorProgram.length Subtype.val (fun _ => rfl) (fun _ => rfl)
  let twice := (pairComputes length length).andThen AccessPrograms.unaryAdd
  let four := (pairComputes twice twice).andThen AccessPrograms.unaryAdd
  let sum := (pairComputes auxiliary four).andThen AccessPrograms.unaryAdd
  exact congrComputes ((pairComputes sum (constantComputes inputEncoding UnaryBinary.unaryEncoding 5)).andThen
    AccessPrograms.unaryAdd) (fun d => by simp [Function.comp_def,exponent,PhaseCompiler.value]; ring)

theorem original_length_bound (d : Input) : exponent d.val≤
    computes.outputBound.bound.eval (inputEncoding.encode d).length := by
  simpa [UnaryBinary.unaryEncoding] using computes.outputBound.length_le d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.RadiusBudget
