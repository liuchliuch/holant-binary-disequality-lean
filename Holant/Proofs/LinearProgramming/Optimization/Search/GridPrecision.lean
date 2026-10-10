import Holant.Proofs.LinearProgramming.Optimization.Search.RoundingDeterminant
import Holant.Proofs.LinearProgramming.Optimization.Search.BudgetProgram

/-!
An ORIGINAL-input-derived binary grid which simultaneously pays for center
error, matrix invertibility and determinant error. Its unary exponents and
iteration count are polynomial outputs of actual physical programs. No loop
runs the numerical grid or n! times. RoundedTrajectory discharges these
bounds along the whole rounded trajectory; they are not a solver premise.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.GridPrecision
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

def iterations (d : Raw) : ℕ := 2*BudgetTermination.iterations d
def exponent (d : Raw) : ℕ := (d.dimension+6)*(iterations d+1)
def inverseBudget (d : Raw) : ℕ := 16*(d.dimension+1)*2^exponent d
def factorialBudget (n : ℕ) : ℕ := 2^(n*n+2*n+1)
def coefficient (n : ℕ) : ℕ := 256*(n+1)^4*(n^3+1)*factorialBudget n
def grid (d : Raw) : ℕ := coefficient d.dimension*inverseBudget d

theorem inverseBudget_pos (d : Raw) : 0 < inverseBudget d := by unfold inverseBudget; positivity
theorem factorialBudget_pos (n : ℕ) : 0<factorialBudget n := by unfold factorialBudget; positivity
theorem coefficient_pos (n : ℕ) : 0<coefficient n := by
  have := factorialBudget_pos n
  unfold coefficient
  positivity
theorem grid_pos (d : Raw) : 0<grid d := Nat.mul_pos (coefficient_pos _) (inverseBudget_pos d)

theorem determinant_coefficient (n : ℕ) : RoundingDeterminant.coefficient n≤factorialBudget n := by
  have h := RoundingDeterminant.coefficient_power n
  exact h.trans (by unfold factorialBudget; rw [pow_succ]; nlinarith)

theorem coefficients (n : ℕ) :
    2*n^2≤coefficient n ∧
    128*n^3*(n+1)*(n^3+1)≤coefficient n ∧
    16*(n^3+1)*RoundingDeterminant.coefficient n*n≤coefficient n := by
  let S := (n+1)^4
  let P := n^3+1
  let F := factorialBudget n
  have hF : 1≤F := factorialBudget_pos n
  have hP : 1≤P := by dsimp [P]; omega
  have hS : 1≤S := Left.one_le_pow_of_le (by omega : 1≤n+1) 4
  have h1S : n+1≤S := by
    simpa only [S,pow_one] using
      Nat.pow_le_pow_right (by omega : 1≤n+1) (by decide : 1≤4)
  have hnS : n≤S := (Nat.le_succ n).trans h1S
  have hn2S : n^2≤S :=
    (Nat.pow_le_pow_left (Nat.le_succ n) 2).trans
      (Nat.pow_le_pow_right (by omega : 1≤n+1) (by decide : 2≤4))
  have hn3S : n^3*(n+1)≤S := by
    have h := Nat.mul_le_mul_right (n+1) (Nat.pow_le_pow_left (Nat.le_succ n) 3)
    simpa only [S,pow_succ] using h
  have hPF : 1≤P*F := by nlinarith
  have hc : coefficient n=256*S*P*F := rfl
  rw [hc]
  refine ⟨?_,?_,?_⟩
  · calc
      2*n^2 ≤ 2*S := Nat.mul_le_mul_left 2 hn2S
      _ ≤ 256*S*(P*F) := by nlinarith
      _ = _ := by ring
  · calc
      128*n^3*(n+1)*P ≤ 128*S*P := by nlinarith [Nat.mul_le_mul_right (128*P) hn3S]
      _ ≤ 256*S*P*F := by nlinarith
  · have hK := determinant_coefficient n
    have hKN := Nat.mul_le_mul hK hnS
    calc
      16*P*RoundingDeterminant.coefficient n*n ≤ 16*P*(F*S) := by
        nlinarith [Nat.mul_le_mul_left (16*P) hKN]
      _ ≤ 256*S*P*F := by nlinarith

/-- These are all three numerical premises of the local storage proofs,
derived from the original input grid and an ordinary current inverse bound.
The current inverse bound is discharged by a trajectory induction, not a
new input field or a conclusion-shaped hypothesis of an FP theorem. -/
theorem adequate (d : Raw) (hn : 2≤d.dimension) (M : ℚ) (hM : 0≤M)
    (hMU : M≤(inverseBudget d:ℚ)) :
    (d.dimension:ℚ)^2*M/(grid d:ℚ)≤1/2 ∧
    2*(d.dimension:ℚ)^2*((d.dimension:ℚ)+1)*M/(grid d:ℚ)≤RoundingDeterminant.eta d.dimension ∧
    (d.dimension:ℚ)*M/(grid d:ℚ)≤1 ∧
    (RoundingDeterminant.coefficient d.dimension:ℚ)*((d.dimension:ℚ)*M/(grid d:ℚ))≤
      RoundingDeterminant.loss d.dimension/8 := by
  let n := d.dimension
  have hN : (2:ℚ)≤n := by exact_mod_cast hn
  have hh : (0:ℚ)<grid d := by exact_mod_cast grid_pos d
  have hU : (0:ℚ) ≤ (inverseBudget d:ℚ) := Nat.cast_nonneg _
  have hC : (0:ℚ)≤(coefficient n:ℚ) := Nat.cast_nonneg _
  obtain ⟨hs,hc,hd⟩ := coefficients n
  have hs' : (2*(n:ℚ)^2)*M≤(grid d:ℚ) := by
    have hsc : (2*(n:ℚ)^2)≤(coefficient n:ℚ) := by exact_mod_cast hs
    have h := mul_le_mul hsc hMU hM hC
    simpa only [grid,Nat.cast_mul] using h
  have hc' : (128*(n:ℚ)^3*((n:ℚ)+1)*((n:ℚ)^3+1))*M≤(grid d:ℚ) := by
    have hcc : 128*(n:ℚ)^3*((n:ℚ)+1)*((n:ℚ)^3+1)≤(coefficient n:ℚ) := by exact_mod_cast hc
    have h := mul_le_mul hcc hMU hM hC
    simpa only [grid,Nat.cast_mul] using h
  have hd' : (16*((n:ℚ)^3+1)*(RoundingDeterminant.coefficient n:ℚ)*(n:ℚ))*M≤(grid d:ℚ) := by
    have hdc : 16*((n:ℚ)^3+1)*(RoundingDeterminant.coefficient n:ℚ)*(n:ℚ)≤(coefficient n:ℚ) := by exact_mod_cast hd
    have h := mul_le_mul hdc hMU hM hC
    simpa only [grid,Nat.cast_mul] using h
  refine ⟨?_,?_,?_,?_⟩
  · exact (div_le_iff₀ hh).mpr (by linarith)
  · unfold RoundingDeterminant.eta
    apply (div_le_div_iff₀ hh (by positivity : (0:ℚ)<64*(n:ℚ)*((n:ℚ)^3+1))).mpr
    nlinarith [hc']
  · apply (div_le_one hh).mpr
    have hmult : (n:ℚ)*M≤2*(n:ℚ)^2*M := by
      nlinarith [mul_nonneg hM (by nlinarith : (0:ℚ)≤2*(n:ℚ)^2-n)]
    exact hmult.trans hs'
  · have hid : RoundingDeterminant.loss n/8=1/(16*((n:ℚ)^3+1)) := by
      unfold RoundingDeterminant.loss
      rw [div_div]
      congr 1 <;> ring
    rw [hid]
    have hid' : (RoundingDeterminant.coefficient n:ℚ)*((n:ℚ)*M/(grid d:ℚ))=
        ((RoundingDeterminant.coefficient n:ℚ)*(n:ℚ)*M)/(grid d:ℚ) := by ring
    rw [hid']
    apply (div_le_div_iff₀ hh (by positivity : (0:ℚ)<16*((n:ℚ)^3+1))).mpr
    nlinarith [hd']

def countComputes : Computes inputEncoding UnaryBinary.unaryEncoding (fun d : Input => iterations d.val) :=
  congrComputes ((pairComputes BudgetProgram.computes BudgetProgram.computes).andThen AccessPrograms.unaryAdd)
    (fun _ => by dsimp only [Function.comp_def]; simp only [iterations]; omega)

def exponentComputes : Computes inputEncoding UnaryBinary.unaryEncoding (fun d : Input => exponent d.val) := by
  let n := (pairComputes BudgetProgram.dimension (constantComputes inputEncoding UnaryBinary.unaryEncoding 6)).andThen
    AccessPrograms.unaryAdd
  let k := (pairComputes countComputes (constantComputes inputEncoding UnaryBinary.unaryEncoding 1)).andThen
    AccessPrograms.unaryAdd
  exact (pairComputes n k).andThen BudgetProgram.multiply

def powerComputes : Computes inputEncoding encodingNatBool (fun d : Input => 2^exponent d.val) :=
  exponentComputes.andThen DenominatorProgram.power

def factorialBudgetComputes : Computes inputEncoding encodingNatBool
    (fun d : Input => factorialBudget d.val.dimension) := by
  let n := BudgetProgram.dimension
  let square := (pairComputes n n).andThen BudgetProgram.multiply
  let twice := (pairComputes n n).andThen AccessPrograms.unaryAdd
  let sum := (pairComputes square twice).andThen AccessPrograms.unaryAdd
  let exponent := (pairComputes sum (constantComputes inputEncoding UnaryBinary.unaryEncoding 1)).andThen AccessPrograms.unaryAdd
  exact congrComputes (exponent.andThen DenominatorProgram.power) (fun _ => by
    dsimp only [Function.comp_def]
    unfold factorialBudget
    congr 1 <;> ring)

def inverseBudgetComputes : Computes inputEncoding encodingNatBool (fun d : Input => inverseBudget d.val) := by
  let n := PrecisionProgram.dimensionComputes.andThen PrecisionProgram.successor
  let c := constantComputes inputEncoding encodingNatBool 16
  let factor := (pairComputes c n).andThen RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes ((pairComputes factor powerComputes).andThen RationalArithmetic.naturalMultiplicationComputes)
    (fun _ => by dsimp only [Function.comp_def]; unfold inverseBudget; ring)

def gridComputes : Computes inputEncoding encodingNatBool (fun d : Input => grid d.val) := by
  let n := PrecisionProgram.dimensionComputes
  let plusOne := n.andThen PrecisionProgram.successor
  let square := (pairComputes plusOne plusOne).andThen RationalArithmetic.naturalMultiplicationComputes
  let fourth := (pairComputes square square).andThen RationalArithmetic.naturalMultiplicationComputes
  let nn := (pairComputes n n).andThen RationalArithmetic.naturalMultiplicationComputes
  let cube := (pairComputes nn n).andThen RationalArithmetic.naturalMultiplicationComputes
  let p := cube.andThen PrecisionProgram.successor
  let c := (pairComputes (constantComputes inputEncoding encodingNatBool 256) fourth).andThen
    RationalArithmetic.naturalMultiplicationComputes
  let cp := (pairComputes c p).andThen RationalArithmetic.naturalMultiplicationComputes
  let cpf := (pairComputes cp factorialBudgetComputes).andThen RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes ((pairComputes cpf inverseBudgetComputes).andThen RationalArithmetic.naturalMultiplicationComputes)
    (fun _ => by dsimp only [Function.comp_def]; unfold grid coefficient; ring)

def etaComputes : Computes inputEncoding rationalEncoding (fun d : Input => RoundingDeterminant.eta d.val.dimension) := by
  let n := PrecisionProgram.dimensionComputes
  let nn := (pairComputes n n).andThen RationalArithmetic.naturalMultiplicationComputes
  let cube := (pairComputes nn n).andThen RationalArithmetic.naturalMultiplicationComputes
  let p := cube.andThen PrecisionProgram.successor
  let scale := (pairComputes (constantComputes inputEncoding encodingNatBool 64) n).andThen
    RationalArithmetic.naturalMultiplicationComputes
  let den := (pairComputes scale p).andThen RationalArithmetic.naturalMultiplicationComputes
  let rational := (den.andThen RationalArithmetic.natCastComputes).andThen PivotProgram.integerCast
  exact congrComputes (rational.andThen Foundation.Infrastructure.RationalInverse.inverseComputes)
    (fun _ => by
      dsimp only [Function.comp_def]
      unfold RoundingDeterminant.eta
      rw [one_div]
      congr 1
      push_cast
      ring)

theorem binary_grid_length (d : Input) : (encodingNatBool.encode (grid d.val)).length≤
    gridComputes.outputBound.bound.eval (inputEncoding.encode d).length := gridComputes.outputBound.length_le d

theorem physical_cost (d : Input) :
    primitiveCost gridComputes.machine (gridComputes.outputs d).steps
      (some (Turing.initList gridComputes.machine.computer (inputEncoding.encode d)))≤
      (primitivePolynomial gridComputes).eval (inputEncoding.encode d).length := computes_primitive_cost gridComputes d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.GridPrecision
