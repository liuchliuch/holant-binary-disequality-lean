import Holant.Proofs.Reductions.EightVertexNonexception.Coefficients
import Holant.Complexity.UniversalPairReduction.SmoothingCompiler.Combinators
import Holant.Complexity.FixedFieldMachines.PrimitiveCost


noncomputable section
namespace Holant.LocalDrafts.Hardness.EightVertexNonexception.BranchTest
open Turing Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open UniversalPairReduction.SmoothingCompiler
open FixedGadgetSubstitution.Compiler
set_option backward.isDefEq.respectTransparency false

variable {K : Type} [Field K] [Algebra ℚ K] {n : ℕ}

def entriesList (M : Signature K 4) : List K :=
  [(entries M).a,(entries M).b,(entries M).c,(entries M).d,
   (entries M).w,(entries M).z,(entries M).y,(entries M).x]

def zeroAt (i : ℕ) (xs : List K) : Bool := by
  classical
  exact decide (xs.getD i 0 = 0)

def test (xs : List K) : Bool :=
  if zeroAt 1 xs then
    if zeroAt 6 xs then
      if zeroAt 4 xs then
        if zeroAt 2 xs then false else
          if zeroAt 3 xs then false else
            if zeroAt 5 xs then false else true
      else false
    else false
  else false

theorem test_eq_true (xs : List K) : test xs = true ↔
    xs.getD 1 0 = 0 ∧ xs.getD 6 0 = 0 ∧ xs.getD 4 0 = 0 ∧
    xs.getD 2 0 ≠ 0 ∧ xs.getD 3 0 ≠ 0 ∧ xs.getD 5 0 ≠ 0 := by
  classical
  by_cases hb : xs.getD 1 0 = 0 <;> by_cases hy : xs.getD 6 0 = 0 <;>
    by_cases hw : xs.getD 4 0 = 0 <;> by_cases hc : xs.getD 2 0 = 0 <;>
    by_cases hd : xs.getD 3 0 = 0 <;> by_cases hz : xs.getD 5 0 = 0 <;>
    simp [test,zeroAt,hb,hy,hw,hc,hd,hz]

theorem test_entries (M : Signature K 4) : test (entriesList M) = true ↔ SparseCase M := by
  rw [test_eq_true]
  rfl

/-- Equality is implemented by WordCompare on the very same field codec.
The constant word is the codec's own canonical zero. -/
def zeroAtComputes (F : FixedField K n) (i : ℕ) :
    Computes (framedListEncoding F.encoding) encodingBoolBool (zeroAt i) := by
  classical
  exact (pairComputes (getDComputes F.encoding i (0 : K))
    (constantComputes (framedListEncoding F.encoding) F.encoding (0 : K))).andThen
      (equalComputes F.encoding)

def computes (F : FixedField K n) :
    Computes (framedListEncoding F.encoding) encodingBoolBool test :=
  ifComputes (zeroAtComputes F 1)
    (ifComputes (zeroAtComputes F 6)
      (ifComputes (zeroAtComputes F 4)
        (ifComputes (zeroAtComputes F 2)
          (constantComputes (framedListEncoding F.encoding) encodingBoolBool false)
          (ifComputes (zeroAtComputes F 3)
            (constantComputes (framedListEncoding F.encoding) encodingBoolBool false)
            (ifComputes (zeroAtComputes F 5)
              (constantComputes (framedListEncoding F.encoding) encodingBoolBool false)
              (constantComputes (framedListEncoding F.encoding) encodingBoolBool true))))
        (constantComputes (framedListEncoding F.encoding) encodingBoolBool false))
      (constantComputes (framedListEncoding F.encoding) encodingBoolBool false))
    (constantComputes (framedListEncoding F.encoding) encodingBoolBool false)

/-- The bound belongs to this exact finite program and original framed words. -/
theorem primitive_bound (F : FixedField K n) (xs : List K) :
    primitiveCost (computes F).machine ((computes F).outputs xs).steps
      (some (initList (computes F).machine.computer
        ((framedListEncoding F.encoding).encode xs))) ≤
      (primitivePolynomial (computes F)).eval
        ((framedListEncoding F.encoding).encode xs).length :=
  computes_primitive_cost (computes F) xs

end Holant.LocalDrafts.Hardness.EightVertexNonexception.BranchTest
