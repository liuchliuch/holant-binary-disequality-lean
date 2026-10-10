import Holant.Proofs.LinearProgramming.Optimization.Search.BudgetTermination
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
The proved geometric iteration count is physically emitted from ORIGINAL
Codec.Input as a unary counter. Unary multiplication is a real range/copy
loop, polynomial in the lengths of its unary input words. No exponential
radius denominator is expanded into unary; only its polynomial exponent B
and the derived polynomial iteration count are emitted.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.BudgetProgram
open Computability Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec

theorem copy_words (n m : ℕ) :
    (List.range n).flatMap (fun _ => List.replicate m true)=List.replicate (n*m) true := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.range_succ,List.flatMap_append,ih]
    simp only [List.flatMap_cons,List.flatMap_nil,List.append_nil]
    rw [← List.replicate_add]
    congr 1
    ring

noncomputable section
def multiply : Computes (pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
    UnaryBinary.unaryEncoding (fun q : ℕ × ℕ => q.1*q.2) := by
  let ea := pairEncoding UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
  let n := Wiring.firstComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding
  let ctx := Wiring.firstComputes ea UnaryBinary.unaryEncoding
  let m := ctx.andThen (Wiring.secondComputes UnaryBinary.unaryEncoding UnaryBinary.unaryEncoding)
  let copies := WireLists.tabulate ea UnaryBinary.unaryEncoding (fun q : ℕ × ℕ => q.1)
    n (fun q _ => q.2) m
  let join := Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators.Bytecode.flatMap UnaryBinary.unaryEncoding
    (fun m => UnaryBinary.unaryEncoding.encode m) (encodeComputes UnaryBinary.unaryEncoding)
  refine recode (copies.andThen join) id (fun _ => rfl) ?_
  intro q
  simp only [List.flatMap_map,Function.comp_def,UnaryBinary.unaryEncoding,Frame.wordEncoding]
  exact copy_words q.1 q.2

def dimension : Computes inputEncoding UnaryBinary.unaryEncoding (fun d : Input => d.val.dimension) :=
  recode Parsing.dimension Subtype.val (fun _ => rfl) (fun _ => rfl)

def computes : Computes inputEncoding UnaryBinary.unaryEncoding
    (fun d : Input => BudgetTermination.iterations d.val) := by
  let one := constantComputes inputEncoding UnaryBinary.unaryEncoding 1
  let two := constantComputes inputEncoding UnaryBinary.unaryEncoding 2
  let nn := (pairComputes dimension dimension).andThen multiply
  let cube := (pairComputes nn dimension).andThen multiply
  let block := (pairComputes two ((pairComputes cube one).andThen AccessPrograms.unaryAdd)).andThen multiply
  let plusTwo := (pairComputes dimension two).andThen AccessPrograms.unaryAdd
  let outer := (pairComputes plusTwo dimension).andThen multiply
  let plusOne := (pairComputes RadiusBudget.computes one).andThen AccessPrograms.unaryAdd
  let rad := (pairComputes plusOne dimension).andThen multiply
  let inner := (pairComputes nn rad).andThen AccessPrograms.unaryAdd
  let blocks := (pairComputes ((pairComputes outer inner).andThen AccessPrograms.unaryAdd) one).andThen
    AccessPrograms.unaryAdd
  exact congrComputes ((pairComputes block blocks).andThen multiply) (fun d => by
    unfold BudgetTermination.iterations BudgetTermination.blocks BudgetTermination.outerExponent
      InverseBounds.exponent Decay.block
    dsimp only [Function.comp_def]
    ring)

theorem count_length (d : Input) : BudgetTermination.iterations d.val≤
    computes.outputBound.bound.eval (inputEncoding.encode d).length := by
  simpa only [UnaryBinary.unaryEncoding,List.length_replicate] using computes.outputBound.length_le d

theorem physical_cost (d : Input) :
    primitiveCost computes.machine (computes.outputs d).steps
      (some (Turing.initList computes.machine.computer (inputEncoding.encode d)))≤
      (primitivePolynomial computes).eval (inputEncoding.encode d).length := computes_primitive_cost computes d

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.BudgetProgram
