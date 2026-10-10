import Holant.Proofs.LinearProgramming.Complexity.ListLemmas
import Holant.Proofs.LinearProgramming.Complexity.StorageProgram
import Holant.Proofs.LinearProgramming.Support.SumProgram

/-!
Physical rational matrix-vector actions, transpose pullback and squared norm.
The original unary dimension controls real nested table scans and default
lookups. Exact sum timing uses the independent Support.SumProgram, including
its same-machine polynomial retiming.
This performs the n² arithmetic needed by the actual factor update, not a
unit-cost mulVec primitive or a supplied dot-product oracle.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.MatrixAction
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open FactorUpdate Codec
open scoped BigOperators Matrix
noncomputable section

abbrev Query := ℕ × (List (List ℚ) × List ℚ)
def tailEncoding := pairEncoding StorageProgram.matrixEncoding pointEncoding
def encoding := pairEncoding UnaryBinary.unaryEncoding tailEncoding
def indexEncoding := pairEncoding encoding UnaryBinary.unaryEncoding
def cellEncoding := pairEncoding indexEncoding UnaryBinary.unaryEncoding
def term (transpose : Bool) (q : Query) (i j : ℕ) : ℚ :=
  (if transpose then (q.2.1.getD j []).getD i 0 else (q.2.1.getD i []).getD j 0)*q.2.2.getD j 0
def terms (transpose : Bool) (q : Query) (i : ℕ) : List ℚ := (List.range q.1).map (term transpose q i)
def value (transpose : Bool) (q : Query) : List ℚ := (List.range q.1).map (fun i => (terms transpose q i).sum)

def dimension : Computes encoding UnaryBinary.unaryEncoding (fun q : Query => q.1) := Wiring.firstComputes _ _
def tail := Wiring.secondComputes UnaryBinary.unaryEncoding tailEncoding
def matrix : Computes encoding StorageProgram.matrixEncoding (fun q : Query => q.2.1) := tail.andThen (Wiring.firstComputes _ _)
def vector : Computes encoding pointEncoding (fun q : Query => q.2.2) := tail.andThen (Wiring.secondComputes _ _)

def termComputes (transpose : Bool) : Computes cellEncoding rationalEncoding
    (fun q : (Query × ℕ) × ℕ => term transpose q.1.1 q.1.2 q.2) := by
  let p := Wiring.firstComputes indexEncoding UnaryBinary.unaryEncoding
  let ctx := p.andThen (Wiring.firstComputes encoding UnaryBinary.unaryEncoding)
  let i := p.andThen (Wiring.secondComputes encoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes indexEncoding UnaryBinary.unaryEncoding
  let x := AccessPrograms.get rationalEncoding 0 (ctx.andThen vector) j
  cases transpose
  · let row := AccessPrograms.get pointEncoding [] (ctx.andThen matrix) i
    let a := AccessPrograms.get rationalEncoding 0 row j
    exact congrComputes ((pairComputes a x).andThen RationalArithmetic.multiplicationComputes)
      (fun q => rfl)
  · let row := AccessPrograms.get pointEncoding [] (ctx.andThen matrix) j
    let a := AccessPrograms.get rationalEncoding 0 row i
    exact congrComputes ((pairComputes a x).andThen RationalArithmetic.multiplicationComputes)
      (fun q => rfl)

def termsComputes (transpose : Bool) : Computes indexEncoding pointEncoding
    (fun q : Query × ℕ => terms transpose q.1 q.2) :=
  WireLists.tabulate indexEncoding rationalEncoding (fun q => q.1.1)
    ((Wiring.firstComputes encoding UnaryBinary.unaryEncoding).andThen dimension)
    (fun q j => term transpose q.1 q.2 j) (termComputes transpose)

def computes (transpose : Bool) : Computes encoding pointEncoding (value transpose) :=
  WireLists.tabulate encoding rationalEncoding (fun q => q.1) dimension
    (fun q i => (terms transpose q i).sum)
    ((termsComputes transpose).andThen
      Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.timing.computes)

theorem correct (transpose : Bool) (n : ℕ) (A : Mat n) (x : Vec n) :
    value transpose (n,List.ofFn (fun i => List.ofFn (A i)),List.ofFn x)=
      List.ofFn ((if transpose then A.transpose else A).mulVec x) := by
  rw [value,DensePrograms.range_map]
  congr 1
  funext i
  rw [terms,DensePrograms.range_map,List.sum_ofFn]
  cases transpose <;>
    simp [term,DensePrograms.getD_ofFn,Matrix.mulVec,dotProduct,Matrix.transpose_apply]

def squareComputes : Computes pointEncoding rationalEncoding (fun xs : List ℚ => (xs.map (fun x => x*x)).sum) :=
  (WireLists.mapComputes rationalEncoding rationalEncoding (fun x => x*x)
    ((Wiring.diagonalComputes rationalEncoding).andThen RationalArithmetic.multiplicationComputes)).andThen
      Holant.LocalDrafts.RemoteWork.RationalLP.Support.SumProgram.timing.computes

theorem square_correct {n : ℕ} (v : Vec n) : ((List.ofFn v).map (fun x => x*x)).sum=square v := by
  rw [List.map_ofFn,List.sum_ofFn]
  simp only [square,pow_two,Function.comp_apply]

theorem physical_cost (transpose : Bool) (q : Query) :
    primitiveCost (computes transpose).machine ((computes transpose).outputs q).steps
      (some (Turing.initList (computes transpose).machine.computer (encoding.encode q)))≤
      (primitivePolynomial (computes transpose)).eval (encoding.encode q).length :=
  computes_primitive_cost (computes transpose) q

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.MatrixAction
