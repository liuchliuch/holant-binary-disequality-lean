import Holant.Proofs.LinearProgramming.Complexity.ListLemmas
import Holant.Proofs.LinearProgramming.Optimization.Search.MatrixAction
import Holant.Proofs.LinearProgramming.Optimization.Search.NormProgram

/-!
Actual physical factor update on framed center/matrix/normal words. The
dimension and scales are read from ORIGINAL Codec.Input. Transpose pullback,
norm, matrix-vector action, center writes and n² rank-one writes call actual
Boolean-stack programs. No arithmetic unit-cost or update-correctness oracle.
The final theorem identifies this SAME program with FactorUpdate.update on
an active nonsingular state. The separator and whole fuel loop are separate
connections; the normal word is plain data, not a claimed valid-cut premise.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

open Holant.LocalDrafts.RemoteWork.RationalLP.Complexity


namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.UpdateProgram
open Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open FactorUpdate Codec
open scoped BigOperators Matrix
noncomputable section

abbrev Query := Input × (StorageProgram.Code × List ℚ)
def tailEncoding := pairEncoding StorageProgram.encoding pointEncoding
def encoding := pairEncoding inputEncoding tailEncoding
def source : Computes encoding inputEncoding (fun q : Query => q.1) := Wiring.firstComputes _ _
def tail := Wiring.secondComputes inputEncoding tailEncoding
def state : Computes encoding StorageProgram.encoding (fun q : Query => q.2.1) := tail.andThen (Wiring.firstComputes _ _)
def normal : Computes encoding pointEncoding (fun q : Query => q.2.2) := tail.andThen (Wiring.secondComputes _ _)
def matrix := state.andThen (Wiring.secondComputes pointEncoding StorageProgram.matrixEncoding)
def center := state.andThen (Wiring.firstComputes pointEncoding StorageProgram.matrixEncoding)
def dimension := source.andThen BudgetProgram.dimension

def pullValue (q : Query) : List ℚ := MatrixAction.value true (q.1.val.dimension,q.2.1.2,q.2.2)
def pushValue (q : Query) : List ℚ := MatrixAction.value false (q.1.val.dimension,q.2.1.2,pullValue q)
def pullComputes : Computes encoding pointEncoding pullValue :=
  (pairComputes dimension (pairComputes matrix normal)).andThen (MatrixAction.computes true)
def pushComputes : Computes encoding pointEncoding pushValue :=
  (pairComputes dimension (pairComputes matrix pullComputes)).andThen (MatrixAction.computes false)

abbrev Work := Query × (List ℚ × List ℚ)
def vectorsEncoding := pairEncoding pointEncoding pointEncoding
def workEncoding := pairEncoding encoding vectorsEncoding
def work (q : Query) : Work := (q,pullValue q,pushValue q)
def workComputes : Computes encoding workEncoding work :=
  pairComputes (identityComputes encoding) (pairComputes pullComputes pushComputes)
def query : Computes workEncoding encoding (fun q : Work => q.1) := Wiring.firstComputes _ _
def workSource := query.andThen source
def vectors := Wiring.secondComputes encoding vectorsEncoding
def pulledWord := vectors.andThen (Wiring.firstComputes pointEncoding pointEncoding)
def pushedWord := vectors.andThen (Wiring.secondComputes pointEncoding pointEncoding)
def workDimension := query.andThen dimension

def rationalDimension : Computes inputEncoding rationalEncoding (fun d : Input => (d.val.dimension:ℚ)) :=
  PrecisionProgram.dimensionComputes.andThen (RationalArithmetic.natCastComputes.andThen PivotProgram.integerCast)

def axialComputes : Computes inputEncoding rationalEncoding (fun d : Input => Scales.axial d.val.dimension) := by
  let one := constantComputes inputEncoding rationalEncoding 1
  let den := (pairComputes rationalDimension one).andThen RationalArithmetic.additionComputes
  exact congrComputes ((pairComputes rationalDimension (den.andThen Foundation.Infrastructure.RationalInverse.inverseComputes)).andThen
    RationalArithmetic.multiplicationComputes) (fun _ => by simp [Scales.axial,div_eq_mul_inv])
def transverseComputes : Computes inputEncoding rationalEncoding (fun d : Input => Scales.transverse d.val.dimension) := by
  let nn := (pairComputes rationalDimension rationalDimension).andThen RationalArithmetic.multiplicationComputes
  exact congrComputes ((pairComputes (constantComputes inputEncoding rationalEncoding 1)
    (nn.andThen Foundation.Infrastructure.RationalInverse.inverseComputes)).andThen RationalArithmetic.additionComputes)
      (fun _ => by simp [Scales.transverse,pow_two,one_div])
def inflationComputes : Computes inputEncoding rationalEncoding (fun d : Input => Scales.inflation d.val.dimension) := by
  let nn := (pairComputes rationalDimension rationalDimension).andThen RationalArithmetic.multiplicationComputes
  let fourth := (pairComputes nn nn).andThen RationalArithmetic.multiplicationComputes
  let den := (pairComputes (constantComputes inputEncoding rationalEncoding 16) fourth).andThen RationalArithmetic.multiplicationComputes
  exact congrComputes ((pairComputes (constantComputes inputEncoding rationalEncoding 1)
    (den.andThen Foundation.Infrastructure.RationalInverse.inverseComputes)).andThen RationalArithmetic.additionComputes)
      (fun _ => by simp [Scales.inflation,one_div]; ring)

def squareValue (q : Work) : ℚ := (q.2.1.map (fun x => x*x)).sum
def squareComputes : Computes workEncoding rationalEncoding squareValue := pulledWord.andThen MatrixAction.squareComputes
def shiftValue (q : Work) : ℚ :=
  1/(((q.1.1.val.dimension:ℚ)+1)*NormApprox.value (squareValue q) (Scales.precision q.1.1.val.dimension))
def rankValue (q : Work) : ℚ :=
  (Scales.axial q.1.1.val.dimension-Scales.transverse q.1.1.val.dimension)/squareValue q

def shiftComputes : Computes workEncoding rationalEncoding shiftValue := by
  let n := workSource.andThen rationalDimension
  let plusOne := (pairComputes n (constantComputes workEncoding rationalEncoding 1)).andThen RationalArithmetic.additionComputes
  let a := (pairComputes workSource squareComputes).andThen NormProgram.fromInput
  exact congrComputes (((pairComputes plusOne a).andThen RationalArithmetic.multiplicationComputes).andThen
    Foundation.Infrastructure.RationalInverse.inverseComputes) (fun _ => by simp [shiftValue,one_div])
def rankComputes : Computes workEncoding rationalEncoding rankValue := by
  let diff := (pairComputes (workSource.andThen axialComputes) (workSource.andThen transverseComputes)).andThen
    Comparison.rationalDifference
  exact congrComputes ((pairComputes diff (squareComputes.andThen Foundation.Infrastructure.RationalInverse.inverseComputes)).andThen
    RationalArithmetic.multiplicationComputes) (fun _ => by simp [rankValue,div_eq_mul_inv])

def centerValue (q : Work) (i : ℕ) : ℚ := q.1.2.1.1.getD i 0-shiftValue q*q.2.2.getD i 0
def factorValue (q : Work) (i j : ℕ) : ℚ :=
  Scales.inflation q.1.1.val.dimension*(Scales.transverse q.1.1.val.dimension*
    ((q.1.2.1.2.getD i []).getD j 0)+rankValue q*q.2.2.getD i 0*q.2.1.getD j 0)
def emit (q : Work) : StorageProgram.Code :=
  ((List.range q.1.1.val.dimension).map (centerValue q),
    (List.range q.1.1.val.dimension).map (fun i => (List.range q.1.1.val.dimension).map (factorValue q i)))
def value (q : Query) : StorageProgram.Code := emit (work q)

def centerCell : Computes (pairEncoding workEncoding UnaryBinary.unaryEncoding) rationalEncoding
    (fun p : Work × ℕ => centerValue p.1 p.2) := by
  let ctx := Wiring.firstComputes workEncoding UnaryBinary.unaryEncoding
  let i := Wiring.secondComputes workEncoding UnaryBinary.unaryEncoding
  let old := AccessPrograms.get rationalEncoding 0 ((ctx.andThen query).andThen center) i
  let w := AccessPrograms.get rationalEncoding 0 (ctx.andThen pushedWord) i
  let change := (pairComputes (ctx.andThen shiftComputes) w).andThen RationalArithmetic.multiplicationComputes
  exact (pairComputes old change).andThen Comparison.rationalDifference

def rowEncoding := pairEncoding workEncoding UnaryBinary.unaryEncoding
def cellEncoding := pairEncoding rowEncoding UnaryBinary.unaryEncoding
def factorCell : Computes cellEncoding rationalEncoding
    (fun p : (Work × ℕ) × ℕ => factorValue p.1.1 p.1.2 p.2) := by
  let p := Wiring.firstComputes rowEncoding UnaryBinary.unaryEncoding
  let ctx := p.andThen (Wiring.firstComputes workEncoding UnaryBinary.unaryEncoding)
  let i := p.andThen (Wiring.secondComputes workEncoding UnaryBinary.unaryEncoding)
  let j := Wiring.secondComputes rowEncoding UnaryBinary.unaryEncoding
  let row := AccessPrograms.get pointEncoding [] (((ctx.andThen query).andThen state).andThen
    (Wiring.secondComputes pointEncoding StorageProgram.matrixEncoding)) i
  let old := AccessPrograms.get rationalEncoding 0 row j
  let w := AccessPrograms.get rationalEncoding 0 (ctx.andThen pushedWord) i
  let v := AccessPrograms.get rationalEncoding 0 (ctx.andThen pulledWord) j
  let t := (pairComputes ((ctx.andThen workSource).andThen transverseComputes) old).andThen RationalArithmetic.multiplicationComputes
  let rank := (pairComputes (ctx.andThen rankComputes) w).andThen RationalArithmetic.multiplicationComputes
  let correction := (pairComputes rank v).andThen RationalArithmetic.multiplicationComputes
  let sum := (pairComputes t correction).andThen RationalArithmetic.additionComputes
  exact (pairComputes ((ctx.andThen workSource).andThen inflationComputes) sum).andThen
    RationalArithmetic.multiplicationComputes

def emitComputes : Computes workEncoding StorageProgram.encoding emit := by
  let c := WireLists.tabulate workEncoding rationalEncoding (fun q : Work => q.1.1.val.dimension)
    workDimension centerValue centerCell
  let row := WireLists.tabulate rowEncoding rationalEncoding (fun q : Work × ℕ => q.1.1.1.val.dimension)
    ((Wiring.firstComputes workEncoding UnaryBinary.unaryEncoding).andThen workDimension)
    (fun q j => factorValue q.1 q.2 j) factorCell
  let matrix := WireLists.tabulate workEncoding pointEncoding (fun q : Work => q.1.1.val.dimension)
    workDimension (fun q i => (List.range q.1.1.val.dimension).map (factorValue q i)) row
  exact pairComputes c matrix
def computes : Computes encoding StorageProgram.encoding value := workComputes.andThen emitComputes

theorem work_exact (d : Input) (s : FactorUpdate.State d.val.dimension) (g : Vec d.val.dimension) :
    work (d,StorageProgram.code s,List.ofFn g)=
      ((d,StorageProgram.code s,List.ofFn g),List.ofFn (pulled s g),List.ofFn (s.factor.mulVec (pulled s g))) := by
  have hp := MatrixAction.correct true d.val.dimension s.factor g
  have hw := MatrixAction.correct false d.val.dimension s.factor (pulled s g)
  simp only [Bool.true_eq_false,↓reduceIte] at hp
  simp only [Bool.false_eq_true,↓reduceIte,pulled] at hw
  simp only [work,pullValue,pushValue,StorageProgram.code,pulled,hp,hw]

theorem factor_entry {n : ℕ} (hn : 2≤n) (s : FactorUpdate.State n) (g : Vec n) (hv : pulled s g≠0) (i j : Fin n) :
    (update s g).factor i j=Scales.inflation n*(Scales.transverse n*s.factor i j+
      ((Scales.axial n-Scales.transverse n)/square (pulled s g))*(s.factor.mulVec (pulled s g)) i*(pulled s g) j) := by
  let v := pulled s g
  have hs := ne_of_gt (square_pos v hv)
  have hI : (∑ k, s.factor i k*(if k=j then 1 else 0 : ℚ))=s.factor i j := by simp [mul_ite]
  change (s.factor*transform v) i j=_
  rw [Matrix.mul_apply]
  simp_rw [RegisterGrowth.transform_entry hn v hv]
  calc
    _ = Scales.inflation n*(Scales.transverse n*(∑ k, s.factor i k*(if k=j then 1 else 0 : ℚ))+
        ((Scales.axial n-Scales.transverse n)/square v)*(∑ k, s.factor i k*v k)*v j) := by
      simp only [Finset.mul_sum,Finset.sum_mul,← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    _ = _ := by rw [hI]; rfl

theorem correct (d : Input) (hn : 2≤d.val.dimension) (s : FactorUpdate.State d.val.dimension) (g : Vec d.val.dimension)
    (hR : s.factor.det≠0) (hg : g≠0) :
    value (d,StorageProgram.code s,List.ofFn g)=StorageProgram.code (update s g) := by
  have hv := Containment.pulled_nonzero s g hR hg
  rw [value,work_exact]
  simp only [emit,DensePrograms.range_map,StorageProgram.code]
  congr 1
  · congr 1
    funext i
    simp only [centerValue,shiftValue,squareValue,DensePrograms.getD_ofFn,StorageProgram.code,
      MatrixAction.square_correct,update,Projection.shift,Matrix.mulVec_smul,
      Pi.sub_apply,Pi.smul_apply,smul_eq_mul]
  · congr 1
    funext i
    congr 1
    funext j
    simp only [factorValue,rankValue,squareValue,StorageProgram.code,DensePrograms.getD_ofFn,
      MatrixAction.square_correct,factor_entry hn s g hv i j]

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (Turing.initList computes.machine.computer (encoding.encode q)))≤
      (primitivePolynomial computes).eval (encoding.encode q).length := computes_primitive_cost computes q

theorem intermediate_bits (q : Query) (k : ℕ) (hk : k≤(computes.outputs q).steps) (c : computes.machine.Config)
    (hc : (fun p => p.bind computes.machine.computer.step)^[k]
      (some (Turing.initList computes.machine.computer (encoding.encode q)))=some c) :
    stackSize c.stk≤computes.outputBound.bound.eval (encoding.encode q).length := by
  have h := computes.machine.run_size_le _ c k hc
  rw [Machine.size_init] at h
  exact h.trans (by
    have ht := hk.trans (computes.outputs q).steps_le_m
    simpa only [Computes.outputBound, Polynomial.eval_add, Polynomial.eval_X,
      Polynomial.eval_mul, Polynomial.eval_C] using
      Nat.add_le_add_left (Nat.mul_le_mul_right _ ht) (encoding.encode q).length)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.UpdateProgram
