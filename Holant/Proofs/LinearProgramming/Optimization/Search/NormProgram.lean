import Holant.Proofs.LinearProgramming.Optimization.Search.NormApprox
import Holant.Proofs.LinearProgramming.Optimization.Search.Scales
import Holant.Proofs.LinearProgramming.Optimization.PrecisionProgram
import Holant.Proofs.LinearProgramming.Optimization.Infrastructure.EncodedSquareRoot
import Holant.Proofs.LinearProgramming.Support.MachineCombinators

/-!
Same rational normalizer as NormApprox.value, now as a physical polynomial
Boolean-stack program. Reuses the existing bitwise square-root program,
including its parser, remainder cleanup and canonical output. Precision is
binary 512*n^4, computed from original input dimension, never unary fuel.
-/
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.Completion

namespace Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.NormProgram
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines GraphPreprocessing
open FixedGadgetSubstitution.Compiler
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Codec
noncomputable section

abbrev rootMachine : Machine where
  K := (Infrastructure.EncodedSquareRoot.computer false).K
  decidableK := (Infrastructure.EncodedSquareRoot.computer false).kDecidableEq
  finiteK := (Infrastructure.EncodedSquareRoot.computer false).kFin
  input := (Infrastructure.EncodedSquareRoot.computer false).k₀
  output := (Infrastructure.EncodedSquareRoot.computer false).k₁
  Label := (Infrastructure.EncodedSquareRoot.computer false).Λ
  finiteLabel := (Infrastructure.EncodedSquareRoot.computer false).ΛFin
  main := (Infrastructure.EncodedSquareRoot.computer false).main
  State := (Infrastructure.EncodedSquareRoot.computer false).σ
  finiteState := (Infrastructure.EncodedSquareRoot.computer false).σFin
  initial := (Infrastructure.EncodedSquareRoot.computer false).initialState
  program := (Infrastructure.EncodedSquareRoot.computer false).m

def rootComputes : Computes encodingNatBool encodingNatBool Nat.sqrt where
  machine := rootMachine
  time := Infrastructure.EncodedSquareRoot.squareRootPolyTime.time
  outputs n := by
    have h := Infrastructure.EncodedSquareRoot.squareRootPolyTime.outputsFun n
    change TM2OutputsInTime rootMachine.computer (List.map id (encodingNatBool.encode n))
      (some (List.map id (encodingNatBool.encode (Nat.sqrt n)))) _ at h
    simpa only [List.map_id] using h

def absoluteNumerator : Computes rationalEncoding encodingNatBool (fun q : ℚ => q.num.natAbs) := by
  let z := RationalArithmetic.numeratorComputes
  let absolute := ifComputes (z.andThen Comparison.negative)
    (z.andThen Comparison.integerNegate) z
  refine congrComputes (absolute.andThen RoundingProgram.toNat) ?_
  intro q
  cases h : q.num <;> simp [h,IntegerArithmetic.negative]

abbrev Query := ℚ × ℕ
def encoding := pairEncoding rationalEncoding encodingNatBool
def scalar : Computes encoding rationalEncoding (fun q : Query => q.1) := Wiring.firstComputes _ _
def precision : Computes encoding encodingNatBool (fun q : Query => q.2) := Wiring.secondComputes _ _
def denominator : Computes encoding encodingNatBool (fun q : Query => q.1.den) :=
  scalar.andThen RationalArithmetic.denominatorComputes

def product : Computes encoding encodingNatBool (fun q : Query => q.1.num.natAbs*q.1.den*q.2^2) := by
  let pq := (pairComputes (scalar.andThen absoluteNumerator) denominator).andThen
    RationalArithmetic.naturalMultiplicationComputes
  let tt := (pairComputes precision precision).andThen RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes ((pairComputes pq tt).andThen RationalArithmetic.naturalMultiplicationComputes)
    (fun q => by simp only [Function.comp_apply,pow_two])

def computes : Computes encoding rationalEncoding (fun q : Query => NormApprox.value q.1 q.2) := by
  let k := (product.andThen rootComputes).andThen PrecisionProgram.successor
  let den := (pairComputes denominator precision).andThen RationalArithmetic.naturalMultiplicationComputes
  let frac := (pairComputes (k.andThen RationalArithmetic.natCastComputes) den).andThen
    RationalArithmetic.normalizationForwardComputes
  exact congrComputes frac (fun q => by
    simp [NormApprox.value,NormApprox.fraction,NormApprox.numerator,Rat.mkRat_eq_div,Nat.add_comm])

def precisionComputes : Computes inputEncoding encodingNatBool (fun d : Input => Scales.precision d.val.dimension) := by
  let n := PrecisionProgram.dimensionComputes
  let nn := (pairComputes n n).andThen RationalArithmetic.naturalMultiplicationComputes
  let fourth := (pairComputes nn nn).andThen RationalArithmetic.naturalMultiplicationComputes
  exact congrComputes ((pairComputes (constantComputes inputEncoding encodingNatBool 512) fourth).andThen
    RationalArithmetic.naturalMultiplicationComputes) (fun d => by
      dsimp only [Function.comp_def]
      unfold Scales.precision
      ring)

def fromInput : Computes (pairEncoding inputEncoding rationalEncoding) rationalEncoding
    (fun q : Input × ℚ => NormApprox.value q.2 (Scales.precision q.1.val.dimension)) :=
  (pairComputes (Wiring.secondComputes inputEncoding rationalEncoding)
    ((Wiring.firstComputes inputEncoding rationalEncoding).andThen precisionComputes)).andThen computes

theorem physical_cost (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (initList computes.machine.computer (encoding.encode q)))≤
      (primitivePolynomial computes).eval (encoding.encode q).length := computes_primitive_cost computes q

theorem intermediate_bits (q : Query) {k : ℕ} {c : computes.machine.Config}
    (hk : k≤computes.time.eval (encoding.encode q).length)
    (hc : (fun p => p.bind computes.machine.computer.step)^[k]
      (some (initList computes.machine.computer (encoding.encode q)))=some c) :
    stackSize c.stk≤(encoding.encode q).length+
      computes.time.eval (encoding.encode q).length*computes.machine.primitiveBudget := by
  have h := computes.machine.run_size_le _ c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ hk) _)

end
end Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.NormProgram
