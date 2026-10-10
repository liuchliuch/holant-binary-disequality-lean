import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.ScalarQuery

set_option autoImplicit false

/-! Kernel-checked recovery component. Actual current-face threshold optimization, endpoint
normalization, ORIGINAL binary D production, and actual Euclidean extraction.
No optimizer callback, free scalar extractor or chosen minimum appears here.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Scalar
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution.Compiler Codec
noncomputable section
def intervalComputes : Computes contextEncoding ExactPointRecovery.payloadEncoding intervalPayload :=
  ContextProgram.current.andThen ExactPointRecovery.Source.intervalPayloadComputes
def numeratorComputes : Computes contextEncoding encodingNatBool
    (fun c : Context => ExactPointRecovery.numerator (intervalPayload c)) :=
  intervalComputes.andThen ExactPointRecovery.numeratorComputes
def denominatorComputes : Computes contextEncoding encodingNatBool
    (fun c : Context => ExactPointRecovery.denominator (intervalPayload c)) :=
  intervalComputes.andThen ExactPointRecovery.denominatorComputes
def successorComputes : Computes contextEncoding encodingNatBool
    (fun c : Context => ExactPointRecovery.numerator (intervalPayload c)+1) :=
  (pairComputes numeratorComputes (constantComputes contextEncoding encodingNatBool 1)).andThen
    Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.Infrastructure.addComputes
def lowerComputes : Computes contextEncoding rationalEncoding lower :=
  congrComputes ((pairComputes (numeratorComputes.andThen RationalArithmetic.natCastComputes)
    denominatorComputes).andThen RationalArithmetic.normalizationForwardComputes)
      (fun c => by simp [lower,Rat.mkRat_eq_div])
def upperComputes : Computes contextEncoding rationalEncoding upper :=
  congrComputes ((pairComputes (successorComputes.andThen RationalArithmetic.natCastComputes)
    denominatorComputes).andThen RationalArithmetic.normalizationForwardComputes)
      (fun c => by simp [upper,Rat.mkRat_eq_div])
def boundComputes : Computes contextEncoding encodingNatBool
    (fun c : Context => InputBounds.denominator c.original.val) :=
  ContextProgram.originalRaw.andThen Holant.LocalDrafts.RemoteWork.RationalLP.Foundation.ExactSolve.DenominatorProgram.computes
def rawQueryComputes : Computes contextEncoding RationalExtraction.queryEncoding rawQuery :=
  pairComputes (pairComputes lowerComputes upperComputes) boundComputes
def queryComputes : Computes contextEncoding RationalExtraction.Source.inputEncoding query :=
  recode rawQueryComputes id (fun _ => rfl) (fun _ => rfl)
def value (c : Context) : Option ℚ := RationalExtraction.Source.extracted (query c)
def computes : Computes contextEncoding RationalExtraction.Source.scalarEncoding value :=
  queryComputes.andThen RationalExtraction.Source.extractComputes

/-- Bounds use the returned Option word alone, even on infeasible faces.
This uniform producer controls every fixation row before feasibility is used. -/
theorem returned_bounds (c : Context) (r : ℚ) (h : value c=Option.some r) :
    0≤r ∧ r≤1 ∧ r.den≤InputBounds.denominator c.original.val := by
  have hs := RationalExtraction.Source.some_sound (query c) r h
  change lower c≤r ∧ r≤upper c ∧ r.den≤InputBounds.denominator c.original.val at hs
  exact ⟨(box c).1.trans hs.1,hs.2.1.trans (box c).2.2,hs.2.2⟩
theorem returned_word (c : Context) (r : ℚ) (h : value c=Option.some r) :
    (rationalEncoding.encode r).length≤4*InputBounds.size c.original.val^2+4 := by
  have hb := returned_bounds c r h
  have hn := ExactPointRecovery.Denominator.box_numerator r ⟨hb.1,hb.2.1⟩
  have hh : rationalHeight r≤InputBounds.denominator c.original.val := max_le (hn.trans hb.2.2) hb.2.2
  have hz := Nat.size_le_size hh
  have hd : (InputBounds.denominator c.original.val).size=2*InputBounds.size c.original.val^2+1 := by
    simp [InputBounds.denominator,Nat.size_pow]
  rw [hd] at hz
  have hw := rationalEncoding_length_le_height r
  unfold rationalBitHeight at hw
  omega
theorem execution (c : Context) : Holant.Complexity.StackProtocol.RunsExactly computes.machine.computer.step
    (initList computes.machine.computer (contextEncoding.encode c))
    (haltList computes.machine.computer (RationalExtraction.Source.scalarEncoding.encode (value c)))
    (computes.outputs c).steps := (computes.outputs c).evals_in_steps
theorem time_bound (c : Context) : (computes.outputs c).steps≤
    computes.time.eval (contextEncoding.encode c).length := (computes.outputs c).steps_le_m
theorem output_bound (c : Context) :
    (RationalExtraction.Source.scalarEncoding.encode (value c)).length≤
      computes.outputBound.bound.eval (contextEncoding.encode c).length := computes.outputBound.length_le c
theorem primitive_bound (c : Context) : primitiveCost computes.machine (computes.outputs c).steps
    (some (initList computes.machine.computer (contextEncoding.encode c)))≤
      (primitivePolynomial computes).eval (contextEncoding.encode c).length := computes_primitive_cost computes c
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial computes
theorem temporary_bound (q : Context) (t : ℕ) (ht : t≤(computes.outputs q).steps) (c : computes.machine.Config)
    (hc : (fun s => s.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (contextEncoding.encode q)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (contextEncoding.encode q).length := by
  have hs := computes.machine.run_size_le _ c t hc
  rw [computes.machine.size_init] at hs
  apply hs.trans
  simpa only [temporaryPolynomial,FixedFieldMachines.primitivePolynomial,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right computes.machine.primitiveBudget (ht.trans (time_bound q))) _
end
end Scalar
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
