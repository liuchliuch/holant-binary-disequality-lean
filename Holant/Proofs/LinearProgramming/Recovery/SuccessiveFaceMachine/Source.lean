import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.SuccessiveFaceMachine.GlobalBounds
import Holant.Complexity.FixedGadgetSubstitution.Compiler.Lists

set_option autoImplicit false

/-! Kernel-checked recovery component. Sole public entry of this batch. Original integer A,b
coefficients and unary dimensions, with WellFormed/n>=2 scope proofs, are all
input fields. Source.computes physically emits the existing Codec.outputEncoding
and Semantics.response proves the SAME output's original A*x=b and box bounds.

Producer chain: original Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt -> current-face threshold machine
ExactPointRecovery.Source.intervalPayloadComputes -> internal isolated Query
Scalar.query -> RationalExtraction.Source.extractComputes -> actual fixed-row
ThresholdProgram.validatedFixedComputes -> n-round ReturningLoop -> actual list.
Supporting/feasible/minimum/denominator facts are derived proof invariants only;
none is an extra machine input. The thickened terminal center is never a seed.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
namespace Source
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines Codec
open scoped BigOperators
noncomputable section
attribute [local irreducible] Programs.prepare Native.machine
abbrev Input := SuccessiveFaceMachine.Input
def inputEncoding := SuccessiveFaceMachine.inputEncoding
@[simp] theorem original_bytes (d : Input) : inputEncoding.encode d=Codec.inputEncoding.encode d.val := rfl

private def prepared_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Computes ea eb f) (N : Machine) (g : A → B) (W T : Polynomial ℕ)
    (receipt : ∀ a, TM2OutputsInTime N.computer (eb.encode (f a))
      (some (eb.encode (g a))) (T.eval (ea.encode a).length))
    (width : ∀ a, (eb.encode (f a)).length≤W.eval (ea.encode a).length) (a : A) :
    TM2OutputsInTime (M.machine.compose N).computer (ea.encode a) (some (eb.encode (g a)))
      ((M.time+2*(W+1)+T).eval (ea.encode a).length) := by
  let o := Machine.compose_correct M.machine N (ea.encode a) (eb.encode (f a)) (eb.encode (g a))
    (M.time.eval (ea.encode a).length) (T.eval (ea.encode a).length) (M.outputs a) (receipt a)
  refine {steps := o.steps,evals_in_steps := o.evals_in_steps,steps_le_m := o.steps_le_m.trans ?_}
  have hw := width a
  simp only [Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_one]
  omega

private def original_word_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Computes ea eb f) (a : A) (input : List Bool) (he : ea.encode a=input) :
    TM2OutputsInTime M.machine.computer input (some (eb.encode (f a))) (M.time.eval input.length) := by
  subst input
  exact M.outputs a

def stateMachine : Machine := Programs.prepare.machine.compose Native.machine
def stateTime : Polynomial ℕ := Programs.prepare.time+2*(GlobalBounds.stateWidth+1)+GlobalBounds.loopTime
def stateOutput (d : Input) : TM2OutputsInTime stateMachine.computer (inputEncoding.encode d)
    (some (stateEncoding.encode (resultState d))) (stateTime.eval (inputEncoding.encode d).length) := by
  dsimp only [stateMachine,stateTime,inputEncoding]
  exact prepared_output Programs.prepare Native.machine resultState GlobalBounds.stateWidth
    GlobalBounds.loopTime GlobalBounds.outputs GlobalBounds.initial_length d
attribute [local irreducible] stateMachine
def stateComputes : Computes inputEncoding stateEncoding resultState where
  machine := stateMachine
  time := stateTime
  outputs := stateOutput
attribute [local irreducible] stateComputes

def projected (s : State) : Option (List ℚ) := if alive s.2 then some (points s.2) else none
def projectPoints : Computes stateEncoding Codec.pointEncoding (fun s : State => points s.2) :=
  Body.payload.andThen Programs.pointsComputes
def projectAlive : Computes stateEncoding encodingBoolBool (fun s : State => alive s.2) :=
  Body.payload.andThen Programs.aliveComputes
def projectSome : Computes stateEncoding Codec.outputEncoding (fun s : State => some (points s.2)) :=
  recode (Holant.Complexity.FixedGadgetSubstitution.Compiler.joinComputes
    (constantComputes stateEncoding Holant.Complexity.GraphPreprocessing.Frame.wordEncoding [true])
    (projectPoints.andThen (Holant.Complexity.FixedGadgetSubstitution.Compiler.encodeComputes Codec.pointEncoding)))
    id (fun _ => rfl) (fun _ => rfl)
def projectComputes : Computes stateEncoding Codec.outputEncoding projected :=
  congrComputes (ifComputes projectAlive projectSome
    (constantComputes stateEncoding Codec.outputEncoding none)) (fun s => by simp [projected])
attribute [local irreducible] projectComputes
def value (d : Input) : Option (List ℚ) := SuccessiveFaceMachine.value d
def computes : Computes inputEncoding Codec.outputEncoding value := stateComputes.andThen projectComputes
def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time
private theorem computes_machine_eq : computes.machine=machine := rfl
private theorem computes_time_eq : computes.time=time := rfl
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial
def outputPolynomial : Polynomial ℕ := computes.outputBound.bound
def output (d : Codec.Input) (hn : 2≤d.val.dimension) :
    TM2OutputsInTime machine.computer (Codec.inputEncoding.encode d)
      (some (Codec.outputEncoding.encode (value ⟨d,hn⟩)))
      (time.eval (Codec.inputEncoding.encode d).length) := by
  dsimp only [machine,time]
  exact original_word_output computes ⟨d,hn⟩ (Codec.inputEncoding.encode d) (original_bytes ⟨d,hn⟩)
theorem inFP : InFP inputEncoding Codec.outputEncoding value := computes.inFP

theorem response (d : Input) : Codec.Response d.val.val (value d) := Semantics.response d
theorem none_iff (d : Input) : value d=none ↔ ¬∃ x, Codec.Feasible d.val.val x := Semantics.none_iff d
theorem same_original_false (d : Input) :
    value d=none ↔ (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value d.val).1=false :=
  (none_iff d).trans (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.rejected d).symm
theorem some_sound (d : Input) (xs : List ℚ) (he : value d=some xs) : Codec.Solution d.val.val xs :=
  Semantics.some_sound d xs he
theorem same_common_vector (d : Input) (xs : List ℚ) (he : value d=some xs) :
    xs.length=d.val.val.dimension ∧
    (∀ i, ∑ j, (d.val.val.coefficient i j:ℚ)*Codec.point d.val.val xs j=d.val.val.constant i) ∧
    (∀ j, 0≤Codec.point d.val.val xs j ∧ Codec.point d.val.val xs j≤1) :=
  some_sound d xs he
theorem same_original (d : Input) : (context («at» d d.val.val.dimension)).original=d.val :=
  Semantics.original_at d _
theorem execution (d : Input) : StackProtocol.RunsExactly machine.computer.step
    (initList machine.computer (inputEncoding.encode d))
    (haltList machine.computer (Codec.outputEncoding.encode (value d))) (computes.outputs d).steps :=
  (computes.outputs d).evals_in_steps
theorem time_bound (d : Input) : (computes.outputs d).steps≤time.eval (inputEncoding.encode d).length :=
  (computes.outputs d).steps_le_m
theorem output_word (d : Input) : (Codec.outputEncoding.encode (value d)).length≤
    outputPolynomial.eval (inputEncoding.encode d).length := computes.outputBound.length_le d
theorem primitive_cost (d : Input) : primitiveCost machine (computes.outputs d).steps
    (some (initList machine.computer (inputEncoding.encode d)))≤
      primitivePolynomial.eval (inputEncoding.encode d).length := computes_primitive_cost computes d
theorem temporary_bits (d : Input) (t : ℕ) (ht : t≤(computes.outputs d).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (inputEncoding.encode d)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (inputEncoding.encode d).length := by
  have hs := machine.run_size_le _ c t hc
  rw [machine.size_init] at hs
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,
    computes_machine_eq,computes_time_eq,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (time_bound d))) _
end
end Source
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.SuccessiveFaceMachine
