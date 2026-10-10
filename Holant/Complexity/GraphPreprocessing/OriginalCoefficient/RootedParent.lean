import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootCaseCall
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedFlag
import Holant.Complexity.BinaryCompose.Identity

/-! One physical query handles both roots and nonroots. The original unary root
and target fields are compared by a finite machine; its Boolean controls the
real branch. Nonroots run actual root allocation and bounded first-hit search. -/
namespace Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
open Turing Computability StackProtocol BinaryCompose FixedFieldMachines
open Holant.OneHot.Computable
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 32768
set_option synthInstance.maxSize 4096
set_option Elab.async false

abbrev Base := RootedNonroot.Base
def Valid (x : Base) : Prop := x.2.1∈(RootedNonroot.baseGraph x).reach x.1.2 x.1.1
instance (x : Base) : Decidable (Valid x) := inferInstanceAs (Decidable (_∈_))
abbrev Input := {x : Base // Valid x}
def inputEncoding : Encoding Input Bool where
  encode x := RootedNonroot.baseEncoding.encode x.val
  decode bits := do
    let x ← RootedNonroot.baseEncoding.decode bits
    if h : Valid x then some ⟨x,h⟩ else none
  decode_encode x := by simp [x.property]

def nonroot (x : Input) (h : x.val.1.2≠x.val.2.1) : RootedNonroot.Input :=
  ⟨x.val,⟨x.property,fun he => h he.symm⟩⟩
def value (x : Input) : ℕ × Option (ℕ × Bool) :=
  if h : x.val.1.2=x.val.2.1 then (0,none) else RootedNonroot.value (nonroot x h)
abbrev outputEncoding := RootedNonroot.outputEncoding

def flag (x : Input) : Bool := RootedFlag.value x.val
noncomputable def flagComputes : Computes inputEncoding encodingBoolBool flag :=
  recode RootedFlag.computes Subtype.val (fun _ => rfl) (fun _ => rfl)
noncomputable def prepareComputes : Computes inputEncoding (pairEncoding encodingBoolBool inputEncoding) (fun x => (flag x,x)) :=
  pairComputes flagComputes (identityComputes inputEncoding)
def prepared (x : Input) : List Bool := (pairEncoding encodingBoolBool inputEncoding).encode (flag x,x)

abbrev prepareMachine : Machine := pairMachine RootedFlag.machine identityMachine
abbrev caseMachine : Machine := RootCase.machine RootedNonroot.machine
abbrev machine : Machine := prepareMachine.compose caseMachine
@[simp] theorem prepareComputes_machine : prepareComputes.machine=prepareMachine := rfl

@[simp] theorem prepared_length (x : Input) : (prepared x).length=(inputEncoding.encode x).length+3 := by
  simp [prepared,pairEncoding,encodingBoolBool,encodeBool,Holant.Algebraic.frame_length,Nat.add_comm]

noncomputable def outputSize : Polynomial ℕ := RootedNonroot.computes.outputBound.bound
noncomputable def branchPolynomial : Polynomial ℕ :=
  RootedNonroot.timePolynomial+2*Polynomial.X+2*outputSize+10

noncomputable def case_timed (x : Input) :
    TM2OutputsInTime caseMachine.computer (prepared x) (some (outputEncoding.encode (value x)))
      (branchPolynomial.eval (inputEncoding.encode x).length) := by
  by_cases hroot : x.val.1.2=x.val.2.1
  · have hp : prepared x = Holant.Algebraic.frame [true]++inputEncoding.encode x := by
      simp [prepared,flag,RootedFlag.value,hroot,pairEncoding,encodingBoolBool,encodeBool]
    have ho : outputEncoding.encode (value x)=[false,false] := by
      simp [value,hroot,outputEncoding,RootedNonroot.outputEncoding,pairEncoding,UnaryBinary.unaryEncoding,ParentRowEncoding.parent,Holant.Algebraic.frame]
    refine { steps := (inputEncoding.encode x).length+8, evals_in_steps := ?_, steps_le_m := ?_ }
    · rw [hp,ho]
      exact RootCase.root_exact RootedNonroot.machine (inputEncoding.encode x)
    · simp only [branchPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      omega
  · let y := nonroot x hroot
    let witness := RootedNonroot.timed y
    have hp : prepared x = Holant.Algebraic.frame [false]++inputEncoding.encode x := by
      simp [prepared,flag,RootedFlag.value,hroot,pairEncoding,encodingBoolBool,encodeBool]
    have ho : value x = RootedNonroot.value y := by simp [value,hroot,y]
    have run := RootCase.nonroot_exact RootedNonroot.machine (inputEncoding.encode x)
      (outputEncoding.encode (RootedNonroot.value y)) witness.steps witness.evals_in_steps
    refine { steps := witness.steps+2*(inputEncoding.encode x).length+
      2*(outputEncoding.encode (RootedNonroot.value y)).length+10, evals_in_steps := ?_, steps_le_m := ?_ }
    · rw [hp,ho]
      exact run
    · have ht := witness.steps_le_m
      have hs := RootedNonroot.computes.outputBound.length_le y
      change (outputEncoding.encode (RootedNonroot.value y)).length≤outputSize.eval (inputEncoding.encode x).length at hs
      change witness.steps≤RootedNonroot.timePolynomial.eval (inputEncoding.encode x).length at ht
      simp only [branchPolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
      omega

noncomputable def timePolynomial : Polynomial ℕ := prepareComputes.time+2*(Polynomial.X+4)+branchPolynomial
noncomputable def timed (x : Input) :
    TM2OutputsInTime machine.computer (inputEncoding.encode x) (some (outputEncoding.encode (value x)))
      (timePolynomial.eval (inputEncoding.encode x).length) := by
  have h := Machine.compose_correct prepareMachine caseMachine
    (inputEncoding.encode x) (prepared x) (outputEncoding.encode (value x))
    (prepareComputes.time.eval (inputEncoding.encode x).length) (branchPolynomial.eval (inputEncoding.encode x).length)
    (prepareComputes.outputs x) (case_timed x)
  refine {steps := h.steps, evals_in_steps := h.evals_in_steps, steps_le_m := ?_}
  have hp := h.steps_le_m
  have hl := prepared_length x
  simp only [timePolynomial,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_ofNat,Polynomial.eval_X]
  omega

noncomputable def computes : Computes inputEncoding outputEncoding value where
  machine := machine
  time := timePolynomial
  outputs := timed

theorem inFP : InFP inputEncoding outputEncoding value := computes.inFP
noncomputable def primitivePolynomial : Polynomial ℕ := timePolynomial*Polynomial.C machine.primitiveBudget
theorem primitive_bound (x : Input) :
    primitiveCost machine (timed x).steps (some (initList machine.computer (inputEncoding.encode x))) ≤
      primitivePolynomial.eval (inputEncoding.encode x).length := by
  have h := Nat.mul_le_mul_right machine.primitiveBudget (timed x).steps_le_m
  simpa only [primitivePolynomial,Polynomial.eval_mul,Polynomial.eval_C] using le_trans (primitiveCost_le _ _ _) h

end Holant.Complexity.GraphPreprocessing.OriginalCoefficient.RootedParent
