import Holant.Proofs.LinearProgramming.Recovery.AllDimensionExactPoint.Semantics
import Holant.Complexity.GraphPreprocessing.OriginalCoefficient.ContextFlatMapInterface
import Holant.Complexity.StackProtocol

/-! Closed all-dimension exact rational point source and physical cost bounds. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open scoped BigOperators
namespace Source
noncomputable section
attribute [local irreducible] Programs.computes

abbrev Input := Codec.Input
def inputEncoding := Codec.inputEncoding
def outputEncoding := Codec.outputEncoding
def top (d : Input) : Option (List ℚ) := Programs.top d
def computes : Computes inputEncoding outputEncoding top := Programs.computes
def machine : Machine := computes.machine
def time : Polynomial ℕ := computes.time
private theorem computes_machine_eq : computes.machine=machine := rfl
private theorem computes_time_eq : computes.time=time := rfl
def primitivePolynomial : Polynomial ℕ := FixedFieldMachines.primitivePolynomial computes
def outputPolynomial : Polynomial ℕ := computes.outputBound.bound
def temporaryPolynomial : Polynomial ℕ := Polynomial.X+primitivePolynomial
def storagePolynomial : Polynomial ℕ := temporaryPolynomial

@[simp] theorem original_bytes (d : Input) : inputEncoding.encode d=Codec.inputEncoding.encode d := rfl
@[simp] theorem original_size (d : Input) : (inputEncoding.encode d).length=InputBounds.size d.val := rfl
@[simp] theorem original_output_bytes (out : Option (List ℚ)) :
    outputEncoding.encode out=Codec.outputEncoding.encode out := rfl

private def original_word_output {A B : Type} {ea : Encoding A Bool} {eb : Encoding B Bool}
    {f : A → B} (M : Computes ea eb f) (a : A) (word : List Bool) (he : ea.encode a=word) :
    TM2OutputsInTime M.machine.computer word (some (eb.encode (f a))) (M.time.eval word.length) := by
  subst word
  exact M.outputs a

def output (d : Input) : TM2OutputsInTime machine.computer (Codec.inputEncoding.encode d)
    (some (Codec.outputEncoding.encode (top d)))
    (time.eval (Codec.inputEncoding.encode d).length) := by
  dsimp only [machine,time,outputEncoding]
  exact original_word_output computes d (Codec.inputEncoding.encode d) (original_bytes d)
theorem inFP : InFP inputEncoding Codec.outputEncoding top := computes.inFP
theorem response (d : Input) : Codec.Response d.val (top d) := Semantics.response d
theorem none_iff (d : Input) : top d=none ↔ ¬∃ x, Codec.Feasible d.val x := Semantics.none_iff d
theorem some_sound (d : Input) (xs : List ℚ) (he : top d=some xs) :
    Codec.Solution d.val xs := Semantics.some_sound d xs he
theorem complete (d : Input) (hf : ∃ x, Codec.Feasible d.val x) :
    ∃ xs, top d=some xs ∧ Codec.Solution d.val xs := Semantics.complete d hf
theorem complete_iff (d : Input) :
    (∃ xs, top d=some xs ∧ Codec.Solution d.val xs) ↔ ∃ x, Codec.Feasible d.val x :=
  Semantics.complete_iff d
theorem same_common_vector (d : Input) (xs : List ℚ) (he : top d=some xs) :
    xs.length=d.val.dimension ∧
    (∀ i, ∑ j, (d.val.coefficient i j:ℚ)*Codec.point d.val xs j=d.val.constant i) ∧
    (∀ j, 0≤Codec.point d.val xs j ∧ Codec.point d.val xs j≤1) :=
  Semantics.same_common_vector d xs he

theorem execution (d : Input) :
    (fun s => s.bind machine.computer.step)^[(computes.outputs d).steps]
      (some (initList machine.computer (Codec.inputEncoding.encode d))) =
      some (haltList machine.computer (Codec.outputEncoding.encode (top d))) :=
  (computes.outputs d).evals_in_steps
theorem time_bound (d : Input) : (computes.outputs d).steps≤time.eval (InputBounds.size d.val) :=
  (computes.outputs d).steps_le_m
theorem output_word (d : Input) : (Codec.outputEncoding.encode (top d)).length≤
    outputPolynomial.eval (InputBounds.size d.val) := computes.outputBound.length_le d
theorem primitive_cost (d : Input) : primitiveCost machine (computes.outputs d).steps
    (some (initList machine.computer (Codec.inputEncoding.encode d)))≤
      primitivePolynomial.eval (InputBounds.size d.val) := computes_primitive_cost computes d

theorem temporary_bits (d : Input) (t : ℕ) (ht : t≤(computes.outputs d).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (Codec.inputEncoding.encode d)))=some c) :
    stackSize c.stk≤temporaryPolynomial.eval (InputBounds.size d.val) := by
  have hs := machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hlength : (Codec.inputEncoding.encode d).length=InputBounds.size d.val := rfl
  apply hs.trans
  simpa only [temporaryPolynomial,primitivePolynomial,FixedFieldMachines.primitivePolynomial,
    computes_machine_eq,computes_time_eq,hlength,Polynomial.eval_add,
    Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C] using Nat.add_le_add_left
      (Nat.mul_le_mul_right machine.primitiveBudget (ht.trans (time_bound d)))
        (Codec.inputEncoding.encode d).length
theorem storage_bits (d : Input) (t : ℕ) (ht : t≤(computes.outputs d).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (Codec.inputEncoding.encode d)))=some c) :
    stackSize c.stk≤storagePolynomial.eval (InputBounds.size d.val) := temporary_bits d t ht c hc
theorem stack_word (d : Input) (t : ℕ) (ht : t≤(computes.outputs d).steps) (c : machine.Config)
    (hc : (fun s => s.bind machine.computer.step)^[t]
      (some (initList machine.computer (Codec.inputEncoding.encode d)))=some c) (k : machine.K) :
    (c.stk k).length≤storagePolynomial.eval (InputBounds.size d.val) := by
  have hs : (c.stk k).length≤stackSize c.stk := by
    unfold stackSize
    exact Finset.single_le_sum (f := fun k => (c.stk k).length) (fun _ _ => Nat.zero_le _) (Finset.mem_univ k)
  exact hs.trans (storage_bits d t ht c hc)

/-- The original None codec is a halting word, not an unsupported branch or
absence of an operational output. Some is the same original rational framing. -/
theorem none_word (d : Input) (he : top d=none) :
    Codec.outputEncoding.encode (top d)=[false] :=
  congrArg Codec.outputEncoding.encode he
theorem some_word (d : Input) (xs : List ℚ) (he : top d=some xs) :
    Codec.outputEncoding.encode (top d)=true::Codec.pointEncoding.encode xs :=
  congrArg Codec.outputEncoding.encode he
theorem scalar_word (d : Input) (xs : List ℚ) (he : top d=some xs)
    (q : ℚ) (hq : q∈xs) : (rationalEncoding.encode q).length≤outputPolynomial.eval (InputBounds.size d.val) := by
  have hm := GraphPreprocessing.OriginalCoefficient.ContextFlatMap.member_length rationalEncoding xs q hq
  change (rationalEncoding.encode q).length≤(Codec.pointEncoding.encode xs).length at hm
  have ho := output_word d
  rw [some_word d xs he] at ho
  simp only [List.length_cons] at ho
  omega

end
end Source
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.AllDimensionExactPoint
