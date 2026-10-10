import Holant.Proofs.LinearProgramming.Support.MachineCombinators
import Holant.Proofs.LinearProgramming.Recovery.ExactPointRecovery.ThresholdProgram
import Holant.Proofs.LinearProgramming.Complexity.CounterLoop.Receipt

set_option autoImplicit false

/-! Kernel-checked recovery component. Ported into the exclusive task namespace and validated with the pinned toolchain.
An actual emitted upper-threshold problem is passed to the unchanged physical
Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt machine. The Boolean below is parsed from THAT returned
word. Its returned original-input field is the emitted threshold matrix,
and its center still has only Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Thickening.At semantics for that matrix.
-/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.LocalDrafts.RemoteWork.RationalLP.Foundation
open Holant.LocalDrafts.RemoteWork.RationalLP.Support.MachineCombinators
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines Codec
namespace Request
noncomputable section
abbrev Query := ThresholdProgram.ValidatedQuery
def encoding := ThresholdProgram.validatedEncoding
abbrev Data := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.Data
def dataEncoding := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.encoding
def highValue (q : Query) : Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Source.HighInput :=
  ⟨ThresholdProgram.value q,by
    have hj := q.1.2.isLt
    change 2≤q.1.1.val.dimension+1
    omega⟩
def highComputes : Computes encoding Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Source.highEncoding highValue :=
  recode ThresholdProgram.validatedComputes id (fun _ => rfl) (fun _ => rfl)
def value (q : Query) : Data := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value (ThresholdProgram.value q)
def computes : Computes encoding dataEncoding value :=
  highComputes.andThen Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.computes
def bit (q : Query) : Bool := (value q).1
def bitComputes : Computes encoding encodingBoolBool bit :=
  computes.andThen (Wiring.firstComputes encodingBoolBool Holant.LocalDrafts.RemoteWork.RationalLP.Optimization.Search.StepProgram.encoding)

theorem original (q : Query) : (value q).2.1=ThresholdProgram.value q :=
  Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.original (highValue q)
theorem accepted (c : CoordinateQuery) (p q : ℕ) (hq : 0<q) :
    bit (c,p,q)=true ↔ ∃ x, Feasible c.1.val x ∧ x c.2≤(p:ℚ)/q := by
  have h := Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.accepted
    (highValue (c,p,q))
  change (Holant.LocalDrafts.RemoteWork.RationalLP.Complexity.CounterLoop.Receipt.value
    (ThresholdProgram.value (c,p,q))).1=true ↔
      ∃ x, Feasible (ThresholdProgram.value (c,p,q)).val x at h
  exact h.trans (ThresholdProgram.exists_iff c p q hq)
theorem rejected (c : CoordinateQuery) (p q : ℕ) (hq : 0<q) :
    bit (c,p,q)=false ↔ ¬∃ x, Feasible c.1.val x ∧ x c.2≤(p:ℚ)/q := by
  rw [← accepted c p q hq]
  cases bit (c,p,q) <;> decide

theorem same_steps (q : Query) :
    Holant.Complexity.StackProtocol.RunsExactly computes.machine.computer.step
      (initList computes.machine.computer (encoding.encode q))
      (haltList computes.machine.computer (dataEncoding.encode (value q)))
      (computes.outputs q).steps := (computes.outputs q).evals_in_steps
theorem output_bound (q : Query) : (dataEncoding.encode (value q)).length≤
    computes.outputBound.bound.eval (encoding.encode q).length := computes.outputBound.length_le q
theorem primitive_bound (q : Query) :
    primitiveCost computes.machine (computes.outputs q).steps
      (some (initList computes.machine.computer (encoding.encode q)))≤
      (primitivePolynomial computes).eval (encoding.encode q).length := computes_primitive_cost computes q
theorem temporary_bits (q : Query) (t : ℕ) (ht : t≤(computes.outputs q).steps)
    (c : computes.machine.Config)
    (hc : (fun p => p.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (encoding.encode q)))=some c) :
    stackSize c.stk≤(encoding.encode q).length+
      computes.time.eval (encoding.encode q).length*computes.machine.primitiveBudget := by
  have hs := computes.machine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (ht.trans (computes.outputs q).steps_le_m)) _)

end
end Request
end Holant.LocalDrafts.RemoteWork.RationalLP.Recovery.ExactPointRecovery
