import Holant.Proofs.LinearProgramming.Parsing.Source
import Holant.Proofs.LinearProgramming.Support.CommonSupportProgram
import Holant.Proofs.LinearProgramming.Optimization.Infrastructure.OutputUniqueness

/-! Strict arbitrary-byte entry for the actual maximal-common-support program.
Outer None is malformed syntax/shape; Some None is a legal infeasible system.
The optional controller skips all LP work on a malformed word. -/
namespace Holant.LocalDrafts.RemoteWork.RationalLP.RawSource
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines StackProtocol
open Holant.LocalDrafts.TraversalCompletion.RationalLP
open Holant.OneHot.StackProgram.GraphLabelEncoding
open GraphPreprocessing Support
noncomputable section

/-- Exact transition iteration for arbitrary finite-machine state types. -/
def RunsOn {S : Type} (step : S → Option S) (start finish : S) (steps : ℕ) : Prop :=
  (fun state => state.bind step)^[steps] (some start) = some finish

abbrev Result := Option (Option (List ℚ))
def outputEncoding := optionEncoding Codec.outputEncoding
def value (input : List Bool) : Result :=
  (Parsing.Source.parse input).map CommonSupportPoint.value
def callee := Recovery.Infrastructure.OptionMap.computes Support.CommonSupportProgram.Source.computes
/-- Sole arbitrary-byte entry. Malformed is outer None; legal original-LP
infeasibility is Some None. The actual optional false branch skips the callee. -/
def entry : Computes Frame.wordEncoding outputEncoding value :=
  Parsing.Source.parseComputes.andThen callee
def entryMachine : Machine := entry.machine
def entryTime : Polynomial ℕ := entry.time
def entryPrimitive : Polynomial ℕ := FixedFieldMachines.primitivePolynomial entry
def entryStorage : Polynomial ℕ := Polynomial.X+entryPrimitive

@[simp] theorem entry_same_program : entryMachine=
    Parsing.Source.parseComputes.machine.compose
      (Recovery.Infrastructure.OptionMap.machine Support.CommonSupportProgram.Source.machine) := rfl
@[simp] theorem entry_same_clock : entryTime=
    Parsing.Source.parseComputes.time+
      2*(Parsing.Source.parseComputes.outputBound.bound+1)+
      callee.time.comp Parsing.Source.parseComputes.outputBound.bound := rfl
theorem entry_inFP : InFP Frame.wordEncoding outputEncoding value := entry.inFP
theorem entry_execution (input : List Bool) : RunsOn entryMachine.computer.step
    (initList entryMachine.computer input) (haltList entryMachine.computer (outputEncoding.encode (value input)))
    (entry.outputs input).steps := (entry.outputs input).evals_in_steps
theorem entry_time_bound (input : List Bool) : (entry.outputs input).steps≤entryTime.eval input.length :=
  (entry.outputs input).steps_le_m
theorem entry_primitive_bound (input : List Bool) : primitiveCost entryMachine (entry.outputs input).steps
    (some (initList entryMachine.computer input))≤entryPrimitive.eval input.length :=
  computes_primitive_cost entry input
theorem entry_output_bound (input : List Bool) : (outputEncoding.encode (value input)).length≤
    entry.outputBound.bound.eval input.length := entry.outputBound.length_le input
theorem entry_prefix_storage (input : List Bool) (t : ℕ) (ht : t≤(entry.outputs input).steps)
    (c : entryMachine.Config) (hc : (fun p => p.bind entryMachine.computer.step)^[t]
      (some (initList entryMachine.computer input))=some c) :
    stackSize c.stk≤entryStorage.eval input.length := by
  have hs := entryMachine.run_size_le _ c t hc
  rw [Machine.size_init] at hs
  have hb := Nat.mul_le_mul_right entryMachine.primitiveBudget (ht.trans (entry.outputs input).steps_le_m)
  apply hs.trans
  simpa only [entryStorage,entryPrimitive,FixedFieldMachines.primitivePolynomial,entryMachine,entryTime,
    Polynomial.eval_add,Polynomial.eval_X,Polynomial.eval_mul,Polynomial.eval_C,Frame.wordEncoding,id_eq] using Nat.add_le_add_left hb input.length

theorem legal_value (d : Codec.Input) : value (Codec.inputEncoding.encode d)=some (CommonSupportPoint.value d) := by
  have hp := (Parsing.Source.parse_some_iff
    (Codec.inputEncoding.encode d) d).mpr rfl
  rw [value,hp,Option.map_some]
theorem malformed_iff (input : List Bool) : value input=none ↔ ¬∃ d : Codec.Input,
    input=Codec.inputEncoding.encode d := by
  rw [value,Option.map_eq_none_iff,Parsing.Source.parse_none_iff]
theorem legal_infeasible_iff (d : Codec.Input) : value (Codec.inputEncoding.encode d)=some none ↔
    ¬∃ x, Codec.Feasible d.val x := by
  rw [legal_value,Option.some.injEq]
  exact CommonSupportPoint.none_iff d
theorem some_sound (input : List Bool) (xs : List ℚ) (he : value input=some (some xs)) :
    ∃ d : Codec.Input, input=Codec.inputEncoding.encode d ∧ Codec.Solution d.val xs ∧
      (∀ j, 0<Codec.point d.val xs j ↔ Codec.Positive d.val j) ∧
      (∀ j, Codec.point d.val xs j=0 ↔ ¬Codec.Positive d.val j) := by
  obtain ⟨d,hp,hd⟩ := Option.map_eq_some_iff.mp he
  exact ⟨d,(Parsing.Source.parse_some_iff input d).mp hp,
    Support.CommonSupportProgram.Source.support d xs hd⟩

/-- Each exact clean result word identifies this actual complete run's
result. Some/None semantics are not assumed from a bit predicate alone. -/
theorem result_run_iff (input : List Bool) (out : Result) :
    (∃ steps, RunsOn entryMachine.computer.step (initList entryMachine.computer input)
      (haltList entryMachine.computer (outputEncoding.encode out)) steps) ↔ value input=out := by
  constructor
  · rintro ⟨steps,hrun⟩
    apply outputEncoding.encode_injective
    exact Optimization.Infrastructure.OutputUniqueness.machine_output_unique entryMachine input
      (outputEncoding.encode (value input)) (outputEncoding.encode out)
      (entry.outputs input).steps steps (entry_execution input) hrun
  · intro he
    exact ⟨(entry.outputs input).steps,by simpa only [he] using entry_execution input⟩

theorem malformed_execution (input : List Bool)
    (hp : Parsing.Source.parse input=none) :
    RunsOn entryMachine.computer.step (initList entryMachine.computer input)
      (haltList entryMachine.computer [false]) (entry.outputs input).steps := by
  have hv : value input=none := by rw [value,hp]; rfl
  have hw : outputEncoding.encode (none : Result) = [false] := rfl
  simpa only [hv,hw] using entry_execution input
theorem malformed_callee : RunsOn callee.machine.computer.step
    (initList callee.machine.computer [false]) (haltList callee.machine.computer [false]) 2 :=
  Recovery.Infrastructure.OptionMap.none_exact Support.CommonSupportProgram.Source.machine
theorem malformed_run_iff (input : List Bool) :
    (∃ steps, RunsOn entryMachine.computer.step (initList entryMachine.computer input)
      (haltList entryMachine.computer [false]) steps) ↔ ¬∃ d : Codec.Input,
        input=Codec.inputEncoding.encode d :=
  (result_run_iff input none).trans (malformed_iff input)
theorem infeasible_execution_iff (d : Codec.Input) :
    (∃ steps, RunsOn entryMachine.computer.step
      (initList entryMachine.computer (Codec.inputEncoding.encode d))
      (haltList entryMachine.computer [true,false]) steps) ↔ ¬∃ x, Codec.Feasible d.val x :=
  (result_run_iff (Codec.inputEncoding.encode d) (some none)).trans (legal_infeasible_iff d)
theorem point_execution_sound (input : List Bool) (xs : List ℚ) (steps : ℕ)
    (hrun : RunsOn entryMachine.computer.step (initList entryMachine.computer input)
      (haltList entryMachine.computer (true::true::Codec.pointEncoding.encode xs)) steps) :
    ∃ d : Codec.Input, input=Codec.inputEncoding.encode d ∧ Codec.Solution d.val xs ∧
      (∀ j, 0<Codec.point d.val xs j ↔ Codec.Positive d.val j) ∧
      (∀ j, Codec.point d.val xs j=0 ↔ ¬Codec.Positive d.val j) :=
  some_sound input xs ((result_run_iff input (some (some xs))).mp ⟨steps,hrun⟩)
theorem feasible_run_iff (input : List Bool) :
    (∃ xs steps, RunsOn entryMachine.computer.step (initList entryMachine.computer input)
      (haltList entryMachine.computer (true::true::Codec.pointEncoding.encode xs)) steps) ↔
      ∃ d : Codec.Input, input=Codec.inputEncoding.encode d ∧ ∃ x, Codec.Feasible d.val x := by
  constructor
  · rintro ⟨xs,steps,hrun⟩
    obtain ⟨d,hd,hs,_,_⟩ := point_execution_sound input xs steps hrun
    exact ⟨d,hd,Codec.point d.val xs,hs.2⟩
  · rintro ⟨d,hd,hf⟩
    obtain ⟨xs,hx,_⟩ := CommonSupportPoint.complete d hf
    have hv : value input=some (some xs) := by rw [hd,legal_value,hx]
    have hw : outputEncoding.encode (some (some xs)) = true::true::Codec.pointEncoding.encode xs := rfl
    exact ⟨xs,(entry.outputs input).steps,by simpa only [hv,hw] using entry_execution input⟩

end
end Holant.LocalDrafts.RemoteWork.RationalLP.RawSource
