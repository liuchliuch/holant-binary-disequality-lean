import Holant.Proofs.Counting.RawGraphMachine.Loop


set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace Holant.LocalDrafts.CountingHardness.RawGraphMachine
open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open GraphPreprocessing StackProtocol

def «initialize» : Computes CircuitInstance.encoding workEncoding (fun c => initial (input c)) :=
  recode Stages.initialComputes input (fun _ => rfl) (fun _ => rfl)

theorem clock_sufficient (c : CircuitInstance) : c.circuit.gates ≤ Bounds.width (initial (input c)) := by
  have h := framedListEncoding_length_lower Circuit.rowEncoding c.circuit.code.1
  rw [Circuit.code_rows_length] at h
  rw [Bounds.work_length]
  change c.circuit.gates ≤
    4 * ((framedListEncoding Circuit.rowEncoding).encode c.circuit.code.1).length +
      2 * (encodingNatBool.encode c.circuit.code.2).length +
        (memoryEncoding.encode (initial (input c)).2).length + 3
  omega

theorem serialized_exact (c : CircuitInstance) :
    RawClosedNetwork.encoding.encode (result (Loop.value (initial (input c)))) =
      (RawClosedNetwork.validatedEncoding 5 1 GateAlphabet.arity).encode (RawCompiler.validated c) :=
  congrArg RawClosedNetwork.encoding.encode
    (result_exact c (Bounds.width (initial (input c))) (clock_sufficient c))

def rawComputes : Computes CircuitInstance.encoding RawClosedNetwork.encoding RawCompiler.compile :=
  congrComputes (((«initialize».andThen Loop.frameComputes).andThen Loop.computes).andThen Stages.resultComputes)
    (fun c => result_exact c (Bounds.width (initial (input c))) (clock_sufficient c))

attribute [local irreducible] rawComputes

/-- Contract endpoint: no compiler, correctness, output-size, environment, or
time assumption is an argument of this construction. -/
def computes : Computes CircuitInstance.encoding
    (RawClosedNetwork.validatedEncoding 5 1 GateAlphabet.arity) RawCompiler.validated :=
  recode rawComputes id (fun _ => rfl) (fun _ => rfl)

theorem machine_unchanged : computes.machine = rawComputes.machine := rfl
theorem time_unchanged : computes.time = rawComputes.time := rfl

def outputs (c : CircuitInstance) :
    TM2OutputsInTime computes.machine.computer (CircuitInstance.encoding.encode c)
      (some ((RawClosedNetwork.validatedEncoding 5 1 GateAlphabet.arity).encode (RawCompiler.validated c)))
      (computes.time.eval (CircuitInstance.encoding.encode c).length) := computes.outputs c

theorem exact_run (c : CircuitInstance) :
    (fun q => q.bind computes.machine.computer.step)^[(computes.outputs c).steps]
      (some (initList computes.machine.computer (CircuitInstance.encoding.encode c))) =
      some (haltList computes.machine.computer
        ((RawClosedNetwork.validatedEncoding 5 1 GateAlphabet.arity).encode (RawCompiler.validated c))) := by
  simpa only [Function.flip_def, Option.map_some, Option.bind_eq_bind] using (computes.outputs c).evals_in_steps

theorem original_primitive_bound (c : CircuitInstance) :
    primitiveCost computes.machine (computes.outputs c).steps
      (some (initList computes.machine.computer (CircuitInstance.encoding.encode c))) ≤
        (primitivePolynomial computes).eval (CircuitInstance.encoding.encode c).length :=
  computes_primitive_cost computes c

def scratchPolynomial : Polynomial ℕ := Polynomial.X + primitivePolynomial computes

/-- Every reached prefix configuration, including nested provider scratch, is
bounded by the original input length and actual primitive instruction budget.
The premise identifies a run prefix; it does not assume a complexity bound. -/
theorem scratch_bound (c : CircuitInstance) (t : ℕ) (ht : t ≤ (computes.outputs c).steps)
    (d : computes.machine.Config)
    (hrun : (fun q => q.bind computes.machine.computer.step)^[t]
      (some (initList computes.machine.computer (CircuitInstance.encoding.encode c))) = some d) :
    stackSize d.stk ≤ scratchPolynomial.eval (CircuitInstance.encoding.encode c).length := by
  have h := computes.machine.run_size_le _ d t hrun
  rw [Machine.size_init] at h
  have ht' := ht.trans (computes.outputs c).steps_le_m
  have hm := Nat.mul_le_mul_right computes.machine.primitiveBudget ht'
  simp only [scratchPolynomial, primitivePolynomial, Polynomial.eval_add, Polynomial.eval_X,
    Polynomial.eval_mul, Polynomial.eval_C]
  omega

end Holant.LocalDrafts.CountingHardness.RawGraphMachine
