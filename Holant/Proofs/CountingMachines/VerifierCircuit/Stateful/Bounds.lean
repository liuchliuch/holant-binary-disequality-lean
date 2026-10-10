import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.FiniteMachine
import Holant.Proofs.CountingMachines.VerifierCircuit.Support.EncodingSize

set_option backward.isDefEq.respectTransparency false

/-!
# Actual reference/codec bounds and final output-stage primitive time

Ported reference proof. See the task validation reports.

The output-stage bound is for its actual prepared input. It does not establish
that the missing capacity-dependent environment compiler produces that input.
-/

namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Bounds


open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines
open FixedGadgetSubstitution GraphPreprocessing Support.EncodingSize

theorem circuit_references {n : ℕ} (c : Circuit n) :
    c.code.2 < n + c.gates ∧ ∀ r ∈ c.code.1, r.1 ≤ 2 ∧ r.2.1 ≤ n + c.gates ∧ r.2.2 ≤ n + c.gates := by
  induction c with
  | output i => exact ⟨i.isLt, by simp [Circuit.code]⟩
  | constant b c ih =>
    constructor
    · simpa [Circuit.code, Circuit.gates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.1
    · intro r hr
      simp only [Circuit.code, List.mem_cons] at hr
      rcases hr with rfl | hr
      · cases b <;> simp
      · simpa [Circuit.gates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.2 r hr
  | nand a b c ih =>
    constructor
    · simpa [Circuit.code, Circuit.gates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.1
    · intro r hr
      simp only [Circuit.code, List.mem_cons] at hr
      rcases hr with rfl | hr
      · have ha := a.isLt
        have hb := b.isLt
        simp only [Circuit.gates]
        exact ⟨le_rfl, by omega, by omega⟩
      · simpa [Circuit.gates, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using ih.2 r hr

theorem row_length (r : Circuit.Row) (R : ℕ)
    (h : r.1 ≤ 2 ∧ r.2.1 ≤ R ∧ r.2.2 ≤ R) :
    (Circuit.rowEncoding.encode r).length ≤ 6 + 3 * R := by
  have ht := le_trans (nat_code_length_le r.1) h.1
  have ha := le_trans (nat_code_length_le r.2.1) h.2.1
  have hb := le_trans (nat_code_length_le r.2.2) h.2.2
  simp only [Circuit.rowEncoding, framedProductEncoding_length]
  omega

theorem instance_length (c : CircuitInstance) :
    (CircuitInstance.encoding.encode c).length ≤ 50 * (c.inputs + c.circuit.gates + 1) ^ 2 := by
  let R := c.inputs + c.circuit.gates
  have hr := circuit_references c.circuit
  have hrows := framedList_length_le Circuit.rowEncoding c.circuit.code.1 (6 + 3 * R)
    (fun r h => row_length r R (hr.2 r h))
  have hout := le_trans (nat_code_length_le c.circuit.code.2) (Nat.le_of_lt hr.1)
  have hslots := framedList_length_le encodingBoolBool (List.replicate c.inputs false) 1
    (by intro b hb; cases b <;> decide)
  simp only [Circuit.code_rows_length, List.length_replicate] at hrows hslots
  change (CircuitInstance.codeEncoding.encode (List.replicate c.inputs false, c.circuit.code)).length ≤ _
  simp only [CircuitInstance.codeEncoding, Circuit.codeEncoding, framedProductEncoding_length]
  change 2 * (framedListEncode encodingBoolBool (List.replicate c.inputs false)).length + 1 +
    (2 * (framedListEncode Circuit.rowEncoding c.circuit.code.1).length + 1 +
      (encodingNatBool.encode c.circuit.code.2).length) ≤ _
  dsimp only [R] at *
  nlinarith [Nat.zero_le c.inputs, Nat.zero_le c.circuit.gates]

/-- The exact emitter witnesses bound every stored output reference. -/
theorem emitted_references {I O : Type} {p : Emit I O} {run : Rows.Run I O}
    (h : Rows.Exact p run) {n : ℕ} (input : I → Fin n) (layout : List O) :
    Environment.Bounded (n + (run (fun i => (input i).val)).1.length)
      (Environment.pack layout (run (fun i => (input i).val)).2) := by
  obtain ⟨m, ctx, out, hm, hc, ho, he⟩ := h Empty n (fun e => nomatch e) input
  have href : (run (fun i => (input i).val)).2 = (fun o => (out o).val) := (funext ho).symm
  rw [href, ← hm]
  exact Environment.pack_bounded layout out

theorem environment_length (env : Environment.Env) (R : ℕ) (h : Environment.Bounded R env) :
    (Environment.encoding.encode env).length ≤ (2 * R + 2) * env.length + 1 :=
  framedList_length_le encodingNatBool env R (fun r hr =>
    le_trans (nat_code_length_le r) (Nat.le_of_lt (h r hr)))

noncomputable section
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

def encodedPolynomial : Polynomial ℕ := 50 * (w.witnessLength + gatePolynomial w + 1) ^ 2

theorem compile_length (a : α) :
    (CircuitInstance.encoding.encode (compile w a)).length ≤ (encodedPolynomial w).eval (ea.encode a).length := by
  have h := instance_length (compile w a)
  have hg := compile_gates_le w a
  have hi : (compile w a).inputs = w.witnessLength.eval (ea.encode a).length := rfl
  change (CircuitInstance.encoding.encode (compile w a)).length ≤
    50 * (w.witnessLength.eval (ea.encode a).length + (compile w a).circuit.gates + 1) ^ 2 at h
  have hp := Nat.pow_le_pow_left (Nat.add_le_add_right
    (Nat.add_le_add_left hg (w.witnessLength.eval (ea.encode a).length)) 1) 2
  simp only [encodedPolynomial, Polynomial.eval_mul, Polynomial.eval_ofNat,
    Polynomial.eval_pow, Polynomial.eval_add, Polynomial.eval_one]
  exact le_trans h (Nat.mul_le_mul_left 50 hp)

def assemblyInput (c : CircuitInstance) : ℕ × (List Bool × ℕ) :=
  (c.inputs, OutputMachine.rowBytes c.circuit.code.1, c.circuit.code.2)

theorem assembly_input_length (c : CircuitInstance) :
    (OutputMachine.assemblyEncoding.encode (assemblyInput c)).length ≤
      (CircuitInstance.encoding.encode c).length := by
  rw [← OutputMachine.assemble_eq_encoding c]
  have hslots := framedListEncoding_length_lower encodingBoolBool (List.replicate c.inputs false)
  simp only [List.length_replicate] at hslots
  simp only [OutputMachine.assemblyEncoding, assemblyInput, pairEncoding_length,
    RuntimeParameters.unary, UnaryBinary.unaryEncoding, List.length_replicate,
    OutputMachine.assembleBytes, OutputMachine.wordEncoding, Frame.wordEncoding,
    RuntimeRows.slotBytes, Holant.Algebraic.frame_length, List.length_append,
    List.length_cons, List.length_nil, id_eq]
  change 2 * c.inputs + 1 ≤
    (framedListEncode encodingBoolBool (List.replicate c.inputs false)).length at hslots
  omega

def assemblyOriginalTime : Polynomial ℕ :=
  OutputMachine.assemblyPrimitivePolynomial.comp (encodedPolynomial w)

theorem assembly_original_bound (a : α) :
    primitiveCost OutputMachine.assembleComputes.machine
      (OutputMachine.assembleComputes.outputs (assemblyInput (compile w a))).steps
      (some (initList OutputMachine.assembleComputes.machine.computer
        (OutputMachine.assemblyEncoding.encode (assemblyInput (compile w a))))) ≤
      (assemblyOriginalTime w).eval (ea.encode a).length := by
  have hb := le_trans (assembly_input_length (compile w a)) (compile_length w a)
  have ht := natPolynomial_eval_mono OutputMachine.assemblyPrimitivePolynomial hb
  simpa only [assemblyOriginalTime, Polynomial.eval_comp] using
    le_trans (OutputMachine.assembly_primitive_bound (assemblyInput (compile w a))) ht

end
end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Stateful.Bounds
