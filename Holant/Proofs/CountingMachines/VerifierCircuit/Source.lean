import Holant.Proofs.CountingMachines.VerifierCircuit.Stateful.CapacityFrontend.Exactness.Reduction

/-!
Ported reference proof chain. See the task validation reports.

Sole entry for universal hardness over the project's actual SharpPWitness.
The only supplied program is the verifier inside that witness. The existing
capacity frontend generates the exact existing NAND circuit from original
input bytes; no circuit, tableau, layout, time or reduction is a premise.
The query program is also exposed for direct one-query native consumers.
Equivalence with conventional nondeterministic #P machine presentations is
a separate obligation and is not asserted by circuit_counting_hard.
-/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Source

open Turing Computability Holant.Complexity BinaryCompose FixedFieldMachines

section Witness
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ} (w : SharpPWitness ea f)

/-- The old compiler on the original encoded input, with exactly the original
fixed-length witness slots. This is not a circuit supplied by the caller. -/
def query : α → CircuitInstance := VerifierCircuit.compile w

/-- Exact bytes from the actual capacity frontend Boolean-stack program. -/
def queryComputes : Computes ea CircuitInstance.encoding (query w) :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.computes w

theorem query_inputs (a : α) :
    (query w a).inputs = w.witnessLength.eval (ea.encode a).length := rfl

theorem query_eval (a : α) (bits : Fin (query w a).inputs → Bool) :
    (query w a).circuit.eval bits = w.accept (a, List.ofFn bits) :=
  VerifierCircuit.compile_eval w a bits

theorem query_value (a : α) : CircuitInstance.value (query w a) = f a :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.preserves_count w a

/-- All internal gates, including padding and both compiled branch arms, have
one determined extension for each witness assignment. -/
theorem query_unique_extension (a : α) (bits : Fin (query w a).inputs → Bool) :
    ∃! gates : Fin (query w a).circuit.gates → Bool,
      (query w a).circuit.consistent bits gates = true :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.unique_extension w a bits

theorem query_extended_value (a : α) :
    countAccepted (fun xz : (Fin (query w a).inputs → Bool) ×
      (Fin (query w a).circuit.gates → Bool) =>
        (query w a).circuit.accepts xz.1 xz.2) = f a :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.preserves_extended_count w a

theorem query_program : (queryComputes w).machine =
    (VerifierCircuit.Stateful.CapacityFrontend.Frontend.rawBytesComputes w).machine :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.machine_unchanged w

theorem query_time : (queryComputes w).time =
    (VerifierCircuit.Stateful.CapacityFrontend.Frontend.rawBytesComputes w).time :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.time_unchanged w

def query_outputs (a : α) :
    TM2OutputsInTime (queryComputes w).machine.computer (ea.encode a)
      (some (CircuitInstance.encoding.encode (query w a)))
      ((queryComputes w).time.eval (ea.encode a).length) :=
  (queryComputes w).outputs a

theorem query_length_bound (a : α) :
    (CircuitInstance.encoding.encode (query w a)).length ≤
      (queryComputes w).outputBound.bound.eval (ea.encode a).length :=
  (queryComputes w).outputBound.length_le a

theorem query_primitive_bound (a : α) :
    primitiveCost (queryComputes w).machine ((queryComputes w).outputs a).steps
      (some (initList (queryComputes w).machine.computer (ea.encode a))) ≤
        (primitivePolynomial (queryComputes w)).eval (ea.encode a).length :=
  computes_primitive_cost (queryComputes w) a

/-- Storage at every actual query-compiler «prefix», measured in original input
bits. The bound follows from pushes in its real finite program. -/
theorem query_prefix_bits (a : α) (j : ℕ)
    (hj : j ≤ ((queryComputes w).outputs a).steps)
    (c : (queryComputes w).machine.Config)
    (hc : (fun p => p.bind (queryComputes w).machine.computer.step)^[j]
      (some (initList (queryComputes w).machine.computer (ea.encode a))) = some c) :
    stackSize c.stk ≤ (ea.encode a).length +
      (queryComputes w).time.eval (ea.encode a).length *
        (queryComputes w).machine.primitiveBudget := by
  have hs := (queryComputes w).machine.run_size_le
    (initList (queryComputes w).machine.computer (ea.encode a)) c j hc
  rw [Machine.size_init] at hs
  exact hs.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _
    (hj.trans ((queryComputes w).outputs a).steps_le_m)) _)

/-- The natural answer bound includes its real binary encoding. -/
theorem answer_length_bound (a : α) :
    (encodingNatBool.encode (f a)).length ≤
      (OracleOneQuery.answerBound (queryComputes w) CircuitInstance.outputBound).eval
        (ea.encode a).length := by
  rw [← query_value w a]
  exact OracleOneQuery.answer_length_le (queryComputes w) CircuitInstance.outputBound a

/-- The existing physical query, answer-copy program and proved answer bound
produce the actual oracle machine. No hardness or reduction is an input. -/
def reduction : PolyTimeOracleReduction ea encodingNatBool
    CircuitInstance.encoding encodingNatBool f CircuitInstance.value :=
  VerifierCircuit.Stateful.CapacityFrontend.Exactness.reduction w

end Witness

/-- Universal hardness for precisely the project's represented witness class.
The conventional #P machine-presentation bridge remains separate. -/
theorem circuit_counting_hard :
    ∀ (α : Type) (ea : Encoding α Bool) (f : α → ℕ),
      ∀ w : SharpPWitness ea f,
        Nonempty (PolyTimeOracleReduction ea encodingNatBool
          CircuitInstance.encoding encodingNatBool f CircuitInstance.value) := by
  intro α ea f w
  exact ⟨reduction w⟩

end Holant.LocalDrafts.RemoteWork.CountingBridge.VerifierCircuit.Source
