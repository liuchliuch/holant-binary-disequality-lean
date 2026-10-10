import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine.Stage


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition

noncomputable def generationTransitions (r : Request) : ℕ := Generation.executes.cost r
noncomputable def generationPrimitives (r : Request) : ℕ :=
  generationTransitions r*Generation.executes.machine.primitiveBudget
noncomputable def generationBits (r : Request) : ℕ := (encoding.encode r).length+generationPrimitives r
noncomputable def transitions (r : Request) : ℕ := executes.cost r
noncomputable def primitives (r : Request) : ℕ := transitions r*executes.machine.primitiveBudget
noncomputable def bits (r : Request) : ℕ := (encoding.encode r).length+primitives r

/-- In particular the catalogue-to-checker transfer is not a zero-cost call. -/
theorem transitions_eq (r : Request) :
    transitions r = generationTransitions r +
      2*((catalogueEncoding.encode (catalogue r)).length+1) +
        Traversal.executes.cost (catalogue r) := rfl

theorem generation_complete_run (r : Request) :
    ∃ ticks,
      (fun p => p.bind Generation.executes.machine.computer.step)^[ticks]
        (some (initList Generation.executes.machine.computer (encoding.encode r))) =
        some (haltList Generation.executes.machine.computer (catalogueEncoding.encode (catalogue r))) ∧
      ticks ≤ generationTransitions r ∧
      primitiveCost Generation.executes.machine ticks
        (some (initList Generation.executes.machine.computer (encoding.encode r))) ≤ generationPrimitives r :=
  ⟨(Generation.executes.outputs r).steps,(Generation.executes.outputs r).evals_in_steps,
    (Generation.executes.outputs r).steps_le_m,Generation.executes.primitive_bound r⟩

theorem generation_intermediate_bits (r : Request) (k : ℕ)
    (hk : k ≤ (Generation.executes.outputs r).steps) (c : Generation.executes.machine.Config)
    (hc : (fun p => p.bind Generation.executes.machine.computer.step)^[k]
      (some (initList Generation.executes.machine.computer (encoding.encode r))) = some c) :
    stackSize c.stk ≤ generationBits r := by
  have h := Generation.executes.machine.run_size_le
    (initList Generation.executes.machine.computer (encoding.encode r)) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hk.trans (Generation.executes.outputs r).steps_le_m)) _)

theorem generated_word_length (r : Request) :
    (catalogueEncoding.encode (catalogue r)).length ≤ generationBits r :=
  Generation.executes.output_length r

theorem complete_run (r : Request) :
    ∃ ticks,
      (fun p => p.bind executes.machine.computer.step)^[ticks]
        (some (initList executes.machine.computer (encoding.encode r))) =
        some (haltList executes.machine.computer (encodingBoolBool.encode (stage r))) ∧
      ticks ≤ transitions r ∧
      primitiveCost executes.machine ticks
        (some (initList executes.machine.computer (encoding.encode r))) ≤ primitives r :=
  ⟨(executes.outputs r).steps,(executes.outputs r).evals_in_steps,
    (executes.outputs r).steps_le_m,executes.primitive_bound r⟩

theorem intermediate_bits (r : Request) (k : ℕ) (hk : k ≤ (executes.outputs r).steps)
    (c : executes.machine.Config)
    (hc : (fun p => p.bind executes.machine.computer.step)^[k]
      (some (initList executes.machine.computer (encoding.encode r))) = some c) :
    stackSize c.stk ≤ bits r := by
  have h := executes.machine.run_size_le (initList executes.machine.computer (encoding.encode r)) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hk.trans (executes.outputs r).steps_le_m)) _)

theorem source_complete_run {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    ∃ ticks,
      (fun p => p.bind executes.machine.computer.step)^[ticks]
        (some (initList executes.machine.computer (encoding.encode (fromSource target S h)))) =
        some (haltList executes.machine.computer
          (encodingBoolBool.encode (StructuredDovetail.negative target S h))) ∧
      ticks ≤ transitions (fromSource target S h) ∧
      primitiveCost executes.machine ticks
        (some (initList executes.machine.computer (encoding.encode (fromSource target S h)))) ≤
          primitives (fromSource target S h) := by
  simpa only [stage_eq_central] using complete_run (fromSource target S h)

/-- Decoder roundtrips here describe the canonical endpoint ONLY; decode is
not used to implement the machine. No malformed-raw-word promise is added. -/
theorem source_answer_codec {m k : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m (5+k)) (h : ℕ) :
    encodingBoolBool.decode (encodingBoolBool.encode (stage (fromSource target S h))) =
      some (StructuredDovetail.negative target S h) := by
  rw [encodingBoolBool.decode_encode,stage_eq_central]

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCatalogueMachine
