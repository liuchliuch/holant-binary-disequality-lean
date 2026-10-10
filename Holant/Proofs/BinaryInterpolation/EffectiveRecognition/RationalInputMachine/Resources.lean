import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Correspondence


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.MainChain.TransformRecognition

noncomputable def transitions (r : Input) : ℕ := Compiler.executes.cost r
noncomputable def primitives (r : Input) : ℕ := transitions r*Compiler.executes.machine.primitiveBudget
noncomputable def bits (r : Input) : ℕ := (encoding.encode r).length+primitives r

noncomputable def source_outputs {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    TM2OutputsInTime Compiler.executes.machine.computer
      (encoding.encode (fromSource original S address))
      (some (NegativeCatalogueMachine.encoding.encode
        (NegativeCatalogueMachine.fromSource (RationalInputSystem.target original S)
          (EncodedGuard.augment (oneSlot (m:=m) S) (negSlot (m:=m) S)
            (RationalInputSystem.system S address)) 0)))
      (transitions (fromSource original S address)) := by
  have h := Compiler.executes.outputs (fromSource original S address)
  rw [request_fromSource] at h
  exact h

theorem complete_run (r : Input) :
    ∃ ticks,
      (fun p => p.bind Compiler.executes.machine.computer.step)^[ticks]
        (some (initList Compiler.executes.machine.computer (encoding.encode r))) =
        some (haltList Compiler.executes.machine.computer (NegativeCatalogueMachine.encoding.encode (request r))) ∧
      ticks ≤ transitions r ∧
      primitiveCost Compiler.executes.machine ticks
        (some (initList Compiler.executes.machine.computer (encoding.encode r))) ≤ primitives r :=
  ⟨(Compiler.executes.outputs r).steps,(Compiler.executes.outputs r).evals_in_steps,
    (Compiler.executes.outputs r).steps_le_m,Compiler.executes.primitive_bound r⟩

theorem source_complete_run {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    ∃ ticks,
      (fun p => p.bind Compiler.executes.machine.computer.step)^[ticks]
        (some (initList Compiler.executes.machine.computer (encoding.encode (fromSource original S address)))) =
        some (haltList Compiler.executes.machine.computer (NegativeCatalogueMachine.encoding.encode
          (NegativeCatalogueMachine.fromSource (RationalInputSystem.target original S)
            (EncodedGuard.augment (oneSlot (m:=m) S) (negSlot (m:=m) S)
              (RationalInputSystem.system S address)) 0))) ∧
      ticks ≤ transitions (fromSource original S address) ∧
      primitiveCost Compiler.executes.machine ticks
        (some (initList Compiler.executes.machine.computer (encoding.encode (fromSource original S address)))) ≤
          primitives (fromSource original S address) := by
  simpa only [request_fromSource] using complete_run (fromSource original S address)

theorem intermediate_bits (r : Input) (k : ℕ) (hk : k ≤ (Compiler.executes.outputs r).steps)
    (c : Compiler.executes.machine.Config)
    (hc : (fun p => p.bind Compiler.executes.machine.computer.step)^[k]
      (some (initList Compiler.executes.machine.computer (encoding.encode r)))=some c) :
    stackSize c.stk ≤ bits r := by
  have h := Compiler.executes.machine.run_size_le
    (initList Compiler.executes.machine.computer (encoding.encode r)) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hk.trans (Compiler.executes.outputs r).steps_le_m)) _)

theorem output_length (r : Input) :
    (NegativeCatalogueMachine.encoding.encode (request r)).length ≤ bits r :=
  Compiler.executes.output_length r

theorem source_roundtrip {m k : ℕ} (original : Fin m → RootCode)
    (S : List (Sparse.Poly (5+k) 1)) (address : Fin m → Fin (5+k)) :
    encoding.decode (encoding.encode (fromSource original S address))=some (fromSource original S address) :=
  encoding.decode_encode _

theorem emitted_one_slot {m n : ℕ} (S : List (Sparse.Poly n 1)) : (oneSlot (m:=m) S).val=m := by
  simp [oneSlot,SparseCoefficientInput.oneIndex]
theorem emitted_negative_slot {m n : ℕ} (S : List (Sparse.Poly n 1)) : (negSlot (m:=m) S).val=m+1 := rfl

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.RationalInputMachine
