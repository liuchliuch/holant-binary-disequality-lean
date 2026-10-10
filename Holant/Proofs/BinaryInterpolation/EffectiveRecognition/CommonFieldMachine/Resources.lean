import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.FamilyMachine


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Resources
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines

noncomputable def transitions (r : Request) : ℕ := FamilyMachine.executes.cost r
noncomputable def primitives (r : Request) : ℕ :=
  transitions r*FamilyMachine.executes.machine.primitiveBudget
noncomputable def bits (r : Request) : ℕ := (requestEncoding.encode r).length+primitives r

/-- Every reached intermediate tape, including inside nested scalar calls,
is bounded by pushes paid for in the actual complete execution. -/
theorem prefix_bits (r : Request) (k : ℕ)
    (hk : k ≤ (FamilyMachine.executes.outputs r).steps)
    (c : FamilyMachine.executes.machine.Config)
    (hc : (fun p => p.bind FamilyMachine.executes.machine.computer.step)^[k]
      (some (initList FamilyMachine.executes.machine.computer (requestEncoding.encode r))) = some c) :
    stackSize c.stk ≤ bits r := by
  have h := FamilyMachine.executes.machine.run_size_le
    (initList FamilyMachine.executes.machine.computer (requestEncoding.encode r)) c k hc
  rw [Machine.size_init] at h
  have ht : k ≤ transitions r := hk.trans (FamilyMachine.executes.outputs r).steps_le_m
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ ht) (requestEncoding.encode r).length)

theorem complete_run (r : Request) :
    ∃ ticks,
      (fun p => p.bind FamilyMachine.executes.machine.computer.step)^[ticks]
        (some (initList FamilyMachine.executes.machine.computer (requestEncoding.encode r))) =
        some (haltList FamilyMachine.executes.machine.computer (encodingBoolBool.encode (check r))) ∧
      ticks ≤ transitions r ∧
      primitiveCost FamilyMachine.executes.machine ticks
        (some (initList FamilyMachine.executes.machine.computer (requestEncoding.encode r))) ≤ primitives r :=
  ⟨(FamilyMachine.executes.outputs r).steps,
    (FamilyMachine.executes.outputs r).evals_in_steps,
    (FamilyMachine.executes.outputs r).steps_le_m,
    FamilyMachine.primitive_bound r⟩

theorem checked_bytes (r : Request) (h : r.shape=true) :
    checkBits (requestEncoding.encode r) = some (encodingBoolBool.encode (check r)) := by
  simp only [checkBits,decodeRequest_encode h,check,h,Bool.true_and]
  rfl

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.CommonFieldMachine.Resources
