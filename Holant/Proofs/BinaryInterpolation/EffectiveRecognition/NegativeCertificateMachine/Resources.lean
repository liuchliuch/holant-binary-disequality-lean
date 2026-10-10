import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine.Checker


namespace Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic

noncomputable def transitionBound (r : Input) := executes.cost r
noncomputable def primitiveBound (r : Input) := transitionBound r*executes.machine.primitiveBudget
noncomputable def bitBound (r : Input) := (encoding.encode r).length+primitiveBound r

theorem complete_run (r : Input) :
    ∃ ticks,
      (fun p => p.bind executes.machine.computer.step)^[ticks]
        (some (initList executes.machine.computer (encoding.encode r))) =
        some (haltList executes.machine.computer (encodingBoolBool.encode (check r))) ∧
      ticks ≤ transitionBound r ∧
      primitiveCost executes.machine ticks
        (some (initList executes.machine.computer (encoding.encode r))) ≤ primitiveBound r :=
  ⟨(executes.outputs r).steps,(executes.outputs r).evals_in_steps,
    (executes.outputs r).steps_le_m,executes.primitive_bound r⟩

theorem source_complete_run {m n : ℕ} (target : Fin m → RootCode)
    (S : EncodedSystem.System m n) (r : NullstellensatzSearch.Candidate m n S.length) :
    ∃ ticks,
      (fun p => p.bind executes.machine.computer.step)^[ticks]
        (some (initList executes.machine.computer (encoding.encode (fromCandidate target S r)))) =
        some (haltList executes.machine.computer
          (encodingBoolBool.encode (NullstellensatzSearch.check target S r))) ∧
      ticks ≤ transitionBound (fromCandidate target S r) ∧
      primitiveCost executes.machine ticks
        (some (initList executes.machine.computer (encoding.encode (fromCandidate target S r)))) ≤
          primitiveBound (fromCandidate target S r) := by
  simpa only [check_fromCandidate] using complete_run (fromCandidate target S r)

theorem intermediate_bits (r : Input) (k : ℕ) (hk : k ≤ (executes.outputs r).steps)
    (c : executes.machine.Config)
    (hc : (fun p => p.bind executes.machine.computer.step)^[k]
      (some (initList executes.machine.computer (encoding.encode r))) = some c) :
    stackSize c.stk ≤ bitBound r := by
  have h := executes.machine.run_size_le (initList executes.machine.computer (encoding.encode r)) c k hc
  rw [Machine.size_init] at h
  exact h.trans (Nat.add_le_add_left
    (Nat.mul_le_mul_right _ (hk.trans (executes.outputs r).steps_le_m)) _)

theorem reject_shape (r : Input) (h : r.shape=false) : check r=false := by simp [check,h]
theorem reject_box (r : Input)
    (h : r.field.box≠RationalBox.ofRectangle r.certificate.rectangle) : check r=false := by
  simp [check,h]

theorem accepted_decoding_sound {m n : ℕ} (target : Fin m → RootCode) (w : Fin m → ℂ)
    (ht : ∀ i,(target i).Represents (w i)) (S : EncodedSystem.System m n)
    (r : NullstellensatzSearch.Candidate m n S.length)
    (h : encodingBoolBool.decode (encodingBoolBool.encode (check (fromCandidate target S r)))=some true) :
    ¬ ∃ x : Fin n → ℂ, ∀ e∈S, MvPolynomial.aeval x (EncodedSystem.polynomial w e)=0 := by
  rw [encodingBoolBool.decode_encode] at h
  exact source_accept_sound target w ht S r (Option.some.inj h)

end Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition.NegativeCertificateMachine
