import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineBodySource
import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemMachine
import Holant.Proofs.Algorithms.TransformRecognition.OriginalAffineDecision


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineBranchMachine
open Turing Computability Holant.Algebraic Holant.Complexity BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open CommonFieldMachine (Executes)

abbrev Input := List RootCode × (List ℕ × RationalAffineBodyMachine.Input)
abbrev tailEncoding := pairEncoding RationalInputMachine.addressesEncoding RationalAffineBodyMachine.encoding
abbrev encoding := pairEncoding CommonFieldMachine.rootsEncoding tailEncoding

def request (r : Input) : RationalInputMachine.Input :=
  ⟨r.2.2.1,r.1,RationalAffineBodyMachine.body r.2.2,r.2.1⟩

noncomputable def compile : Executes encoding RationalInputMachine.encoding request := by
  let roots := Wiring.firstComputes CommonFieldMachine.rootsEncoding tailEncoding
  let tail := Wiring.secondComputes CommonFieldMachine.rootsEncoding tailEncoding
  let addresses := tail.andThen (Wiring.firstComputes RationalInputMachine.addressesEncoding RationalAffineBodyMachine.encoding)
  let bodyInput := tail.andThen (Wiring.secondComputes RationalInputMachine.addressesEncoding RationalAffineBodyMachine.encoding)
  let width := bodyInput.andThen RationalAffineBodyMachine.width
  let body := (Executes.ofComputes bodyInput).comp RationalAffineBodyMachine.executes
  let wire := (Executes.ofComputes width).pair ((Executes.ofComputes roots).pair
    (body.pair (Executes.ofComputes addresses)))
  exact Executes.recode wire id (fun _ => rfl) (fun _ => rfl)

noncomputable def machine := compile.machine.compose OriginalSystemMachine.machine

variable {s : ℕ} (arity : Fin s → ℕ)
noncomputable def fromSource (input : OriginalAffineSystem.Input arity)
    (B : AffineBranch.Branch arity) : Input :=
  (List.ofFn (OriginalVariableLayout.descriptors input),
    List.ofFn (fun i => (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) (s+1) i).val),
    OriginalAffineBodySource.encode arity B)

theorem request_fromSource (input : OriginalAffineSystem.Input arity) (B : AffineBranch.Branch arity) :
    request (fromSource arity input B) = RationalInputMachine.fromSource
      (OriginalVariableLayout.descriptors input) (OriginalAffineSystem.body arity B)
      (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) (s+1)) := by
  unfold request fromSource
  rw [OriginalAffineBodySource.body_exact]
  rfl

theorem descriptors_valid (input : OriginalAffineSystem.Input arity)
    (hv : OriginalAffineDecision.InputValid arity input) :
    OriginalSystemDecision.Valid (OriginalVariableLayout.descriptors input) := by
  obtain ⟨w,hw⟩ := hv
  refine ⟨OriginalAffineDecision.originalValues arity w,?_⟩
  have h := OriginalVariableLayout.descriptors_represents input (fun i => (w i : ℂ)) hw
  rw [←OriginalAffineDecision.originalValues_coe arity w] at h
  exact h

theorem source_outputs (input : OriginalAffineSystem.Input arity)
    (hv : OriginalAffineDecision.InputValid arity input) (B : AffineBranch.Branch arity) :
    ∃ bound, Nonempty (TM2OutputsInTime machine.computer
      (encoding.encode (fromSource arity input B))
      (some (encodingBoolBool.encode (OriginalSystemDecision.answer
        (OriginalVariableLayout.descriptors input) (descriptors_valid arity input hv)
        (OriginalAffineSystem.body arity B)
        (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) (s+1))))) bound) := by
  obtain ⟨bound,⟨run⟩⟩ := OriginalSystemMachine.source_outputs
    (OriginalVariableLayout.descriptors input) (descriptors_valid arity input hv)
    (OriginalAffineSystem.body arity B)
    (OriginalVariableLayout.binding (OriginalAffineSystem.Entries arity) (s+1))
  have prepared := compile.outputs (fromSource arity input B)
  rw [request_fromSource] at prepared
  exact ⟨_,⟨Machine.compose_correct _ _ _ _ _ _ _ prepared run⟩⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalAffineBranchMachine
