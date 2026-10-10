import Holant.Proofs.BinaryInterpolation.EffectiveRecognition.RationalInputMachine.Resources
import Holant.Proofs.Algorithms.TransformRecognition.CertificateSearchSource
import Holant.Proofs.Algorithms.TransformRecognition.OriginalSystemDecision


namespace Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemMachine
open Turing Computability Holant.Tractable Holant.Algebraic Holant.Complexity
open FixedFieldMachines
open Holant.LocalDrafts.EffectiveAlgebraic
open Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
variable {m q : ℕ}

noncomputable def machine : BinaryCompose.Machine :=
  RationalInputMachine.Compiler.executes.machine.compose CertificateSearchLoop.machine

/-- The transition bound is derived from the actual two runs and charges the
intermediate request transfer. It is not a runtime fuel parameter. -/
theorem source_outputs (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Sparse.Poly (5+q) 1)) (address : Fin m → Fin (5+q)) :
    ∃ bound, Nonempty (TM2OutputsInTime machine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address))
      (some (encodingBoolBool.encode (OriginalSystemDecision.answer input hv S address))) bound) := by
  obtain ⟨searchBound,⟨searchRun⟩⟩ := CertificateSearchSource.outputs
    (RationalInputSystem.target input S) (OriginalSystemDecision.oneSlot S)
    (OriginalSystemDecision.negSlot S) (RationalInputSystem.system S address)
    (OriginalSystemDecision.target_valid input hv S)
  let r := RationalInputMachine.fromSource input S address
  have compileRun := RationalInputMachine.Compiler.executes.outputs r
  have searchRun' : TM2OutputsInTime CertificateSearchLoop.machine.computer
      (NegativeCatalogueMachine.encoding.encode (RationalInputMachine.request r))
      (some (encodingBoolBool.encode (OriginalSystemDecision.answer input hv S address)))
      searchBound := by
    dsimp only [r]
    rw [RationalInputMachine.request_fromSource]
    exact searchRun
  exact ⟨_,⟨BinaryCompose.Machine.compose_correct _ _ _ _ _ _ _ compileRun searchRun'⟩⟩

/-- Correctness refers to the original independently specified conjugates and
the literal rational body. Guard membership is a syntactic property of the
compiler output, not an assumed matrix or a system solution. -/
theorem source_correct (input : Fin m → RootCode)
    (w : Fin m → AlgebraicComplex) (hw : ∀ i, (input i).Represents (w i : ℂ))
    (S : List (Sparse.Poly (5+q) 1)) (address : Fin m → Fin (5+q))
    (hg : SparseTransform.guard RationalCompiler.data q ∈ S) :
    ∃ b bound, Nonempty (TM2OutputsInTime machine.computer
      (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address))
      (some (encodingBoolBool.encode b)) bound) ∧
      (b=true ↔ ∃ z : Fin (5+q) → ℂ,
        (∀ i, z (address i)=(w i : ℂ)) ∧
        ∀ p ∈ S, SparseEvaluation.evaluate RationalCompiler.field (algebraMap ℚ ℂ) z p=0) := by
  let hv : OriginalSystemDecision.Valid input := ⟨w,hw⟩
  obtain ⟨bound,run⟩ := source_outputs input hv S address
  refine ⟨_,bound,run,?_⟩
  rw [OriginalSystemDecision.answer_correct input hv w hw S address hg]
  exact exists_congr (fun z => RationalInputSystem.system_zero_iff _ S address z)

/-- Physical steps and primitive instructions belong to this same composed
machine. There is no replacement evaluator hidden in the resource statement. -/
theorem complete_run (input : Fin m → RootCode) (hv : OriginalSystemDecision.Valid input)
    (S : List (Sparse.Poly (5+q) 1)) (address : Fin m → Fin (5+q)) :
    ∃ ticks bound,
      (fun p => p.bind machine.computer.step)^[ticks]
        (some (initList machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address)))) =
        some (haltList machine.computer
          (encodingBoolBool.encode (OriginalSystemDecision.answer input hv S address))) ∧
      ticks ≤ bound ∧
      primitiveCost machine ticks
        (some (initList machine.computer
          (RationalInputMachine.encoding.encode (RationalInputMachine.fromSource input S address)))) ≤
        bound*machine.primitiveBudget := by
  obtain ⟨bound,⟨run⟩⟩ := source_outputs input hv S address
  exact ⟨run.steps,bound,run.evals_in_steps,run.steps_le_m,
    (primitiveCost_le _ _ _).trans (Nat.mul_le_mul_right _ run.steps_le_m)⟩

end Holant.LocalDrafts.MainChain.TransformRecognition.OriginalSystemMachine
