import Holant.Proofs.Dichotomy.Main.PaperBinaryDisequality
import Holant.Proofs.Recognition.RuntimeAugmentedNativeDecision

/-! One actual uniform programme decides the first main theorem's exact
criterion from original algebraic RootCodes and the varying arity layout.
Its represented input is precisely the same indexed family as the complexity
statement. No recognition oracle or polynomial-time decision claim is added. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperBinaryDisequalityDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
namespace R
export RuntimeAugmentedNativeDecision (answer output outputEncoding executes source_outputs answer_correct)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
attribute [local irreducible] RuntimeAugmentedNativeDecision.executes
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (input : OriginalFamilyInput.Input (fun i : Fin s=>a i.val))
variable (represented : ∀i x,(input i x).Represents (G i x : ℂ))

def data : RuntimeTensorAggregation.Data where
  count:=s
  arity i:=a i.val
  G:=G
  input:=input
  represented:=represented
  native:=false
  opposite:=false

theorem correct : R.answer (data G input represented)=true ↔ PaperBinaryDisequality.Criterion G :=
  R.answer_correct (data G input represented)

/-- The machine is fixed independently of the layout, coefficients, and their
represented mathematical family. -/
theorem uniform : ∃M : BinaryCompose.Machine,
    ∀(s : ℕ) (a : ℕ→ℕ) (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s=>a i.val))
      (represented : ∀i x,(input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode (RuntimeTensorAggregation.original (data G input represented)))
        (some (R.outputEncoding.encode (R.output (data G input represented))))
        (R.executes.cost (data G input represented))) ∧
      (R.answer (data G input represented)=true ↔ PaperBinaryDisequality.Criterion G) := by
  obtain ⟨M,hM⟩:=RuntimeAugmentedNativeDecision.uniform_source
  refine ⟨M,?_⟩
  intro s a G input represented
  exact ⟨(hM (data G input represented)).1,correct G input represented⟩


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperBinaryDisequalityDecision
end
