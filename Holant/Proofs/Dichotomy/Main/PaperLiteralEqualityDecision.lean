import Holant.Proofs.Dichotomy.Main.PaperLiteralEquality
import Holant.Proofs.Recognition.RuntimeFourDecision

/-! The exact native supplied-I theorem has one uniform terminating
criterion programme on varying original layouts and algebraic RootCodes.
The programme reads G itself, and decides precisely TractX(KG). -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityDecision
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain.TransformRecognition
open Holant.LocalDrafts.EffectiveAlgebraic Holant.LocalDrafts.BinaryInterpolation.EffectiveRecognition
open Holant.LocalDrafts.RemoteWork.TractChainV1
namespace R
export RuntimeFourDecision (output outputEncoding executes source_outputs native_correct)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
attribute [local irreducible] RuntimeFourDecision.executes
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
abbrev answer : Bool := (R.output (data G input represented)).1.2

theorem correct : answer G input represented=true ↔ PaperLiteralEquality.Criterion G :=
  R.native_correct (data G input represented)

theorem false_iff : answer G input represented=false ↔ ¬PaperLiteralEquality.Criterion G :=
  RuntimeFourDecision.native_false_iff (data G input represented)

theorem uniform : ∃M : BinaryCompose.Machine,
    ∀(s : ℕ) (a : ℕ→ℕ) (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
      (input : OriginalFamilyInput.Input (fun i : Fin s=>a i.val))
      (represented : ∀i x,(input i x).Represents (G i x : ℂ)),
      Nonempty (TM2OutputsInTime M.computer
        (OriginalFamilyPackingMachine.encoding.encode (RuntimeTensorAggregation.original (data G input represented)))
        (some (R.outputEncoding.encode (R.output (data G input represented))))
        (R.executes.cost (data G input represented))) ∧
      (answer G input represented=true ↔ PaperLiteralEquality.Criterion G) := by
  refine ⟨R.executes.machine,?_⟩
  intro s a G input represented
  exact ⟨⟨R.source_outputs (data G input represented)⟩,correct G input represented⟩

theorem positive (accepted : answer G input represented=true) :
    InFP (PaperLiteralEquality.inputEncoding (s:=s) (a:=a))
      (PaperLiteralEquality.presentation G).encoding (PaperLiteralEquality.value G) :=
  PaperLiteralEquality.positive G ((correct G input represented).mp accepted)

theorem negative (j : Fin s)
    (literal : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex)=⟨2,kernelSignature Signature.equality⟩)
    (rejected : answer G input represented=false) : PaperLiteralEquality.Hard G :=
  PaperLiteralEquality.negative G j literal ((false_iff G input represented).mp rejected)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperLiteralEqualityDecision
end
