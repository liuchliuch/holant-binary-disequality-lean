import Holant.Proofs.Dichotomy.Main.PaperQuaternaryDecision.RuntimeSevenDecision

/-! Exact third-main-theorem criterion decision on original RootCodes.
One fixed physical programme reads the original varying arity layout and
coefficient descriptors. Forward K is composed into its support, tensor and
EO constraints; no transformed coefficient descriptors are source inputs.
The complete seven-clause output and actual search-dependent costs remain
attached to that same programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecisionSource
open Turing Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain.TransformRecognition
abbrev Data := Holant.LocalDrafts.RemoteWork.TractChainV1.RuntimeSupportTable.Data
def original (d : Data) := OriginalFamilyPackingSource.fromSource d.arity d.input false
def family (d : Data) : SignatureFamily AlgebraicComplex :=
  Set.range (fun i : Fin d.count=>(⟨d.arity i,d.G i⟩ : AnySignature AlgebraicComplex))
def answer (d : Data) : Bool := (PaperQuaternaryDecision.RuntimeSevenPrograms.output d).1

theorem answer_correct (d : Data) : answer d=true ↔ Tract (familyAction sourceKBasis (family d)) := by
  have h:=PaperQuaternaryDecision.RuntimeSevenDecision.output_correct d
  rw [PaperQuaternaryDecision.RuntimeSevenDecision.family,
    PaperQuaternaryDecision.RuntimeSevenCriterionNormalization.family_forward] at h
  simpa only [answer,PaperQuaternaryDecision.RuntimeSevenCriterionNormalization.family,family] using h

theorem answer_false_iff (d : Data) : answer d=false ↔ ¬Tract (familyAction sourceKBasis (family d)) := by
  have hb : ∀b : Bool,b=false↔¬b=true := by intro b;cases b <;> simp
  rw [hb,answer_correct]

theorem uniform_source : ∃M : BinaryCompose.Machine,∀d : Data,
    Nonempty (TM2OutputsInTime M.computer (OriginalFamilyPackingMachine.encoding.encode (original d))
      (some (PaperQuaternaryDecision.RuntimeSevenPrograms.outputEncoding.encode (PaperQuaternaryDecision.RuntimeSevenPrograms.output d))) (PaperQuaternaryDecision.RuntimeSevenPrograms.executes.cost d)) ∧
    (answer d=true↔Tract (familyAction sourceKBasis (family d))) ∧
    (answer d=false↔¬Tract (familyAction sourceKBasis (family d))) :=
  ⟨PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine,fun d=>⟨⟨PaperQuaternaryDecision.RuntimeSevenPrograms.executes.outputs d⟩,answer_correct d,answer_false_iff d⟩⟩

theorem resources (d : Data) :
    primitiveCost PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine (PaperQuaternaryDecision.RuntimeSevenPrograms.executes.outputs d).steps
      (some (initList PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d)))) ≤
      PaperQuaternaryDecision.RuntimeSevenPrograms.executes.cost d*PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.primitiveBudget ∧
    ∀k,k≤(PaperQuaternaryDecision.RuntimeSevenPrograms.executes.outputs d).steps → ∀cfg : PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.Config,
      (fun st=>st.bind PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.computer.step)^[k]
        (some (initList PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.computer (OriginalFamilyPackingMachine.encoding.encode (original d))))=some cfg →
      stackSize cfg.stk ≤ (OriginalFamilyPackingMachine.encoding.encode (original d)).length+
        PaperQuaternaryDecision.RuntimeSevenPrograms.executes.cost d*PaperQuaternaryDecision.RuntimeSevenPrograms.executes.machine.primitiveBudget :=
  PaperQuaternaryDecision.RuntimeSevenDecision.resources d


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.PaperQuaternaryDecisionSource
end
