import Holant.Proofs.Closure.FrontierCurrentClosure
import Holant.Proofs.Algorithms.TractXCoreSource
import Holant.Proofs.Algorithms.ReductionToFP
import Holant.Proofs.Recognition.InstalledResources

/-! Install the implemented native-X evaluator on an actual StableClosureV2
palette, convert its answer to the original coefficient field, and inline it
through the SAME returned fromOriginal programme. The explicit forward-K TractX
premise is unchanged; no solver or oracle backend is supplied by the caller. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StablePaletteTractability
open Computability Holant Holant.Algebraic Holant.Tractable Holant.Complexity
open BinaryCompose FixedFieldMachines
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.StableClosureV2.CurrentFrontierClosure
namespace Original
export Holant.LocalDrafts.Hardness.OriginalFrozenForest.OriginalInput (embedding)
end Original
namespace Target
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalValue target_exact)
end Target
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G

abbrev mapped (P : Palette G) := OriginalLCodec.mapped (Original.embedding G) P.table

theorem mapped_member (P : Palette G) (i : Fin P.count) :
    (⟨P.arity i.val,mapped G P i⟩ : AnySignature AlgebraicComplex) ∈ currentFamily G P :=
  ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩

/-- The existing four-branch implementation uses the native disequality edge
and the exact forward K image supplied by the structural engine. -/
def nativeComputes (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P))) :
    Computes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
      (OriginalFamily.presentation (mapped G P) KSourceTransport.nativeEdges).encoding
      (OriginalFamily.value (mapped G P) KSourceTransport.nativeEdges) :=
  TractXCoreSource.nativeComputesOfKTractX (mapped G P) (currentFamily G P)
    (mapped_member G P) (currentFamily_finite G P) h

/-- The embedded vertex-only answer codec differs from the vertex-plus-edge
codec of the evaluator. The real rational conversion runs on the same graph. -/
def coefficientComputes (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P))) :
    Computes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
      (Target.originalPresentation (mapped G P)).encoding
      (Target.originalValue (mapped G P)) := by
  let convert := FamilyAnswerTransport.computes (Target.coefficients (mapped G P))
    (OriginalFamily.coefficient (mapped G P) KSourceTransport.nativeEdges)
    (Target.coefficients_algebraic (mapped G P))
    (OriginalFamily.coefficient_algebraic (mapped G P) KSourceTransport.nativeEdges)
  apply congrComputes ((nativeComputes G P h).andThen convert)
  intro r
  apply FamilyAnswerTransport.recover_exact
  rw [OriginalFamily.value_exact,Target.target_exact]

/-- Full answer recovery into the ORIGINAL OI.K G presentation. This is a
physical composition of the implemented evaluator and original-field codec. -/
def currentComputes (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P))) :
    Computes (RawClosedNetwork.validatedEncoding P.count 1 P.arity)
      (OI.presentation G).encoding (OriginalLCodec.value P.table) :=
  ReductionToFP.computes (OriginalLCodec.toCoefficient (Original.embedding G) P.table)
    (coefficientComputes G P h)

/-- Original literal G+X with equality edges, exactly the engine's original
source bytes and answer codec. All oracle calls are physically eliminated. -/
def originalComputes (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P))) :
    Computes (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) :=
  ReductionToFP.computes P.fromOriginal.controlled (currentComputes G P h)

theorem original_inFP (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P))) :
    InFP (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
      (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) :=
  (originalComputes G P h).inFP

theorem original_resources (P : Palette G)
    (h : TractX (familyAction sourceKBasis (currentFamily G P)))
    (r : EdgeSubdivision.WireEquivalence.Input s a) :
    Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources.Contract
      (originalComputes G P h) r :=
  Holant.LocalDrafts.RemoteWork.TractChainV1.InstalledResources.receipt _ _

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StablePaletteTractability
end
