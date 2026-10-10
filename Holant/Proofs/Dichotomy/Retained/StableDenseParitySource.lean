import Holant.Proofs.Dichotomy.Retained.StableDenseParityMap
import Holant.Proofs.Dichotomy.Retained.StableCurrentEvenEOHardness
import Holant.Proofs.Hardness.EightVertexCapSource

/-! The accepted explicit eight-vertex sources are connected to an actual
current-palette graph and its saved original-G programme. Each independently
presented coefficient field is crossed by a real rational-linear answer
programme; no generated and original codecs are identified. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParitySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.Hardness
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace C
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field presentation targetEncoding targetValue)
end O

variable {K L : Type} [Field K] [Field L]
def Covered (M : Signature K 4) : Prop :=
  EightVertexCancellationLocal.Applicable M ∨ EightVertexCapLocal.Applicable M

theorem covered_map (φ : K →+* L) (M : Signature K 4) (h : Covered M) :
    Covered (StableDenseParityMap.mapped φ M) :=
  h.elim (fun h => Or.inl (StableDenseParityMap.cancellation φ M h))
    (fun h => Or.inr (StableDenseParityMap.cap φ M h))

/-- Numerical tests only; actual cap choice ranges over twelve original loops. -/
def Region (M : Signature K 4) : Prop := StableDenseParityAlgebra.Region M ∨
  ∃ k : GeneralCancellationCapPin.Choice, StableDenseParityAlgebra.CapRegion M k

theorem covered_of_region (M : Signature K 4)
    (he : EightVertexNonexception.EvenSupport M) (hd : StableDenseParityAlgebra.Dense M)
    (h : Region M) : Covered M := by
  rcases h with direct | ⟨k,cap⟩
  · exact Or.inl ((StableDenseParityAlgebra.applicable_iff M he hd).mpr direct)
  · exact Or.inr (StableDenseParityAlgebra.cap_applicable M he hd k cap)

variable (M : Signature AlgebraicComplex 4) (covered : Covered M)
abbrev complexMap : AlgebraicComplex →ₐ[ℚ] ℂ := (algebraicClosure ℚ ℂ).val
theorem algebraic : ∀ x, IsAlgebraic ℚ (M x) := fun _ => Algebra.IsAlgebraic.isAlgebraic _
local instance originalAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance complexAlgebra : Algebra ℚ (O.field (SignatureFieldMap.mapped M complexMap)) :=
  (O.field (SignatureFieldMap.mapped M complexMap)).algebra'
variable {α : Type} {ea : Encoding α Bool} {f : α → ℕ}

def singletonSource (w : SharpPWitness ea f) : LengthControlledOracleReduction
    ea encodingNatBool O.targetEncoding (O.presentation M (algebraic M)).encoding
    f (O.targetValue M (algebraic M)) := by
  classical
  have mapped := covered_map complexMap.toRingHom M covered
  by_cases direct : EightVertexCancellationLocal.Applicable
      (StableDenseParityMap.mapped complexMap.toRingHom M)
  · exact C.composeControlled
      (EightVertexCancellationSource.source (SignatureFieldMap.mapped M complexMap)
        (SignatureFieldMap.mapped_algebraic M (algebraic M) complexMap) direct w)
      (SignatureFieldMap.controlled M (algebraic M) complexMap)
  · exact C.composeControlled
      (EightVertexCapSource.source (SignatureFieldMap.mapped M complexMap)
        (SignatureFieldMap.mapped_algebraic M (algebraic M) complexMap) (mapped.resolve_left direct) w)
      (SignatureFieldMap.controlled M (algebraic M) complexMap)

namespace Family
namespace T
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalValue)
end T
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (j : Fin s)
variable (hj : (⟨a j.val,G j⟩ : AnySignature AlgebraicComplex) = ⟨4,M⟩)
local instance targetAlgebra : Algebra ℚ (T.originalField G) := (T.originalField G).algebra'

def source (w : SharpPWitness ea f) : LengthControlledOracleReduction ea encodingNatBool
    (RawClosedNetwork.validatedEncoding s 1 a) (T.originalPresentation G).encoding
    f (T.originalValue G) :=
  C.composeControlled (singletonSource M covered w) (SelectedOriginalFamily.controlled G M j hj)
end Family

namespace Graph
open StableCurrentEvenEOHardness
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (N : Network AlgebraicComplex 4)
variable (labels : ∀ v, (⟨N.shape.arity v,N.vertex v⟩ : AnySignature AlgebraicComplex) ∈
  ClosurePhysicalBridge.RH.mapFamily (ClosurePhysicalBridge.algebraicEmbedding G) P.family)
variable (d : ClosurePhysicalBridge.NetworkGraphAccess G P
  (ClosurePhysicalBridge.algebraicEmbedding G) N labels)
variable (graphCovered : Covered (mappedOutput G P N labels d))

/-- Select the actual appended row, then decode the ambient family answer
into the fixed original field using its explicit coefficient inclusion. -/
def branchSource (w : SharpPWitness ea f) : LengthControlledOracleReduction
    ea encodingNatBool
    (RawClosedNetwork.validatedEncoding (P.count+1) 1 (RetainedBranch.arity G P ⟨4,d.output⟩))
    (OI.presentation G).encoding f (OriginalLCodec.value (extended G P N labels d)) :=
  C.composeControlled
    (Family.source (mappedOutput G P N labels d) graphCovered
      (mappedExtended G P N labels d) (newLabel G P) (selected G P N labels d) w)
    (OriginalLCodec.fromCoefficient (originalEmbedding G) (extended G P N labels d))

/-- The final programme is the one saved by THIS graph receipt, and its
oracle is precisely the frozen original-G input, answer and value. -/
def source (w : SharpPWitness ea f) : LengthControlledOracleReduction
    ea encodingNatBool (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding f (OriginalForestSource.value G) :=
  C.composeControlled (branchSource G P N labels d graphCovered w) d.toOriginal.controlled

include graphCovered in
theorem witnessCountingHard : Holant.LocalDrafts.CountingHardness.WitnessCountingHard
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding (OriginalForestSource.value G) := by
  intro α ea f w
  exact ⟨(source G P N labels d graphCovered w).reduction⟩

end Graph
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableDenseParitySource
end
