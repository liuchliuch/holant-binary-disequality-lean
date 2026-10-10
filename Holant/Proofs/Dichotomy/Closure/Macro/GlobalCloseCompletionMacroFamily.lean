import Holant.Proofs.Dichotomy.Closure.E.GlobalCloseCompletionEOSelection
import Holant.Proofs.Hardness.GeneralEOPureFamilyAccess
import Holant.Proofs.Hardness.GeneralEOPinnedDescentAccess

/-! A whole finite family of actual current-palette graph templates has one
joint controlled programme to the frozen original problem. No independent
single-row source or separately chosen holographic basis is substituted. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMacroFamily
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace A
export GeneralEOPureFamilyAccess (arity family source)
end A
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 16384
set_option maxHeartbeats 1200000
set_option Elab.async false
variable {s t : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
variable (T : ℕ → Template) (valid : ∀k<t,(T k).WellFormed P.count 1 P.arity)
abbrev family := A.family (mapped G P) T valid

/-- One replacement query compiles the complete fixed template family. The
macro coefficient field is genuinely retracted, then the existing palette
programme is inlined into the untouched original input and answer codecs. -/
def source : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (A.arity T))
    (O.originalPresentation (family G P T valid)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a))
    (OriginalForestSource.presentation G).encoding
    (O.originalValue (family G P T valid)) (OriginalForestSource.value G) :=
  Programme.compose (Programme.compose (A.source (mapped G P) T valid)
    (OriginalLCodec.fromCoefficient (StableHigherCurrentPurePinsCore.embedding G) P.table))
    P.toOriginal.controlled

/-- The family entry is the tensor of its literal serialized network. -/
theorem family_exact (i : Fin t) : family G P T valid i=
    ((T i.val).network (valid i.val i.isLt) (mapped G P)
      (fun _ : Fin 1=>Signature.disequality)).denote := rfl

section Graph
variable {n : ℕ} (N : Network AlgebraicComplex n)
variable (uses : ∀v,∃j : Fin P.count,
  (⟨P.arity j.val,mapped G P j⟩ : AnySignature AlgebraicComplex)=⟨N.shape.arity v,N.vertex v⟩)

def labels : Labelling N.shape P.count 1 P.arity where
  vertex v := (uses v).choose
  vertex_arity v := congrArg Sigma.fst (uses v).choose_spec
  edge _ := 0

theorem labels_exact : LabelledNetwork.Exact (mapped G P) N (labels G P N uses) :=
  fun v=>(uses v).choose_spec

/-- No new free label is introduced by serializing the chosen actual graph. -/
theorem template_denote (native : ∀e,N.edge e=Signature.disequality) :
    ((labels G P N uses).template.network (labels G P N uses).wellFormed
      (mapped G P) (fun _ : Fin 1=>Signature.disequality)).denote=N.denote :=
  GeneralEOPinnedDescentAccess.template_denote (mapped G P) N (labels G P N uses)
    (labels_exact G P N uses) native
end Graph
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionMacroFamily
end
