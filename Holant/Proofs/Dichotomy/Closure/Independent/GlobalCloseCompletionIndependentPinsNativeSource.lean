import Holant.Proofs.Dichotomy.Closure.Independent.GlobalCloseCompletionIndependentPinsAlgebra
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPowerOrdinary
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryFieldCodec
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4OrdinaryWire

/-! Retained ordinary Z becomes a literal native equality vertex. The exact
wire-swap compiler then supplies ordinary access to the entire inverse-K
table and a literal X, in its actual generated coefficient field. The two
canonical answer codecs are composed with the unchanged original-G source.
Neither independent unary access nor this wire equivalence is hardness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsNativeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.GeneralExtraction.SupportCaps
namespace O
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalField
  (field presentation original tables value)
end O
namespace W
export GlobalCloseCompletionEq4OrdinaryWire (withX withXControlled)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))

abbrev native := KSourceTransport.nativeSignatures H
abbrev field := O.field (native H)
local instance : Algebra ℚ (field H) := (field H).algebra'
abbrev presentation := O.presentation (native H)
abbrev table := O.original (native H)
abbrev nativeTables := O.tables (native H)
abbrev nativeValue := O.value (native H)
abbrev ordinaryTable := W.withX (table H)
abbrev arity := EdgeSubdivision.targetArity r b
abbrev ordinaryTables := QuaternaryOrdinaryCompanion.tables (presentation H) (ordinaryTable H)

theorem table_value (i : Fin r) (x : Fin (b i.val)→Bool) :
    (table H i x : AlgebraicComplex)=sourceKBasis.symm.action (H i) x := rfl

theorem mapped_literal {n : ℕ} (j : Fin r) (f : Signature AlgebraicComplex n)
    (literal : (⟨b j.val,H j⟩ : AnySignature AlgebraicComplex)=⟨n,f⟩) :
    RingHomRealization.mapAny (field H).subtype (⟨b j.val,table H j⟩ : AnySignature (field H))=
      ⟨n,sourceKBasis.symm.action f⟩ := by
  exact congrArg (fun g : AnySignature AlgebraicComplex=>
    (⟨g.1,sourceKBasis.symm.action g.2⟩ : AnySignature AlgebraicComplex)) literal

theorem mapAny_injective : Function.Injective (RingHomRealization.mapAny (field H).subtype) := by
  rintro ⟨m,f⟩ ⟨n,g⟩ h
  have hn : m=n := congrArg Sigma.fst h
  subst n
  have hf:=eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun f : Signature (field H) m=>(⟨m,f⟩ : AnySignature (field H)))
  funext x
  exact Subtype.ext (congrFun hf x)

variable (z : Fin r) (zLiteral : (⟨b z.val,H z⟩ : AnySignature AlgebraicComplex)=⟨2,zAnchor⟩)

include zLiteral in
theorem identity_literal : (⟨b z.val,table H z⟩ : AnySignature (field H))=
    ⟨2,fun x=>Signature.equality (x 0) (x 1)⟩ := by
  apply mapAny_injective H
  rw [mapped_literal H z zAnchor zLiteral,sourceKBasis_symm_action_zAnchor]
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [kernelSignature,RingHomRealization.mapSignature,Signature.equality,h0,h1]

def nativeControlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) (presentation H).encoding
    (RawClosedNetwork.validatedEncoding r 1 b) (KSourceTransport.originalPresentation H).encoding
    (nativeValue H) (KSourceTransport.originalValue H) :=
  GlobalCloseCompletionUnaryPowerOrdinary.oldOrdinary H

/-- The retained equality label is used at every subdivided edge. The
additional X label is compiled by the two-stage wire swap, including cycles. -/
def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+1) 1 (arity (r:=r) (b:=b))) (presentation H).encoding
    (RawClosedNetwork.validatedEncoding r 1 b) (KSourceTransport.originalPresentation H).encoding
    ((ordinaryTables H).evaluate (presentation H)) (KSourceTransport.originalValue H) :=
  Programme.compose (W.withXControlled (presentation H) (table H) z (identity_literal H z zLiteral))
    (nativeControlled H)

def old (_H : (i : Fin r)→Signature AlgebraicComplex (b i.val)) (i : Fin r) : Fin (r+1) := Fin.castAdd 1 i
def xLabel (_H : (i : Fin r)→Signature AlgebraicComplex (b i.val)) : Fin (r+1) := Fin.natAdd r 0

theorem old_literal (i : Fin r) :
    (⟨arity (r:=r) (b:=b) (old H i).val,ordinaryTable H (old H i)⟩ : AnySignature (field H))=
      ⟨b i.val,table H i⟩ :=
  Sigma.ext (by simp [arity,EdgeSubdivision.targetArity,old,i.isLt])
    (EdgeSubdivision.extendedSignatures_old_heq (table H) (fun _ : Fin 1=>Signature.disequality) i)

theorem x_literal :
    (⟨arity (r:=r) (b:=b) (xLabel H).val,ordinaryTable H (xLabel H)⟩ : AnySignature (field H))=
      ⟨2,fun x=>Signature.disequality (x 0) (x 1)⟩ :=
  Sigma.ext (by simp [arity,EdgeSubdivision.targetArity,xLabel])
    (EdgeSubdivision.extendedSignatures_new_heq (table H) (fun _ : Fin 1=>Signature.disequality) (0 : Fin 1))

section Pin
variable (j : Fin r) (u : Signature AlgebraicComplex 1)
variable (literal : (⟨b j.val,H j⟩ : AnySignature AlgebraicComplex)=⟨1,u⟩)
variable (v : Bool) (c : AlgebraicComplex) (axis : sourceKBasis.symm.action u=purePin c v 1)

def scalar : field H := table H j (fun _=>v)

include literal axis in
theorem scalar_value : (scalar H j v : AlgebraicComplex)=c := by
  have h:=mapped_literal H j u literal
  have arityOne:=congrArg Sigma.fst h
  have hv:=BinaryInterpolation.Chains.signature_cast_apply
    (sourceKBasis.symm.action (H j)) (purePin c v 1) (h.trans (congrArg (Sigma.mk 1) axis))
    arityOne (fun _=>v)
  simpa only [scalar,table_value,purePin,ite_true] using hv

include literal axis in
theorem scalar_nonzero (hc : c≠0) : scalar H j v≠0 := by
  intro zero
  apply hc
  rw [←scalar_value H j u literal v c axis,zero]
  rfl

include literal axis in
theorem pin_literal : (⟨b j.val,table H j⟩ : AnySignature (field H))=
    ⟨1,purePin (scalar H j v) v 1⟩ := by
  apply mapAny_injective H
  rw [mapped_literal H j u literal,axis]
  apply congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp only [RingHomRealization.mapSignature,purePin]
  split_ifs
  · exact (scalar_value H j u literal v c axis).symm
  · rfl
end Pin

section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (T : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F T).evaluate F) (OriginalForestSource.value G))
variable (j : Fin r) (hasZ :
    (⟨b j.val,GlobalCloseCompletionUnaryOrdinaryFieldCodec.ambient L T j⟩ : AnySignature AlgebraicComplex)=⟨2,zAnchor⟩)

def toOriginal := Programme.compose
  (controlled (GlobalCloseCompletionUnaryOrdinaryFieldCodec.ambient L T) j hasZ)
  (Programme.compose (GlobalCloseCompletionUnaryOrdinaryFieldCodec.controlled L F T) back)

end Original


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIndependentPinsNativeSource
end
