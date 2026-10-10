import Holant.Proofs.Dichotomy.Native.NativeAntiTargetSource
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryNativeSource

/-! Exact native-X table/answer conversion from an existing fixed subfield
presentation to the canonical algebraic family presentation. The graph bytes
are unchanged and the fixed rational retraction is an actual program. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeTableFieldCodec
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 800000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r degree : ℕ} {b : ℕ→ℕ}
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (H : (i : Fin r)→Signature L (b i.val))

def ambient (i : Fin r) : Signature AlgebraicComplex (b i.val) := fun x=>(H i x : AlgebraicComplex)
abbrev coefficients := OriginalFamily.coefficient (ambient L H) KSourceTransport.nativeEdges
abbrev field := familyField (coefficients L H)
abbrev presentation := OriginalFamily.presentation (ambient L H) KSourceTransport.nativeEdges
abbrev value := OriginalFamily.value (ambient L H) KSourceTransport.nativeEdges
abbrev inputEncoding := RawClosedNetwork.validatedEncoding r 1 b

theorem field_le : field L H≤L := by
  apply IntermediateField.adjoin_le_iff.mpr
  rintro z ⟨i,rfl⟩
  rcases i with ⟨i,x⟩|⟨i,p,q⟩
  · exact (H i x).property
  · cases p <;> cases q <;>
      simp [coefficients,OriginalFamily.coefficient,KSourceTransport.nativeEdges,Signature.disequality]

def embedding : field L H→ₐ[ℚ]L := IntermediateField.inclusion (field_le L H)

theorem mapped_value (q : ExactSignatureTables.Input r 1 b) :
    (NativeAntiTargetSource.base H F).evaluate F q=embedding L H (value L H q) := by
  apply Subtype.ext
  change (((NativeAntiTargetSource.base H F).evaluate F q : L) : AlgebraicComplex)=(value L H q : AlgebraicComplex)
  rw [OriginalFamily.value_exact,ExactSignatureTables.evaluate_eq_decoded]
  change L.subtype _=_
  rw [←Network.denote_map]
  congr 1
  unfold Network.map RawClosedNetwork.realize
  congr 1
  · funext v x
    simp only [NativeAntiTargetSource.base,LinearEquiv.apply_symm_apply]
    rfl
  · funext e p q
    simp only [NativeAntiTargetSource.base,LinearEquiv.apply_symm_apply]
    cases p <;> cases q <;> rfl

def recover : Computes F.encoding (presentation L H).encoding (embedding L H).toLinearMap.leftInverse :=
  FieldCodec.retractComputes (presentation L H) F (embedding L H)

def controlled : LengthControlledOracleReduction
    (inputEncoding (r:=r) (b:=b)) (presentation L H).encoding
    (inputEncoding (r:=r) (b:=b)) F.encoding
    (value L H) ((NativeAntiTargetSource.base H F).evaluate F) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (b:=b))) (recover L F H)
    ((NativeAntiTargetSource.base H F).outputBound F) (value L H) (fun q=>by
      rw [mapped_value,FieldCodec.retract_embedding];rfl)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeTableFieldCodec
end
