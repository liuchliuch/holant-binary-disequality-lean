import Holant.Proofs.Dichotomy.WithoutIdentity.NoIOrdinaryRaw.GenericOrdinarySource
import Holant.Proofs.Dichotomy.Closure.Generic.GlobalCloseCompletionGenericOrdinaryData

/-! Exact ordinary Eq4/two-pin access from a native equality anchor, ending
at an explicit oracle target. The native self-target contains exactly H and
disequality edges; no identity label is appended. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.AnchorSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryCompose
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace D
export GlobalCloseCompletionGenericOrdinaryData (field presentation arity table internalSource)
end D
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (paletteControlled palette_original palette_first_pin palette_second_pin palette_ambient)
end Pins
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalField originalPresentation originalTables originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (T : NoIOrdinaryRaw.Target)
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family H))
variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) (O.originalPresentation H).encoding
  T.inputEncoding T.outputEncoding (O.originalValue H) T.value)

def build : NoIOrdinaryRaw.GenericOrdinarySource.Data T where
  K:=D.field H A
  degree:=_
  F:=D.presentation H A
  size:=r+3
  b:=D.arity H A
  H:=D.table H A
  e:=⟨r,by omega⟩
  p v:=if v then ⟨r+2,by omega⟩ else ⟨r+1,by omega⟩
  he:=(Pins.palette_original H A (QuaternaryOrdinaryCompanion.eq4Index (s:=r))).trans
    (QuaternaryOrdinaryCompanion.decoded_eq4 H A)
  hp v:=by
    cases v
    · exact Pins.palette_first_pin H A
    · exact Pins.palette_second_pin H A
  toOriginal:=Programme.compose (Pins.paletteControlled H A)
    (Programme.compose (D.internalSource H A) back)

theorem transformed_included : familyAction A.basis (UniversalPairReduction.FiniteFamily.family H)⊆
    NoIOrdinaryRaw.GenericOrdinarySource.family T (build T H A back) := by
  have exactFamily : NoIOrdinaryRaw.GenericOrdinarySource.family T (build T H A back)=
      ((familyAction A.basis (UniversalPairReduction.FiniteFamily.family H)∪
      {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩})∪
      {⟨1,QuaternaryUnaryAccess.pin false⟩})∪{⟨1,QuaternaryUnaryAccess.pin true⟩}:=Pins.palette_ambient H A
  rw [exactFamily]
  intro f member
  exact Or.inl (Or.inl (Or.inl member))

def nativeTarget : NoIOrdinaryRaw.Target where
  Input:=ExactSignatureTables.Input r 1 b
  Output:=O.originalField H
  inputEncoding:=RawClosedNetwork.validatedEncoding r 1 b
  outputEncoding:=(O.originalPresentation H).encoding
  value:=O.originalValue H

def nativeIdentity : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding r 1 b) (O.originalPresentation H).encoding
    (nativeTarget H).inputEncoding (nativeTarget H).outputEncoding (O.originalValue H) (nativeTarget H).value :=
  controlledOneQueryOfEq (identityComputes _) (identityComputes _)
    ((O.originalTables H).outputBound (O.originalPresentation H)) (O.originalValue H) (fun _=>rfl)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIOrdinaryRaw.AnchorSource
end
