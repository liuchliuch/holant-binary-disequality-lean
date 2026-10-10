import Holant.Proofs.Dichotomy.General.GenericOrdinarySource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentAnchorPins

/-! A finite actual native anchor and its real original-G oracle programme
supply the ordinary Eq4/two-pin interface. No literal identity, X row, special
binary, or hardness backend is required. Every original row is retained under
the same anchor basis and in one physically implemented coefficient field. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericOrdinaryData
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Pins
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (paletteArity palette palette_ambient palette_original palette_first_pin palette_second_pin paletteControlled)
end Pins
namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single (K F)
end Single
namespace Pair
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication (anchorControlled)
end Pair
namespace Unary
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
  (pairControlled factorControlled ordinaryControlled paletteControlled)
end Unary
namespace Both
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
  (pairPrefix companionPrefix nativePairControlled factorControlled ordinaryControlled)
end Both
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r : ℕ} {a b : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep (UniversalPairReduction.FiniteFamily.family H))
abbrev field := Single.K H A
local instance : Algebra ℚ (field H A) := (field H A).algebra'
abbrev presentation := Single.F H A
abbrev arity := Pins.paletteArity H A
abbrev table := Pins.palette H A

def anchorSource :=
  Programme.compose (QuaternaryAnchorAccess.edgeControlled H A)
    (Programme.compose (QuaternaryAnchorAccess.basisControlled H A)
      (Programme.compose (QuaternaryAnchorAccess.macroControlled H A)
        (QuaternaryAnchorAccess.originalControlled H A)))
def companionSource (v : Bool) :=
  Programme.compose (QuaternaryOrdinaryCompanion.anchorControlled H A v) (anchorSource H A)
def pairSource (v : Bool) :=
  Programme.compose (Pair.anchorControlled r b H A v) (companionSource H A v)
def singleSource (v : Bool) :=
  Programme.compose (Unary.paletteControlled H A v)
    (Programme.compose (Unary.ordinaryControlled H A v)
      (Programme.compose (Unary.factorControlled H A v)
        (Programme.compose (Unary.pairControlled H A v) (pairSource H A v))))
def secondPairSource :=
  Programme.compose (Both.pairPrefix H A)
    (Programme.compose (Both.companionPrefix H A) (singleSource H A false))
def internalSource :=
  Programme.compose (Both.ordinaryControlled H A)
    (Programme.compose (Both.factorControlled H A)
      (Programme.compose (Both.nativePairControlled H A) (secondPairSource H A)))

variable (back : LengthControlledOracleReduction
  (RawClosedNetwork.validatedEncoding r 1 b) (O.originalPresentation H).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (O.originalValue H) (OriginalForestSource.value G))

def build : GenericOrdinarySource.Data G where
  K := field H A
  degree := _
  F := presentation H A
  size := r+3
  b := arity H A
  H := table H A
  e := ⟨r,by omega⟩
  p v := if v then ⟨r+2,by omega⟩ else ⟨r+1,by omega⟩
  he := (Pins.palette_original H A (QuaternaryOrdinaryCompanion.eq4Index (s:=r))).trans
    (QuaternaryOrdinaryCompanion.decoded_eq4 H A)
  hp v := by
    cases v
    · exact Pins.palette_first_pin H A
    · exact Pins.palette_second_pin H A
  toOriginal := Programme.compose (Pins.paletteControlled H A)
    (Programme.compose (internalSource H A) back)

theorem family_exact : GenericOrdinarySource.family G (build G H A back)=
    ((familyAction A.basis (UniversalPairReduction.FiniteFamily.family H)∪
      {⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩})∪
      {⟨1,QuaternaryUnaryAccess.pin false⟩})∪{⟨1,QuaternaryUnaryAccess.pin true⟩} :=
  Pins.palette_ambient H A

theorem transformed_included : familyAction A.basis (UniversalPairReduction.FiniteFamily.family H)⊆
    GenericOrdinarySource.family G (build G H A back) := by
  rw [family_exact]
  intro f hf
  exact Or.inl (Or.inl (Or.inl hf))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionGenericOrdinaryData
end
