import Holant.Proofs.Tetrahedral.OrdinaryBothPins.Source
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPurePinsCore
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentFamilyTransport

/-! Preserve actual query/answer control through the existing equality-anchor
and sequential ordinary-two-pin construction. Every local compiler, field map,
edge scalar, factor macro and table is reused. The derived coordinate field is
kept on source answers; the terminal oracle remains the original G encoding and
field. No ordinary anchor matrix is asserted to be an original-field gadget. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 8192
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorPins
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity Computability
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace Pair
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryReplication (anchorControlled)
end Pair
namespace Single
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryUnaryAccess
  (pairControlled factorControlled ordinaryControlled paletteControlled)
end Single
namespace Both
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins
  (pairPrefix companionPrefix nativePairControlled factorControlled ordinaryControlled)
end Both
namespace Output
export Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Source
  (inputEncoding value paletteControlled palette_family_exact palette_ambient palette_first_pin palette_second_pin)
end Output

variable {s : ℕ} {a : ℕ → ℕ}
variable {L : Type} [Field L] [NumberField L]
variable (φ : L →ₐ[ℚ] AlgebraicComplex) (H : (i : Fin s) → Signature L (a i.val))
variable (A : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (OriginalLCodec.mapped φ H)))

/-- Actual scaled-anchor, holographic and edge-correction callers, followed
by the real original-L answer-codec transport. -/
def anchor :=
  Programme.compose (QuaternaryAnchorAccess.edgeControlled (OriginalLCodec.mapped φ H) A)
    (Programme.compose (QuaternaryAnchorAccess.basisControlled (OriginalLCodec.mapped φ H) A)
      (Programme.compose (QuaternaryAnchorAccess.macroControlled (OriginalLCodec.mapped φ H) A)
        (Programme.compose (QuaternaryAnchorAccess.originalControlled (OriginalLCodec.mapped φ H) A)
          (OriginalLCodec.fromCoefficient φ H))))

/-- The companion is the one selected for this whole ordinary family and
this same Eq4 anchor, not a free unary or separate singleton calculation. -/
def companion (b : Bool) :=
  Programme.compose (QuaternaryOrdinaryCompanion.anchorControlled (OriginalLCodec.mapped φ H) A b)
    (anchor φ H A)

def pair (b : Bool) :=
  Programme.compose (Pair.anchorControlled s a (OriginalLCodec.mapped φ H) A b)
    (companion φ H A b)

/-- The single-pin factor query is already controlled. Retaining this
certificate avoids erasing query validity at the finite factor interpreter. -/
def single (b : Bool) :=
  Programme.compose (Single.paletteControlled (OriginalLCodec.mapped φ H) A b)
    (Programme.compose (Single.ordinaryControlled (OriginalLCodec.mapped φ H) A b)
      (Programme.compose (Single.factorControlled (OriginalLCodec.mapped φ H) A b)
        (Programme.compose (Single.pairControlled (OriginalLCodec.mapped φ H) A b)
          (pair φ H A b))))

/-- The false-pin whole-family source is inside the second true-pin caller.
Mixed arbitrary pin occurrences therefore use one joint machine. -/
def secondPair :=
  Programme.compose (Both.pairPrefix (OriginalLCodec.mapped φ H) A)
    (Programme.compose (Both.companionPrefix (OriginalLCodec.mapped φ H) A)
      (single φ H A false))

def internal :=
  Programme.compose (Both.ordinaryControlled (OriginalLCodec.mapped φ H) A)
    (Programme.compose (Both.factorControlled (OriginalLCodec.mapped φ H) A)
      (Programme.compose (Both.nativePairControlled (OriginalLCodec.mapped φ H) A)
        (secondPair φ H A)))

/-- Charged whole-family RG+Eq4+e0+e1 source, with the unchanged original-L
native oracle. All six composition boundaries retain their query control. -/
def source : LengthControlledOracleReduction
    (Output.inputEncoding (OriginalLCodec.mapped φ H) A)
    (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single.F (OriginalLCodec.mapped φ H) A).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (Output.value (OriginalLCodec.mapped φ H) A) (OriginalLCodec.value H) :=
  Programme.compose (Output.paletteControlled (OriginalLCodec.mapped φ H) A)
    (internal φ H A)

theorem source_machine : (source φ H A).reduction.machine =
    (Programme.compose (Output.paletteControlled (OriginalLCodec.mapped φ H) A)
      (internal φ H A)).reduction.machine := rfl

/-- The source uses precisely the existing joint pin table; no independently
chosen ordinary coordinate matrix or new equality-graph construction occurs. -/
def physical : PhysicalProgramme
    (Output.inputEncoding (OriginalLCodec.mapped φ H) A)
    (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single.F (OriginalLCodec.mapped φ H) A).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (OriginalLCodec.presentation (L:=L)).encoding
    (Output.value (OriginalLCodec.mapped φ H) A) (OriginalLCodec.value H) :=
  PhysicalProgramme.ofControlled (source φ H A)

section Current
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (B : QuaternaryEqualityTerminal.AnchorStep
  (UniversalPairReduction.FiniteFamily.family (StableHigherCurrentPurePinsCore.mapped G P)))

/-- Final external oracle is the original-G native problem. The source's
ordinary edge, transformed old rows, Eq4 and both pins stay in their one actual
anchor coordinate system and its own work-field answer codec. -/
def toOriginal : PhysicalProgramme
    (Output.inputEncoding (StableHigherCurrentPurePinsCore.mapped G P) B)
    (Holant.LocalDrafts.TetrahedralCompletion.OrdinaryBothPins.Single.F
      (StableHigherCurrentPurePinsCore.mapped G P) B).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (Output.value (StableHigherCurrentPurePinsCore.mapped G P) B) (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose
    (source (StableHigherCurrentPurePinsCore.embedding G) P.table B) P.toOriginal.controlled)

theorem toOriginal_same_machine : (toOriginal G P B).controlled.reduction.machine =
    (Programme.compose (source (StableHigherCurrentPurePinsCore.embedding G) P.table B)
      P.toOriginal.controlled).reduction.machine := rfl
export StableHigherCurrentFamilyTransport (ambientFamily_eq fromAmbient)

/-- Whole-current-family anchor access from the original row source, with
one actual anchor graph and the unchanged original-G terminal oracle. -/
def fromAmbientToOriginal (A : QuaternaryEqualityTerminal.AnchorStep
    (ClosureSourceRows.ambientFamily G P)) :=
  toOriginal G P (fromAmbient G P A)

end Current

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentAnchorPins
end
