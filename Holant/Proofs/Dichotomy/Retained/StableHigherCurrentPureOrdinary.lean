import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPureOrdinaryCodec
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPurePinsCore

/-! Whole-family ordinary source for the actual pure q4 event. The existing
fixed K graph identity and both field-codec callers are composed with the
controlled joint native-pin machine, then with the saved current-to-original G
programme. The actual ordinary nonzero unary is an output, not a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinary
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open StableHigherCurrentPurePinsCore
namespace Ordinary
export Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource
  (inputEncoding presentation value ordinaryControlled nativeCodec ordinaryPalette ordinaryFamily
   unary unary_nonzero pinIndex ordinary_pin ordinary_family_exact odd_label)
end Ordinary
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (j : Fin P.count) {q : Signature AlgebraicComplex 4}
variable (literal : (⟨P.arity j.val,mapped G P j⟩ : AnySignature AlgebraicComplex) = ⟨4,q⟩)
variable (pure : QuaternaryEqualityTerminal.PureStep q)

/-- The displayed pure q4 event feeds the real SourceV2 interpreter. The
ordinary table is exactly the old source K-image and its two transformed pins. -/
def toCurrent : LengthControlledOracleReduction
    (Ordinary.inputEncoding (s:=P.count) (a:=P.arity)) (Ordinary.presentation (mapped G P)).encoding
    (RawClosedNetwork.validatedEncoding P.count 1 P.arity) (OI.presentation G).encoding
    (Ordinary.value (mapped G P)) (Holant.LocalDrafts.Hardness.FrozenFactorNormalization.OriginalLCodec.value P.table) :=
  Programme.compose (Ordinary.ordinaryControlled (mapped G P))
    (Programme.compose (Ordinary.nativeCodec (mapped G P))
      (StableHigherCurrentUnaryQueryControl.SourceV2.source (embedding G) P.table j literal pure))

def toOriginal : PhysicalProgramme
    (Ordinary.inputEncoding (s:=P.count) (a:=P.arity)) (Ordinary.presentation (mapped G P)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (Ordinary.value (mapped G P)) (OriginalForestSource.value G) :=
  PhysicalProgramme.ofControlled (Programme.compose (toCurrent G P j literal pure) P.toOriginal.controlled)

/-- Both displayed unaries belong to the one actual whole-family ordinary
source, including their genuine original integer labels and arities. -/
theorem source_unary (b : Bool) :
    (⟨1,Ordinary.unary b⟩ : AnySignature AlgebraicComplex) ∈ Ordinary.ordinaryFamily (mapped G P) ∧
      Ordinary.unary b ≠ 0 :=
  ⟨⟨Ordinary.pinIndex b,Ordinary.ordinary_pin (mapped G P) b⟩,Ordinary.unary_nonzero b⟩

theorem source_odd (b : Bool) :
    Odd (Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinarySource.arity
      (s:=P.count) (a:=P.arity) (Ordinary.pinIndex (s:=P.count) b).val) ∧
      Ordinary.ordinaryPalette (mapped G P) (Ordinary.pinIndex b) ≠ 0 :=
  Ordinary.odd_label (mapped G P) b

theorem same_machine : (toOriginal G P j literal pure).controlled.reduction.machine =
    (Programme.compose (toCurrent G P j literal pure) P.toOriginal.controlled).reduction.machine := rfl

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.StableHigherCurrentPureOrdinary
end
