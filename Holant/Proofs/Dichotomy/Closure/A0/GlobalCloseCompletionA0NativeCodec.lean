import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0NativeSource
import Holant.Proofs.Dichotomy.Closure.A0.GlobalCloseCompletionA0RetainedX
import Holant.Proofs.Hardness.GeneralEOPureFamilyAccess

/-! Actual coefficient-codec native-X source for the whole Hadamard current
family. The original-field codec conversion is the proved OriginalLCodec
programme. The unshifted branch supplies the required scalar-X row internally
from its actual retained complete-group source, without an extra resource. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0NativeCodec
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace W
export GlobalCloseCompletionA0Workfield (K field)
end W
namespace S
export GlobalCloseCompletionA0NativeSource (arity inputEncoding table tables value source native_edges)
end S
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (originalPresentation originalValue)
end O
namespace R
export GlobalCloseCompletionA0RetainedX (retained coefficient coefficient_nonzero label row_literal)
end R
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (d : GlobalCloseCompletionA0XSource.Row G P)

abbrev embedding := StableHigherCurrentPurePinsCore.embedding G
abbrev mapped := OriginalLCodec.mapped (embedding G) (S.table G P)

private theorem native_tables : OriginalLCodec.tables (S.table G P)=S.tables G P := by
  unfold OriginalLCodec.tables
    Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralFieldReduction.targetTables
    Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.FieldReduction.targetTables
  congr 1
  · funext i x
    exact LinearEquiv.symm_apply_apply _ _
  · funext i b c
    apply (W.field G).decode.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (S.native_edges G P i b c).symm

/-- Both codecs are explicit; equality of unspecified field encodings is not
assumed. All answers are converted back into the field fixed from original G. -/
def fromCoefficient : LengthControlledOracleReduction
    (S.inputEncoding G P) (O.originalPresentation (mapped G P)).encoding
    (S.inputEncoding G P) (W.field G).encoding
    (O.originalValue (mapped G P)) (S.value G P) := by
  have r := OriginalLCodec.fromCoefficient (embedding G) (S.table G P)
  change LengthControlledOracleReduction _ _ _ _ _
    ((OriginalLCodec.tables (S.table G P)).evaluate (W.field G)) at r
  rw [native_tables] at r
  exact r

def source : LengthControlledOracleReduction
    (S.inputEncoding G P) (O.originalPresentation (mapped G P)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue (mapped G P)) (OriginalForestSource.value G) :=
  Programme.compose (fromCoefficient G P) (S.source G P d)

variable {t : ℕ} (T : ℕ → Template)
variable (valid : ∀k<t,(T k).WellFormed (P.count+1) 1 (S.arity G P))
abbrev macroFamily := GeneralEOPureFamilyAccess.family (mapped G P) T valid

def macroSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (GeneralEOPureFamilyAccess.arity T))
    (O.originalPresentation (macroFamily G P T valid)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue (macroFamily G P T valid)) (OriginalForestSource.value G) :=
  Programme.compose (GeneralEOPureFamilyAccess.source (mapped G P) T valid) (source G P d)

variable (torsion : ResidualTorsion P.family)
variable (N : ClosureMarkedDihedralA0.NativeA0
  (ClosureMarkedDihedral.Source.group (ClosureSourceRows.embedding G) P.family torsion))
variable (q : Signature (OI.K G) 4) (core : Holant.LocalDrafts.FinitePGL2.Stabilization.MinimumCore P.family)
variable (literal : core.signature=⟨4,q⟩)

def actualRow : GlobalCloseCompletionA0XSource.Row G (R.retained G P torsion q core literal) where
  label := R.label G P torsion N q core literal
  scalar := R.coefficient G P torsion N
  nonzero := R.coefficient_nonzero G P torsion N
  literal := R.row_literal G P torsion N q core literal

def actualSource := source G (R.retained G P torsion q core literal)
  (actualRow G P torsion N q core literal)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionA0NativeCodec
end
