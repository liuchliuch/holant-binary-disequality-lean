import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBNativeSource
import Holant.Proofs.Hardness.GeneralEOPureFamilyAccess

/-! Coefficient-field input for the actual B-normalized native source. The
answer is recovered by the proved rational-linear retraction, enabling existing
arbitrary-family native gadget compilers without identifying field codecs. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNativeCodec
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace W
export GlobalCloseCompletionBWorkfield (K field values algebraic)
end W
namespace S
export GlobalCloseCompletionBNativeSource (arity inputEncoding table tables value source native_edges)
end S
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalValue target_exact)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
local instance : Algebra ℚ (W.K G P) := (W.K G P).algebra'

def mapped (i : Fin (P.count+1)) : Signature AlgebraicComplex (S.arity G P i.val) :=
  fun x => (S.table G P i x : AlgebraicComplex)

theorem native_value (r : ExactSignatureTables.Input (P.count+1) 1 (S.arity G P)) :
    (S.value G P r : AlgebraicComplex)=(O.originalValue (mapped G P) r : AlgebraicComplex) := by
  rw [O.target_exact,S.value,ExactSignatureTables.evaluate_eq_decoded]
  change (W.K G P).subtype _=_
  rw [←Network.denote_map (W.K G P).subtype]
  apply congrArg (fun N : Network AlgebraicComplex 0 => N.denote Fin.elim0)
  unfold Network.map RawClosedNetwork.realize
  congr 1
  funext e b c
  change (W.K G P).subtype ((W.field G P).decode
    ((S.tables G P).edge (r.val.edgeLabel r.property e) b c))=Signature.disequality b c
  rw [S.native_edges]
  cases b <;> cases c <;> rfl

/-- Same raw input, real faithful field conversion, and no algebraic-field
inclusion assumption in either direction. -/
def fromCoefficient : LengthControlledOracleReduction
    (S.inputEncoding G P) (O.originalPresentation (mapped G P)).encoding
    (S.inputEncoding G P) (W.field G P).encoding
    (O.originalValue (mapped G P)) (S.value G P) :=
  controlledOneQueryOfEq (identityComputes (S.inputEncoding G P))
    (FamilyAnswerTransport.computes (O.coefficients (mapped G P)) (W.values G P)
      (O.coefficients_algebraic (mapped G P)) (W.algebraic G P))
    ((S.tables G P).outputBound (W.field G P)) (O.originalValue (mapped G P))
    (fun r => (FamilyAnswerTransport.recover_exact (O.coefficients (mapped G P)) (W.values G P)
      (O.originalValue (mapped G P) r) (S.value G P r) (native_value G P r)).symm)

def source : LengthControlledOracleReduction
    (S.inputEncoding G P) (O.originalPresentation (mapped G P)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue (mapped G P)) (OriginalForestSource.value G) :=
  Programme.compose (fromCoefficient G P) (S.source G P)

variable {t : ℕ} (T : ℕ → Template)
variable (valid : ∀k<t,(T k).WellFormed (P.count+1) 1 (S.arity G P))
abbrev macroFamily := GeneralEOPureFamilyAccess.family (mapped G P) T valid

def macroSource : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding t 1 (GeneralEOPureFamilyAccess.arity T))
    (O.originalPresentation (macroFamily G P T valid)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (O.originalValue (macroFamily G P T valid)) (OriginalForestSource.value G) :=
  Programme.compose (GeneralEOPureFamilyAccess.source (mapped G P) T valid) (source G P)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBNativeCodec
end
