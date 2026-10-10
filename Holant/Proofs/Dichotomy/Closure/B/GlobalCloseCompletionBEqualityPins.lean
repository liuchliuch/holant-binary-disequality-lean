import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityAdjoin
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Pins

/-! Whole-dictionary two-pin access from the actual generic Eq4 adjoin.
The existing physical replication/factor interpreter and every coefficient
retraction are composed. The final oracle is the original input dictionary. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityPins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionBEqualityAdjoin
  (K embedding arity signatures oldLabel old_signature eq4Label eq4_signature toOriginal)
end E
namespace Q
export QuaternaryUnaryAccess (K F paletteArity palette paletteEncoding paletteValue palette_old palette_pin decoded decoded_exact)
end Q
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget (originalPresentation originalValue)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (H : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K H) := OI.numberField H
variable (d : GlobalCloseCompletionBPrimeEq4.Output H)

abbrev mapped := OriginalLCodec.mapped (E.embedding H) (E.signatures H d)

theorem eq4_literal :
    (⟨E.arity H d (E.eq4Label H).val,mapped H d (E.eq4Label H)⟩ : AnySignature AlgebraicComplex)=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have h := congrArg (RingHomRealization.mapAny (E.embedding H).toRingHom) (E.eq4_signature H d)
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

def nativeSource : LengthControlledOracleReduction
    (Q.paletteEncoding (s+1) (E.arity H d)) (Q.F (mapped H d)).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation H).encoding
    (Q.paletteValue (mapped H d)) (O.originalValue H) :=
  Programme.compose
    (StableHigherCurrentUnaryQueryControl.SourceV2.source (E.embedding H) (E.signatures H d)
      (E.eq4Label H) (eq4_literal H d) GlobalCloseCompletionEq4Pins.pure)
    (E.toOriginal H d)

abbrev pinArity := Q.paletteArity (s+1) (E.arity H d)
abbrev pinTable := Q.palette (mapped H d)
def pinOld (_H : (i : Fin s) → Signature AlgebraicComplex (a i.val)) (i : Fin (s+1)) : Fin ((s+1)+2) :=
  ⟨i.val,Nat.lt_succ_of_lt (Nat.lt_succ_of_lt i.isLt)⟩

theorem pin_old_literal (i : Fin s) :
    RingHomRealization.mapAny (Q.K (mapped H d)).subtype
      (⟨pinArity H d (pinOld H (E.oldLabel H i)).val,pinTable H d (pinOld H (E.oldLabel H i))⟩ :
        AnySignature (Q.K (mapped H d)))=⟨a i.val,H i⟩ := by
  have hp := congrArg (RingHomRealization.mapAny (Q.K (mapped H d)).subtype)
    (Q.palette_old (mapped H d) (E.oldLabel H i))
  refine hp.trans ?_
  have decoded : RingHomRealization.mapAny (Q.K (mapped H d)).subtype
      ⟨E.arity H d (E.oldLabel H i).val,Q.decoded (mapped H d) (E.oldLabel H i)⟩=
      (⟨E.arity H d (E.oldLabel H i).val,mapped H d (E.oldLabel H i)⟩ :
        AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex (E.arity H d (E.oldLabel H i).val) =>
      (⟨E.arity H d (E.oldLabel H i).val,f⟩ : AnySignature AlgebraicComplex))
    exact funext (Q.decoded_exact (mapped H d) (E.oldLabel H i))
  exact decoded.trans (congrArg (RingHomRealization.mapAny (E.embedding H).toRingHom)
    (E.old_signature H d i))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityPins
end
