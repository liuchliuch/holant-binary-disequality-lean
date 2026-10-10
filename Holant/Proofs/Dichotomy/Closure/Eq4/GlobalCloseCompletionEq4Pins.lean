import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Adjoin
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPureOrdinary

/-! An actual scalar Eq4 graph installs simultaneous, arbitrary-occurrence
access to both pins for the entire current palette. The normalization caller,
physical replication/factor interpreter and original-field answer map are all
inlined; no pin gadget or higher-ancestor reconstruction is assumed. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Pins
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4Adjoin (arity signatures eq4Label eq4_signature oldLabel old_signature toOriginal)
end E
namespace Q
export QuaternaryUnaryAccess (K F paletteArity palette paletteEncoding paletteValue palette_old palette_pin decoded decoded_exact)
end Q
namespace O
export StableHigherCurrentPureOrdinarySource (ordinaryControlled nativeCodec ordinaryFamily ordinary_family_exact)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)

abbrev embedding := StableHigherCurrentPurePinsCore.embedding G
abbrev mapped := OriginalLCodec.mapped (embedding G) (E.signatures G P d)

theorem eq4_literal :
    (⟨E.arity G P d (E.eq4Label G P).val,mapped G P d (E.eq4Label G P)⟩ :
      AnySignature AlgebraicComplex)=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  have h := congrArg (RingHomRealization.mapAny (embedding G).toRingHom) (E.eq4_signature G P d)
  refine h.trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

def pure : QuaternaryEqualityTerminal.PureStep
    (Holant.EightVertex.ProductAnchor.equalityFour : Signature AlgebraicComplex 4) where
  left := 1
  right := 1
  left_ne_zero := one_ne_zero
  right_ne_zero := one_ne_zero
  original := by
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3 <;>
      simp [Holant.EightVertex.ProductAnchor.equalityFour,Holant.EightVertex.ProductAnchor.ge4,
        funext_iff,Fin.forall_fin_succ,h0,h1,h2,h3]

/-- The two-pin source is a real interpreter over the normalized Eq4 adjoin,
followed by its actual nonzero scalar removal at every occurrence. -/
def nativeSource : LengthControlledOracleReduction
    (Q.paletteEncoding (P.count+1) (E.arity G P d)) (Q.F (mapped G P d)).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (Q.paletteValue (mapped G P d)) (OriginalForestSource.value G) :=
  Programme.compose
    (StableHigherCurrentUnaryQueryControl.SourceV2.source (embedding G) (E.signatures G P d)
      (E.eq4Label G P) (eq4_literal G P d) pure)
    (E.toOriginal G P d)

/-- One fixed normalized K acts on every old row, Eq4 and both pins. -/
def ordinaryKSource := PhysicalProgramme.ofControlled (Programme.compose
  (O.ordinaryControlled (mapped G P d))
  (Programme.compose (O.nativeCodec (mapped G P d)) (nativeSource G P d)))

abbrev pinArity := Q.paletteArity (P.count+1) (E.arity G P d)
abbrev pinTable := Q.palette (mapped G P d)
def pinOld (i : Fin (P.count+1)) : Fin ((P.count+1)+2) :=
  ⟨i.val,Nat.lt.step (Nat.lt.step i.isLt)⟩

theorem pin_old_literal (i : Fin P.count) :
    RingHomRealization.mapAny (Q.K (mapped G P d)).subtype
      (⟨pinArity G P d (pinOld G P (E.oldLabel G P i)).val,
        pinTable G P d (pinOld G P (E.oldLabel G P i))⟩ : AnySignature (Q.K (mapped G P d)))=
      RingHomRealization.mapAny (embedding G).toRingHom ⟨P.arity i.val,P.table i⟩ := by
  have hp := congrArg (RingHomRealization.mapAny (Q.K (mapped G P d)).subtype)
    (Q.palette_old (mapped G P d) (E.oldLabel G P i))
  refine hp.trans ?_
  have decoded : RingHomRealization.mapAny (Q.K (mapped G P d)).subtype
      ⟨E.arity G P d (E.oldLabel G P i).val,Q.decoded (mapped G P d) (E.oldLabel G P i)⟩=
      (⟨E.arity G P d (E.oldLabel G P i).val,mapped G P d (E.oldLabel G P i)⟩ :
        AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex (E.arity G P d (E.oldLabel G P i).val) =>
      (⟨E.arity G P d (E.oldLabel G P i).val,f⟩ : AnySignature AlgebraicComplex))
    exact funext (Q.decoded_exact (mapped G P d) (E.oldLabel G P i))
  exact decoded.trans (congrArg (RingHomRealization.mapAny (embedding G).toRingHom)
    (E.old_signature G P d i))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4Pins
end
