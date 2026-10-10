import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4Pins
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4OrdinaryWire

/-! Whole-current-family ordinary, even-CSP and squared-CSP sources from an
actual scalar Eq4 graph. All original rows are literal in one work field;
Eq4 and both pins have literal unit coefficients. Identity-edge subdivision
and each field/scalar/pin compiler terminate at the unchanged original G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4CSPSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionEq4Adjoin (arity signatures eq4Label oldLabel old_signature)
end E
namespace Pn
export GlobalCloseCompletionEq4Pins
  (mapped embedding eq4_literal nativeSource pinArity pinTable pinOld pin_old_literal)
end Pn
namespace Q
export QuaternaryUnaryAccess (K F palette_old decoded decoded_exact)
end Q
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)

abbrev field := Q.K (Pn.mapped G P d)
local instance : Algebra ℚ (field G P d) := (field G P d).algebra'
abbrev presentation := Q.F (Pn.mapped G P d)
abbrev arity := Pn.pinArity G P d
abbrev table := Pn.pinTable G P d
abbrev inputEncoding := QuaternaryUnaryAccess.paletteEncoding (P.count+1) (E.arity G P d)

def identityLabel := Pn.pinOld G P (E.oldLabel G P P.equality.choose)
def eq4Label := Pn.pinOld G P (E.eq4Label G P)

private theorem mapAny_injective {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun t : Signature K n => (⟨n,t⟩ : AnySignature K))
  funext x
  exact φ.injective (congrFun hf x)

theorem identity_literal :
    (⟨arity G P d (identityLabel G P).val,table G P d (identityLabel G P)⟩ :
      AnySignature (field G P d))=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  apply mapAny_injective (field G P d).subtype
  change RingHomRealization.mapAny (Q.K (Pn.mapped G P d)).subtype
    ⟨Pn.pinArity G P d (Pn.pinOld G P (E.oldLabel G P P.equality.choose)).val,
      Pn.pinTable G P d (Pn.pinOld G P (E.oldLabel G P P.equality.choose))⟩ = _
  rw [Pn.pin_old_literal]
  have hi : (⟨P.arity P.equality.choose.val,P.table P.equality.choose⟩ : AnySignature (OI.K G))=
    ⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := P.equality.choose_spec
  rw [hi]
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,Signature.equality]

theorem eq4_literal :
    (⟨arity G P d (eq4Label G P).val,table G P d (eq4Label G P)⟩ :
      AnySignature (field G P d))=⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  apply mapAny_injective (field G P d).subtype
  have h := congrArg (RingHomRealization.mapAny (field G P d).subtype)
    (Q.palette_old (Pn.mapped G P d) (E.eq4Label G P))
  refine h.trans ?_
  have hd : RingHomRealization.mapAny (field G P d).subtype
      ⟨E.arity G P d (E.eq4Label G P).val,Q.decoded (Pn.mapped G P d) (E.eq4Label G P)⟩=
      (⟨E.arity G P d (E.eq4Label G P).val,Pn.mapped G P d (E.eq4Label G P)⟩ :
        AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex (E.arity G P d (E.eq4Label G P).val) =>
      (⟨E.arity G P d (E.eq4Label G P).val,f⟩ : AnySignature AlgebraicComplex))
    exact funext (Q.decoded_exact (Pn.mapped G P d) (E.eq4Label G P))
  refine hd.trans ((Pn.eq4_literal G P d).trans ?_)
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

abbrev ordinaryTables := QuaternaryOrdinaryCompanion.tables (presentation G P d) (table G P d)
abbrev ordinaryValue := (ordinaryTables G P d).evaluate (presentation G P d)

/-- The ordinary table keeps every row in its original coordinates. -/
def ordinarySource : LengthControlledOracleReduction
    (inputEncoding G P d) (presentation G P d).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (ordinaryValue G P d) (OriginalForestSource.value G) :=
  Programme.compose
    (GlobalCloseCompletionEq4OrdinaryWire.controlled (presentation G P d) (table G P d)
      (identityLabel G P) (identity_literal G P d))
    (Pn.nativeSource G P d)

/-- Arbitrary even occurrences of every current row, Eq4 and both pins. -/
def evenCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.controlled (presentation G P d) (table G P d)
    (eq4Label G P) (eq4_literal G P d))
  (ordinarySource G P d))

/-- Arbitrary CSP occurrences of the pointwise-squared whole pin family. -/
def squareCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.squareGraphControlled (presentation G P d) (table G P d)
    (eq4Label G P) (eq4_literal G P d))
  (ordinarySource G P d))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4CSPSource
end
