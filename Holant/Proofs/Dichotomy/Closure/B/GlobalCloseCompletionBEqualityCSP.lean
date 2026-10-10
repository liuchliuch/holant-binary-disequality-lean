import Holant.Proofs.Dichotomy.Closure.B.GlobalCloseCompletionBEqualityPins
import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4FullSource

/-! Actual whole-dictionary ordinary, even-CSP and squared-CSP sources with
literal Eq4, both pins and X. The construction is generic in the finite input
and therefore consumes the B-normalized source without a native-Palette claim. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityCSP
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace E
export GlobalCloseCompletionBEqualityAdjoin (oldLabel eq4Label)
end E
namespace Pn
export GlobalCloseCompletionBEqualityPins
  (mapped eq4_literal nativeSource pinArity pinTable pinOld pin_old_literal)
end Pn
namespace Q
export QuaternaryUnaryAccess (K F palette_old palette_pin decoded decoded_exact)
end Q
namespace W
export GlobalCloseCompletionEq4OrdinaryWire (withX withXControlled)
end W
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
variable (j : Fin s) (identity : (⟨a j.val,H j⟩ : AnySignature AlgebraicComplex)=
  ⟨2,fun x => Signature.equality (x 0) (x 1)⟩)

abbrev field := Q.K (Pn.mapped H d)
local instance : Algebra ℚ (field H d) := (field H d).algebra'
abbrev presentation := Q.F (Pn.mapped H d)
abbrev arity := EdgeSubdivision.targetArity ((s+1)+2) (Pn.pinArity H d)
abbrev table := W.withX (Pn.pinTable H d)
abbrev tables := QuaternaryOrdinaryCompanion.tables (presentation H d) (table H d)
abbrev value := (tables H d).evaluate (presentation H d)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (((s+1)+2)+1) 1 (arity H d)

def old (_H : (i : Fin s) → Signature AlgebraicComplex (a i.val))
    (i : Fin ((s+1)+2)) : Fin (((s+1)+2)+1) := Fin.castAdd 1 i

theorem old_literal (i : Fin ((s+1)+2)) :
    (⟨arity H d (old H i).val,table H d (old H i)⟩ : AnySignature (field H d))=
      ⟨Pn.pinArity H d i.val,Pn.pinTable H d i⟩ :=
  Sigma.ext (by simp [arity,old,EdgeSubdivision.targetArity,i.isLt])
    (EdgeSubdivision.extendedSignatures_old_heq (Pn.pinTable H d)
      (fun _ : Fin 1 => Signature.disequality) i)

private theorem mapAny_injective {K L : Type*} [Field K] [Field L] (φ : K →+* L) :
    Function.Injective (RingHomRealization.mapAny φ) := by
  rintro ⟨n,f⟩ ⟨m,g⟩ h
  have hn : n=m := congrArg Sigma.fst h
  subst m
  have hf := eq_of_heq (Sigma.mk.inj_iff.mp h).2
  apply congrArg (fun t : Signature K n => (⟨n,t⟩ : AnySignature K))
  funext x
  exact φ.injective (congrFun hf x)

def pinIdentity := Pn.pinOld H (E.oldLabel H j)
def pinEq4 := Pn.pinOld H (E.eq4Label H)

include identity in
theorem pin_identity_literal :
    (⟨Pn.pinArity H d (pinIdentity H j).val,Pn.pinTable H d (pinIdentity H j)⟩ :
      AnySignature (field H d))=⟨2,fun x => Signature.equality (x 0) (x 1)⟩ := by
  apply mapAny_injective (field H d).subtype
  refine (Pn.pin_old_literal H d j).trans (identity.trans ?_)
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;>
    simp [RingHomRealization.mapSignature,Signature.equality,h0,h1]

theorem pin_eq4_literal :
    (⟨Pn.pinArity H d (pinEq4 H).val,Pn.pinTable H d (pinEq4 H)⟩ : AnySignature (field H d))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ := by
  apply mapAny_injective (field H d).subtype
  have h := congrArg (RingHomRealization.mapAny (field H d).subtype)
    (Q.palette_old (Pn.mapped H d) (E.eq4Label H))
  refine h.trans ?_
  have hd : RingHomRealization.mapAny (field H d).subtype
      ⟨GlobalCloseCompletionBEqualityAdjoin.arity H d (E.eq4Label H).val,
        Q.decoded (Pn.mapped H d) (E.eq4Label H)⟩=
      (⟨GlobalCloseCompletionBEqualityAdjoin.arity H d (E.eq4Label H).val,
        Pn.mapped H d (E.eq4Label H)⟩ : AnySignature AlgebraicComplex) := by
    apply congrArg (fun f : Signature AlgebraicComplex
      (GlobalCloseCompletionBEqualityAdjoin.arity H d (E.eq4Label H).val) =>
        (⟨GlobalCloseCompletionBEqualityAdjoin.arity H d (E.eq4Label H).val,f⟩ :
          AnySignature AlgebraicComplex))
    exact funext (Q.decoded_exact (Pn.mapped H d) (E.eq4Label H))
  refine hd.trans ((Pn.eq4_literal H d).trans ?_)
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,Holant.EightVertex.ProductAnchor.equalityFour]

def eq4Label := old H (pinEq4 H)
def pinLabel (b : Bool) : Fin (((s+1)+2)+1) :=
  old H ⟨(s+1)+b.toNat,by cases b <;> simp⟩
def xLabel (_H : (i : Fin s) → Signature AlgebraicComplex (a i.val)) : Fin (((s+1)+2)+1) :=
  Fin.natAdd ((s+1)+2) (0 : Fin 1)

theorem eq4_literal :
    (⟨arity H d (eq4Label H).val,table H d (eq4Label H)⟩ : AnySignature (field H d))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ :=
  (old_literal H d (pinEq4 H)).trans (pin_eq4_literal H d)

theorem pin_literal (b : Bool) :
    (⟨arity H d (pinLabel H b).val,table H d (pinLabel H b)⟩ : AnySignature (field H d))=
      ⟨1,QuaternaryUnaryAccess.pin b⟩ :=
  (old_literal H d _).trans (Q.palette_pin (Pn.mapped H d) b)

theorem x_literal :
    (⟨arity H d (xLabel H).val,table H d (xLabel H)⟩ : AnySignature (field H d))=
      ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ :=
  Sigma.ext (by simp [arity,xLabel,EdgeSubdivision.targetArity])
    (EdgeSubdivision.extendedSignatures_new_heq (Pn.pinTable H d)
      (fun _ : Fin 1 => Signature.disequality) (0 : Fin 1))

def ordinarySource : LengthControlledOracleReduction
    (inputEncoding H d) (presentation H d).encoding
    (RawClosedNetwork.validatedEncoding s 1 a) (O.originalPresentation H).encoding
    (value H d) (O.originalValue H) :=
  Programme.compose
    (W.withXControlled (presentation H d) (Pn.pinTable H d)
      (pinIdentity H j) (pin_identity_literal H d j identity)) (Pn.nativeSource H d)

def evenCSPSource := Programme.compose
  (StableHigherCurrentEvenCSPSource.controlled (presentation H d) (table H d)
    (eq4Label H) (eq4_literal H d)) (ordinarySource H d j identity)

def squareCSPSource := Programme.compose
  (StableHigherCurrentEvenCSPSource.squareGraphControlled (presentation H d) (table H d)
    (eq4Label H) (eq4_literal H d)) (ordinarySource H d j identity)

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (((s+1)+2)+1) =>
  RingHomRealization.mapAny (field H d).subtype ⟨arity H d i.val,table H d i⟩

theorem family_eq4 : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex)∈family H d := by
  refine ⟨eq4Label H,?_⟩
  dsimp only
  rw [eq4_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,StableHigherCurrentAnchorCriterion.eq4,
    Holant.EightVertex.ProductAnchor.equalityFour]

theorem family_pin (b : Bool) :
    (⟨1,StableHigherCurrentOrdinaryTerminal.L.pin b⟩ : AnySignature AlgebraicComplex)∈family H d := by
  refine ⟨pinLabel H b,?_⟩
  dsimp only
  rw [pin_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 1 => (⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin,StableHigherCurrentAnchorLocalBasis.pin]

theorem family_x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈family H d := by
  refine ⟨xLabel H,?_⟩
  dsimp only
  rw [x_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.disequality]

theorem old_mapped (i : Fin s) :
    RingHomRealization.mapAny (field H d).subtype
      ⟨arity H d (old H (Pn.pinOld H (E.oldLabel H i))).val,
        table H d (old H (Pn.pinOld H (E.oldLabel H i)))⟩=⟨a i.val,H i⟩ := by
  rw [old_literal]
  exact Pn.pin_old_literal H d i

theorem current_included : (Set.range fun i : Fin s => (⟨a i.val,H i⟩ : AnySignature AlgebraicComplex))⊆family H d := by
  rintro _ ⟨i,rfl⟩
  exact ⟨old H (Pn.pinOld H (E.oldLabel H i)),old_mapped H d i⟩

theorem tract_iff_test : Tract (family H d) ↔
    StableHigherCurrentOrdinaryTerminal.Test (preprocess (family H d)) := by
  rw [StableHigherCurrentOrdinaryTerminal.tract_iff_finite_test
    (family_pin H d false) (family_pin H d true) (family_eq4 H d)]
  exact and_iff_right ((Set.finite_range _).subset (fun _ h => h.1))

theorem rejected_iff : ¬Tract (family H d) ↔
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (family H d)) :=
  StableHigherCurrentOrdinaryTerminal.not_tract_iff_obstruction
    ((Set.finite_range _).subset (fun _ h => h.1))
    (family_pin H d false) (family_pin H d true) (family_eq4 H d)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionBEqualityCSP
end
