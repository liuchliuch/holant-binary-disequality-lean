import Holant.Proofs.Dichotomy.Closure.Eq4.GlobalCloseCompletionEq4CSPSource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentOrdinaryTerminal
import Holant.Proofs.Closure.FrontierCurrentClosure

/-! The full Eq4 ordinary source also retains literal X as a vertex. This
records the original native edge for a later common-basis pullback. Old rows,
Eq4 and both pins remain literal, and all source machines terminate at G. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4FullSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace S
export GlobalCloseCompletionEq4CSPSource (field presentation arity table identityLabel identity_literal eq4Label eq4_literal)
end S
namespace E
export GlobalCloseCompletionEq4Adjoin (oldLabel)
end E
namespace Pn
export GlobalCloseCompletionEq4Pins (mapped nativeSource pinOld pin_old_literal)
end Pn
namespace W
export GlobalCloseCompletionEq4OrdinaryWire (withX withXControlled)
end W
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ → ℕ}
variable (G : (i : Fin s) → Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (d : GlobalCloseCompletionEq4Graph.Output G P)
local instance : Algebra ℚ (S.field G P d) := (S.field G P d).algebra'

abbrev count := ((P.count+1)+2)+1
abbrev arity := EdgeSubdivision.targetArity ((P.count+1)+2) (S.arity G P d)
abbrev table := W.withX (S.table G P d)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P d)
abbrev tables := QuaternaryOrdinaryCompanion.tables (S.presentation G P d) (table G P d)
abbrev value := (tables G P d).evaluate (S.presentation G P d)
def old (i : Fin ((P.count+1)+2)) : Fin (count G P) := Fin.castAdd 1 i

theorem old_literal (i : Fin ((P.count+1)+2)) :
    (⟨arity G P d (old G P i).val,table G P d (old G P i)⟩ : AnySignature (S.field G P d))=
      ⟨S.arity G P d i.val,S.table G P d i⟩ :=
  Sigma.ext (by simp [arity,old,EdgeSubdivision.targetArity,i.isLt])
    (EdgeSubdivision.extendedSignatures_old_heq (S.table G P d)
      (fun _ : Fin 1 => Signature.disequality) i)

def eq4Label := old G P (S.eq4Label G P)
def pinLabel (b : Bool) : Fin (count G P) :=
  old G P ⟨(P.count+1)+b.toNat,by cases b <;> simp <;> omega⟩
def xLabel : Fin (count G P) := Fin.natAdd ((P.count+1)+2) (0 : Fin 1)

theorem eq4_literal :
    (⟨arity G P d (eq4Label G P).val,table G P d (eq4Label G P)⟩ : AnySignature (S.field G P d))=
      ⟨4,Holant.EightVertex.ProductAnchor.equalityFour⟩ :=
  (old_literal G P d (S.eq4Label G P)).trans (S.eq4_literal G P d)

theorem pin_literal (b : Bool) :
    (⟨arity G P d (pinLabel G P b).val,table G P d (pinLabel G P b)⟩ :
      AnySignature (S.field G P d))=⟨1,QuaternaryUnaryAccess.pin b⟩ :=
  (old_literal G P d _).trans (QuaternaryUnaryAccess.palette_pin (Pn.mapped G P d) b)

theorem x_literal :
    (⟨arity G P d (xLabel G P).val,table G P d (xLabel G P)⟩ : AnySignature (S.field G P d))=
      ⟨2,fun x => Signature.disequality (x 0) (x 1)⟩ :=
  Sigma.ext (by simp [arity,xLabel,EdgeSubdivision.targetArity])
    (EdgeSubdivision.extendedSignatures_new_heq (S.table G P d)
      (fun _ : Fin 1 => Signature.disequality) (0 : Fin 1))

/-- Both the arbitrary-X-vertex source and its identity wire replacement are
fully controlled in one field; the original Eq4 and pin programmes are inlined. -/
def ordinarySource : LengthControlledOracleReduction
    (inputEncoding G P d) (S.presentation G P d).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P d) (OriginalForestSource.value G) :=
  Programme.compose (W.withXControlled (S.presentation G P d) (S.table G P d)
    (S.identityLabel G P) (S.identity_literal G P d)) (Pn.nativeSource G P d)

def evenCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.controlled (S.presentation G P d) (table G P d)
    (eq4Label G P) (eq4_literal G P d)) (ordinarySource G P d))

def squareCSPSource := PhysicalProgramme.ofControlled (Programme.compose
  (StableHigherCurrentEvenCSPSource.squareGraphControlled (S.presentation G P d) (table G P d)
    (eq4Label G P) (eq4_literal G P d)) (ordinarySource G P d))

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin (count G P) =>
  RingHomRealization.mapAny (S.field G P d).subtype ⟨arity G P d i.val,table G P d i⟩

theorem family_eq4 : (⟨4,StableHigherCurrentAnchorCriterion.eq4⟩ : AnySignature AlgebraicComplex)∈
    family G P d := by
  refine ⟨eq4Label G P,?_⟩
  dsimp only
  rw [eq4_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 4 => (⟨4,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,StableHigherCurrentAnchorCriterion.eq4,
    Holant.EightVertex.ProductAnchor.equalityFour]

theorem family_pin (b : Bool) :
    (⟨1,StableHigherCurrentOrdinaryTerminal.L.pin b⟩ : AnySignature AlgebraicComplex)∈family G P d := by
  refine ⟨pinLabel G P b,?_⟩
  dsimp only
  rw [pin_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 1 => (⟨1,f⟩ : AnySignature AlgebraicComplex))
  funext x
  simp [RingHomRealization.mapSignature,QuaternaryUnaryAccess.pin,
    StableHigherCurrentAnchorLocalBasis.pin]

theorem family_x : (⟨2,kernelSignature Signature.disequality⟩ : AnySignature AlgebraicComplex)∈
    family G P d := by
  refine ⟨xLabel G P,?_⟩
  dsimp only
  rw [x_literal]
  apply congrArg (fun f : Signature AlgebraicComplex 2 => (⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext x
  cases x 0 <;> cases x 1 <;> simp [RingHomRealization.mapSignature,kernelSignature,Signature.disequality]

/-- Every original current label, including noncentral higher rows and
repeated equal rows, is retained in the same ordinary table. -/
theorem current_included : CurrentFrontierClosure.currentFamily G P ⊆ family G P d := by
  rintro _ ⟨f,⟨i,rfl⟩,rfl⟩
  refine ⟨old G P (Pn.pinOld G P (E.oldLabel G P i)),?_⟩
  dsimp only
  rw [old_literal]
  exact Pn.pin_old_literal G P d i

theorem tract_iff_test : Tract (family G P d) ↔
    StableHigherCurrentOrdinaryTerminal.Test (preprocess (family G P d)) := by
  rw [StableHigherCurrentOrdinaryTerminal.tract_iff_finite_test
    (family_pin G P d false) (family_pin G P d true) (family_eq4 G P d)]
  exact and_iff_right ((Set.finite_range _).subset (fun _ h => h.1))

theorem rejected_iff : ¬Tract (family G P d) ↔
    StableHigherCurrentOrdinaryTerminal.Obstruction (preprocess (family G P d)) :=
  StableHigherCurrentOrdinaryTerminal.not_tract_iff_obstruction
    ((Set.finite_range _).subset (fun _ h => h.1))
    (family_pin G P d false) (family_pin G P d true) (family_eq4 G P d)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionEq4FullSource
end
