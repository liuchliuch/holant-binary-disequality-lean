import Holant.Proofs.Dichotomy.Closure.Symmetric.GlobalCloseCompletionSymmetricGHZCoordinates
import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryOrdinaryFieldCodec

/-! Whole-family symmetric-GHZ source, with its actual Gram edge. The
matrix may use algebraic coefficients outside the original presentation.
Both answer conversions are real fixed rational machines; all ordered raw
incidences and all old labels survive. This is the holographic source step,
not the further bipartite equality-three-to-CSP compiler. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
namespace C
export GlobalCloseCompletionSymmetricGHZCoordinates (eq3 gram ghz pin gram_value inverse_ghz)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val)) (R : InvertibleKernel)

def transformed (i : Fin r) : Signature AlgebraicComplex (b i.val) := R.symm.action (H i)
def edges : Fin 1→Kernel AlgebraicComplex := fun _=>C.gram R.matrix
abbrev coefficients := OriginalFamily.coefficient (transformed H R) (edges R)
abbrev field := familyField (coefficients H R)
local instance : Algebra ℚ (field H R) := (field H R).algebra'
abbrev presentation := OriginalFamily.presentation (transformed H R) (edges R)
abbrev tables := OriginalFamily.tables (transformed H R) (edges R)
abbrev value := OriginalFamily.value (transformed H R) (edges R)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding r 1 b

theorem value_exact (q : ExactSignatureTables.Input r 1 b) :
    (value H R q : AlgebraicComplex)=(KSourceTransport.originalValue H q : AlgebraicComplex) := by
  rw [OriginalFamily.value_exact,OriginalFamily.value_exact]
  have h := congrFun (Network.denote_holographicTransform
    (q.val.realize q.property H KSourceTransport.equalityEdges)
    R.matrix R.inverse R.matrix_inverse) Fin.elim0
  simp only [transformed,edges,C.gram,KSourceTransport.equalityEdges,
    InvertibleKernel.action,InvertibleKernel.symm,Network.holographicTransform,
    RawClosedNetwork.realize,Network.denote] at h ⊢
  convert h using 1 <;> rfl

def recover : Computes (KSourceTransport.originalPresentation H).encoding (presentation H R).encoding
    (FamilyAnswerTransport.recover (coefficients H R) (KSourceTransport.originalCoefficient H)) :=
  FamilyAnswerTransport.computes _ _
    (OriginalFamily.coefficient_algebraic (transformed H R) (edges R))
    (OriginalFamily.coefficient_algebraic H KSourceTransport.equalityEdges)

def controlled : LengthControlledOracleReduction
    (inputEncoding (r:=r) (b:=b)) (presentation H R).encoding
    (inputEncoding (r:=r) (b:=b)) (KSourceTransport.originalPresentation H).encoding
    (value H R) (KSourceTransport.originalValue H) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (b:=b))) (recover H R)
    ((OriginalFamily.tables H KSourceTransport.equalityEdges).outputBound
      (KSourceTransport.originalPresentation H)) (value H R) (fun q=>
        (FamilyAnswerTransport.recover_exact (coefficients H R) (KSourceTransport.originalCoefficient H)
          (value H R q) (KSourceTransport.originalValue H q) (value_exact H R q).symm).symm)

def table (i : Fin r) : Signature (field H R) (b i.val) :=
  fun x=>(presentation H R).decode ((tables H R).vertex i x)

theorem table_value (i : Fin r) (x : Fin (b i.val)→Bool) :
    (table H R i x : AlgebraicComplex)=R.symm.action (H i) x :=
  familyCoordinates_spec (coefficients H R)
    (OriginalFamily.coefficient_algebraic (transformed H R) (edges R)) (.inl ⟨i,x⟩)

theorem edge_value (i : Fin 1) (p q : Bool) :
    ((presentation H R).decode ((tables H R).edge i p q) : AlgebraicComplex)=C.gram R.matrix p q :=
  familyCoordinates_spec (coefficients H R)
    (OriginalFamily.coefficient_algebraic (transformed H R) (edges R)) (.inr (i,p,q))

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin r=>
  RingHomRealization.mapAny (field H R).subtype (⟨b i.val,table H R i⟩ : AnySignature (field H R))

theorem table_literal (i : Fin r) :
    RingHomRealization.mapAny (field H R).subtype (⟨b i.val,table H R i⟩ : AnySignature (field H R))=
      ⟨b i.val,R.symm.action (H i)⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (b i.val)=>(⟨b i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (table_value H R i))

theorem family_exact : family H R=familyAction R.symm (UniversalPairReduction.FiniteFamily.family H) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨b i.val,H i⟩,⟨i,rfl⟩,(table_literal H R i).symm⟩
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    exact ⟨i,table_literal H R i⟩

theorem ghz_literal (j : Fin r)
    (literal : (⟨b j.val,H j⟩ : AnySignature AlgebraicComplex)=⟨3,C.ghz R.matrix⟩) :
    RingHomRealization.mapAny (field H R).subtype (⟨b j.val,table H R j⟩ : AnySignature (field H R))=
      ⟨3,C.eq3⟩ := by
  refine (table_literal H R j).trans ?_
  have h := congrArg (fun f : AnySignature AlgebraicComplex=>
    (⟨f.1,R.symm.action f.2⟩ : AnySignature AlgebraicComplex)) literal
  exact h.trans (congrArg (fun f : Signature AlgebraicComplex 3=>(⟨3,f⟩ : AnySignature AlgebraicComplex))
    (C.inverse_ghz R.matrix R.inverse R.inverse_matrix))

theorem pin_literal (j : Fin r)
    (literal : (⟨b j.val,H j⟩ : AnySignature AlgebraicComplex)=⟨1,C.pin false⟩) :
    RingHomRealization.mapAny (field H R).subtype (⟨b j.val,table H R j⟩ : AnySignature (field H R))=
      ⟨1,fun x=>R.inverse (x 0) false⟩ := by
  refine (table_literal H R j).trans ?_
  have h := congrArg (fun f : AnySignature AlgebraicComplex=>
    (⟨f.1,R.symm.action f.2⟩ : AnySignature AlgebraicComplex)) literal
  exact h.trans (congrArg (fun f : Signature AlgebraicComplex 1=>(⟨1,f⟩ : AnySignature AlgebraicComplex))
    (GlobalCloseCompletionSymmetricGHZCoordinates.right_pin R.inverse))

section Original
variable {s degree : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
variable (L : IntermediateField ℚ AlgebraicComplex)
local instance : Algebra ℚ L := L.algebra'
variable (F : FixedField L degree) (S : (i : Fin r)→Signature L (b i.val))
variable (back : LengthControlledOracleReduction
    (inputEncoding (r:=r) (b:=b)) F.encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables F S).evaluate F) (OriginalForestSource.value G))

def toOriginal : LengthControlledOracleReduction
    (inputEncoding (r:=r) (b:=b))
      (presentation (GlobalCloseCompletionUnaryOrdinaryFieldCodec.ambient L S) R).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value (GlobalCloseCompletionUnaryOrdinaryFieldCodec.ambient L S) R) (OriginalForestSource.value G) :=
  Programme.compose (controlled (GlobalCloseCompletionUnaryOrdinaryFieldCodec.ambient L S) R)
    (Programme.compose (GlobalCloseCompletionUnaryOrdinaryFieldCodec.controlled L F S) back)


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionSymmetricGHZSource
end
