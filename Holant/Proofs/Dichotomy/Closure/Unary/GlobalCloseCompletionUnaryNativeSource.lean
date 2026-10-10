import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryDescentSource
import Holant.Proofs.Algorithms.KSourceTransport

/-! A generic finite native table with its genuine original-G source has an
ordinary source-K table in its actual coefficient field. The adapter does not
require or manufacture a retained Palette, an Eq4 anchor, or free pins. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNativeSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalTables originalValue target_exact)
end O
namespace D
export GlobalCloseCompletionUnaryDescentSource (ambient endpoint Outcome complete)
end D
namespace U
export GeneralOddNonisotropicFrame (norm)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s r : ℕ} {a b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))

abbrev ordinary := KSourceTransport.ordinarySignatures H
abbrev coefficients := OriginalFamily.coefficient (ordinary H) KSourceTransport.equalityEdges
abbrev field := familyField (coefficients H)
local instance : Algebra ℚ (field H) := (field H).algebra'
abbrev presentation := OriginalFamily.presentation (ordinary H) KSourceTransport.equalityEdges
abbrev oldTables := OriginalFamily.tables (ordinary H) KSourceTransport.equalityEdges
abbrev value := OriginalFamily.value (ordinary H) KSourceTransport.equalityEdges
abbrev inputEncoding := RawClosedNetwork.validatedEncoding r 1 b

def table (i : Fin r) : Signature (field H) (b i.val) :=
  fun x=>(presentation H).decode ((oldTables H).vertex i x)
theorem table_value (i : Fin r) (x : Fin (b i.val)→Bool) :
    (table H i x : AlgebraicComplex)=ordinary H i x :=
  familyCoordinates_spec (coefficients H)
    (OriginalFamily.coefficient_algebraic (ordinary H) KSourceTransport.equalityEdges) (.inl ⟨i,x⟩)

theorem table_literal (i : Fin r) :
    RingHomRealization.mapAny (field H).subtype (⟨b i.val,table H i⟩ : AnySignature (field H))=
      ⟨b i.val,sourceKBasis.action (H i)⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (b i.val)=>(⟨b i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (table_value H i))

theorem retained_literal {n : ℕ} (i : Fin r) (f : Signature AlgebraicComplex n)
    (literal : (⟨b i.val,H i⟩ : AnySignature AlgebraicComplex)=⟨n,f⟩) :
    RingHomRealization.mapAny (field H).subtype (⟨b i.val,table H i⟩ : AnySignature (field H))=
      ⟨n,sourceKBasis.action f⟩ :=
  (table_literal H i).trans
    (congrArg (fun g : AnySignature AlgebraicComplex=>(⟨g.1,sourceKBasis.action g.2⟩ : AnySignature AlgebraicComplex)) literal)

theorem old_edge (i : Fin 1) (p q : Bool) :
    (presentation H).decode ((oldTables H).edge i p q)=Signature.equality p q := by
  apply Subtype.ext
  have h := familyCoordinates_spec (coefficients H)
    (OriginalFamily.coefficient_algebraic (ordinary H) KSourceTransport.equalityEdges) (.inr (i,p,q))
  exact h.trans (by cases p <;> cases q <;> simp [OriginalFamily.coefficient,KSourceTransport.equalityEdges,Signature.equality])

theorem tables_exact : QuaternaryOrdinaryCompanion.tables (presentation H) (table H)=oldTables H := by
  unfold QuaternaryOrdinaryCompanion.tables
  congr 1
  · funext i x
    exact (presentation H).decode.symm_apply_apply _
  · funext i p q
    apply (presentation H).decode.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (old_edge H i p q).symm

abbrev nativeCoefficients := OriginalFamily.coefficient H KSourceTransport.nativeEdges
abbrev nativePresentation := OriginalFamily.presentation H KSourceTransport.nativeEdges
abbrev nativeValue := OriginalFamily.value H KSourceTransport.nativeEdges
def recoverComputes : Computes (O.originalPresentation H).encoding (nativePresentation H).encoding
    (FamilyAnswerTransport.recover (nativeCoefficients H) (O.coefficients H)) :=
  FamilyAnswerTransport.computes (nativeCoefficients H) (O.coefficients H)
    (OriginalFamily.coefficient_algebraic H KSourceTransport.nativeEdges) (O.coefficients_algebraic H)
theorem recover_value (q : ExactSignatureTables.Input r 1 b) :
    nativeValue H q=FamilyAnswerTransport.recover (nativeCoefficients H) (O.coefficients H) (O.originalValue H q) := by
  symm
  apply FamilyAnswerTransport.recover_exact
  rw [O.target_exact,OriginalFamily.value_exact]
def nativeCodec : LengthControlledOracleReduction (inputEncoding (r:=r) (b:=b)) (nativePresentation H).encoding
    (inputEncoding (r:=r) (b:=b)) (O.originalPresentation H).encoding (nativeValue H) (O.originalValue H) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (b:=b))) (recoverComputes H)
    ((O.originalTables H).outputBound (O.originalPresentation H)) (nativeValue H) (recover_value H)
def ordinaryToNative : LengthControlledOracleReduction
    (inputEncoding (r:=r) (b:=b)) (presentation H).encoding
    (inputEncoding (r:=r) (b:=b)) (nativePresentation H).encoding (value H) (nativeValue H) := by
  have R := KSourceTransport.toNative (ordinary H)
  change LengthControlledOracleReduction (inputEncoding (r:=r) (b:=b)) (presentation H).encoding
    (inputEncoding (r:=r) (b:=b))
    (OriginalFamily.presentation (KSourceTransport.nativeSignatures (ordinary H)) KSourceTransport.nativeEdges).encoding
    (value H) (OriginalFamily.value (KSourceTransport.nativeSignatures (ordinary H)) KSourceTransport.nativeEdges) at R
  rw [KSourceTransport.native_ordinary] at R
  exact R

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin r=>
  RingHomRealization.mapAny (field H).subtype (⟨b i.val,table H i⟩ : AnySignature (field H))
theorem family_exact : family H=familyAction sourceKBasis (UniversalPairReduction.FiniteFamily.family H) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨b i.val,H i⟩,⟨i,rfl⟩,(table_literal H i).symm⟩
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    exact ⟨i,table_literal H i⟩

section Original
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (back : LengthControlledOracleReduction
  (inputEncoding (r:=r) (b:=b)) (O.originalPresentation H).encoding
  (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
  (O.originalValue H) (OriginalForestSource.value G))

def toOriginal : LengthControlledOracleReduction (inputEncoding (r:=r) (b:=b)) (presentation H).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation H) (table H)).evaluate (presentation H))
    (OriginalForestSource.value G) := by
  rw [tables_exact]
  exact Programme.compose (ordinaryToNative H) (Programme.compose (nativeCodec H) back)

variable (i : Fin r) (u : Signature AlgebraicComplex 1)
variable (literal : (⟨b i.val,H i⟩ : AnySignature AlgebraicComplex)=⟨1,u⟩)
def unary : Signature (field H) 1 :=
  fun x=>table H i (fun j=>x (Fin.cast (congrArg Sigma.fst literal) j))
private theorem cast_pair {K : Type} {m n : ℕ} (h : m=n) (f : Signature K m) :
    (⟨m,f⟩ : AnySignature K)=⟨n,fun x=>f (fun j=>x (Fin.cast h j))⟩ := by cases h; rfl
theorem unary_literal : (⟨b i.val,table H i⟩ : AnySignature (field H))=⟨1,unary H i u literal⟩ :=
  cast_pair (congrArg Sigma.fst literal) (table H i)

theorem unary_mapped : (fun x=>(unary H i u literal x : AlgebraicComplex))=sourceKBasis.action u := by
  have h := (congrArg (RingHomRealization.mapAny (field H).subtype) (unary_literal H i u literal)).symm.trans
    (retained_literal H i u literal)
  exact eq_of_heq (Sigma.mk.inj_iff.mp h).2

theorem unary_nonzero (nonzero : u≠0) : unary H i u literal≠0 := by
  intro zero
  apply nonzero
  apply (Conformal.action_eq_zero_iff sourceKBasis u).mp
  rw [←unary_mapped H i u literal,zero]
  funext x
  exact map_zero (field H).subtype

def graph : Network (field H) 1 := Network.corolla (unary H i u literal)
def labels : Labelling (graph H i u literal).shape r 1 b where
  vertex _ := i
  vertex_arity _ := congrArg Sigma.fst literal
  edge e := Fin.elim0 e
theorem exact : LabelledNetwork.Exact (table H) (graph H i u literal) (labels H i u literal) :=
  fun _=>unary_literal H i u literal
theorem ordinary_graph : ∀e,(graph H i u literal).edge e=Signature.equality := fun e=>Fin.elim0 e

abbrev Descent (hu : U.norm (graph H i u literal).denote≠0) (negative : ¬Tract (family H)) :=
  D.Outcome (field H) (table H) (graph H i u literal) G
    (D.endpoint (field H) (table H) (graph H i u literal) (labels H i u literal)
      (exact H i u literal) (ordinary_graph H i u literal) hu negative)
def descend (hu : U.norm (graph H i u literal).denote≠0) (negative : ¬Tract (family H)) :
    Descent H G i u literal hu negative :=
  D.complete (field H) (table H) (graph H i u literal) (labels H i u literal)
    (exact H i u literal) (ordinary_graph H i u literal) hu negative G (presentation H) (toOriginal H G back)


end Original
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryNativeSource
end
