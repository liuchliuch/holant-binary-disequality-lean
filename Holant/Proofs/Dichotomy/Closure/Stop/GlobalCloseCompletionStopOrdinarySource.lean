import Holant.Proofs.Algorithms.KSourceTransport
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentPurePinsCore
import Holant.Proofs.Algorithms.QuaternaryOrdinaryCompanion
import Holant.Proofs.Dichotomy.Retained.StablePaletteTractability
import Holant.Tractable.Anchor

/-! The entire current native palette has a genuine ordinary K-coordinate
source before any Eq4 anchor or pins exist. The two generated coefficient
fields are kept distinct; exact ambient network semantics supply the real
fixed rational answer conversion before the saved original-G programme. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopOrdinarySource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open BinaryCompose FixedGadgetSubstitution
open Holant.LocalDrafts.MainChain Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.Hardness.FrozenFactorNormalization
namespace O
export Holant.LocalDrafts.Hardness.GeneralExtraction.GeneralOriginalTarget
  (coefficients coefficients_algebraic originalPresentation originalTables originalValue target_exact)
end O
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 100000
set_option maxRecDepth 16384
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)

abbrev native := StableHigherCurrentPurePinsCore.mapped G P
abbrev ordinary := KSourceTransport.ordinarySignatures (native G P)
abbrev coefficients := OriginalFamily.coefficient (ordinary G P) KSourceTransport.equalityEdges
abbrev field := familyField (coefficients G P)
local instance : Algebra ℚ (field G P) := (field G P).algebra'
abbrev presentation := OriginalFamily.presentation (ordinary G P) KSourceTransport.equalityEdges
abbrev oldTables := OriginalFamily.tables (ordinary G P) KSourceTransport.equalityEdges
abbrev value := OriginalFamily.value (ordinary G P) KSourceTransport.equalityEdges
abbrev inputEncoding := RawClosedNetwork.validatedEncoding P.count 1 P.arity

def table (i : Fin P.count) : Signature (field G P) (P.arity i.val) :=
  fun x=>(presentation G P).decode ((oldTables G P).vertex i x)

theorem table_value (i : Fin P.count) (x : Fin (P.arity i.val)→Bool) :
    (table G P i x : AlgebraicComplex)=ordinary G P i x :=
  familyCoordinates_spec (coefficients G P)
    (OriginalFamily.coefficient_algebraic (ordinary G P) KSourceTransport.equalityEdges) (.inl ⟨i,x⟩)

theorem table_literal (i : Fin P.count) :
    RingHomRealization.mapAny (field G P).subtype
      (⟨P.arity i.val,table G P i⟩ : AnySignature (field G P))=
      ⟨P.arity i.val,sourceKBasis.action (native G P i)⟩ :=
  congrArg (fun f : Signature AlgebraicComplex (P.arity i.val)=>(⟨P.arity i.val,f⟩ : AnySignature AlgebraicComplex))
    (funext (table_value G P i))

/-- Any actual retained row, with its original arity and port order, maps to
its precise source-K image in the same whole ordinary table. -/
theorem retained_literal {n : ℕ} (i : Fin P.count) (f : Signature (OI.K G) n)
    (literal : (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G))=⟨n,f⟩) :
    RingHomRealization.mapAny (field G P).subtype
      (⟨P.arity i.val,table G P i⟩ : AnySignature (field G P))=
      ⟨n,sourceKBasis.action (RingHomRealization.mapSignature
        (StableHigherCurrentPurePinsCore.embedding G).toRingHom f)⟩ :=
  (table_literal G P i).trans
    (congrArg (fun g : AnySignature AlgebraicComplex=>(⟨g.1,sourceKBasis.action g.2⟩ : AnySignature AlgebraicComplex))
      (congrArg (RingHomRealization.mapAny (StableHigherCurrentPurePinsCore.embedding G).toRingHom) literal))

theorem old_edge (i : Fin 1) (b c : Bool) :
    (presentation G P).decode ((oldTables G P).edge i b c)=Signature.equality b c := by
  apply Subtype.ext
  have h := familyCoordinates_spec (coefficients G P)
    (OriginalFamily.coefficient_algebraic (ordinary G P) KSourceTransport.equalityEdges) (.inr (i,b,c))
  exact h.trans (by cases b <;> cases c <;> simp [OriginalFamily.coefficient,KSourceTransport.equalityEdges,Signature.equality])

theorem tables_exact : QuaternaryOrdinaryCompanion.tables (presentation G P) (table G P)=oldTables G P := by
  unfold QuaternaryOrdinaryCompanion.tables
  congr 1
  · funext i x
    exact (presentation G P).decode.symm_apply_apply _
  · funext i b c
    apply (presentation G P).decode.injective
    rw [LinearEquiv.apply_symm_apply]
    exact (old_edge G P i b c).symm

abbrev nativeCoefficients := OriginalFamily.coefficient (native G P) KSourceTransport.nativeEdges
abbrev nativePresentation := OriginalFamily.presentation (native G P) KSourceTransport.nativeEdges
abbrev nativeValue := OriginalFamily.value (native G P) KSourceTransport.nativeEdges

def recoverComputes : Computes (O.originalPresentation (native G P)).encoding
    (nativePresentation G P).encoding
    (FamilyAnswerTransport.recover (nativeCoefficients G P) (O.coefficients (native G P))) :=
  FamilyAnswerTransport.computes (nativeCoefficients G P) (O.coefficients (native G P))
    (OriginalFamily.coefficient_algebraic (native G P) KSourceTransport.nativeEdges)
    (O.coefficients_algebraic (native G P))

theorem recover_value (r : ExactSignatureTables.Input P.count 1 P.arity) :
    nativeValue G P r=FamilyAnswerTransport.recover (nativeCoefficients G P)
      (O.coefficients (native G P)) (O.originalValue (native G P) r) := by
  symm
  apply FamilyAnswerTransport.recover_exact
  rw [O.target_exact,OriginalFamily.value_exact]

def nativeCodec : LengthControlledOracleReduction (inputEncoding G P) (nativePresentation G P).encoding
    (inputEncoding G P) (O.originalPresentation (native G P)).encoding
    (nativeValue G P) (O.originalValue (native G P)) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding G P)) (recoverComputes G P)
    ((O.originalTables (native G P)).outputBound (O.originalPresentation (native G P)))
    (nativeValue G P) (recover_value G P)

def ordinaryToNative : LengthControlledOracleReduction
    (inputEncoding G P) (presentation G P).encoding
    (inputEncoding G P) (nativePresentation G P).encoding (value G P) (nativeValue G P) := by
  have R := KSourceTransport.toNative (ordinary G P)
  change LengthControlledOracleReduction (inputEncoding G P) (presentation G P).encoding
    (inputEncoding G P)
    (OriginalFamily.presentation (KSourceTransport.nativeSignatures (ordinary G P)) KSourceTransport.nativeEdges).encoding
    (value G P) (OriginalFamily.value (KSourceTransport.nativeSignatures (ordinary G P)) KSourceTransport.nativeEdges) at R
  rw [KSourceTransport.native_ordinary] at R
  exact R

/-- Every original current row, arbitrary multiplicity and ordered port is
retained. No anchor, target interpolation or query-safety premise is supplied. -/
def toOriginal : LengthControlledOracleReduction (inputEncoding G P) (presentation G P).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation G P) (table G P)).evaluate (presentation G P))
    (OriginalForestSource.value G) := by
  rw [tables_exact]
  exact Programme.compose (ordinaryToNative G P)
    (Programme.compose (nativeCodec G P)
      (Programme.compose (OriginalLCodec.fromCoefficient
        (StableHigherCurrentPurePinsCore.embedding G) P.table) P.toOriginal.controlled))

def family : SignatureFamily AlgebraicComplex := Set.range fun i : Fin P.count=>
  RingHomRealization.mapAny (field G P).subtype (⟨P.arity i.val,table G P i⟩ : AnySignature (field G P))

theorem family_exact : family G P=familyAction sourceKBasis
    (UniversalPairReduction.FiniteFamily.family (native G P)) := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    refine ⟨⟨P.arity i.val,native G P i⟩,⟨i,rfl⟩,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (P.arity i.val)=>(⟨P.arity i.val,g⟩ : AnySignature AlgebraicComplex))
    exact (funext (table_value G P i)).symm
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    refine ⟨i,?_⟩
    apply congrArg (fun g : Signature AlgebraicComplex (P.arity i.val)=>(⟨P.arity i.val,g⟩ : AnySignature AlgebraicComplex))
    exact funext (table_value G P i)

theorem native_family : UniversalPairReduction.FiniteFamily.family (native G P)=
    CurrentFrontierClosure.currentFamily G P := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩
  · rintro ⟨f,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩

theorem z_member : (⟨2,zAnchor⟩ : AnySignature AlgebraicComplex)∈family G P := by
  rw [family_exact]
  have hI : (⟨2,kernelSignature Signature.equality⟩ : AnySignature AlgebraicComplex)∈
      UniversalPairReduction.FiniteFamily.family (native G P) := by
    obtain ⟨i,hi⟩ := P.equality
    refine ⟨i,?_⟩
    have h := congrArg (RingHomRealization.mapAny (StableHigherCurrentPurePinsCore.embedding G).toRingHom) hi
    refine h.trans ?_
    apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
    funext x
    cases h0 : x 0 <;> cases h1 : x 1 <;>
      simp [RingHomRealization.mapSignature,Holant.Certificates.MatchingContractionClosure.binarySignature,
        kernelSignature,Signature.equality,h0,h1]
  refine ⟨⟨2,kernelSignature Signature.equality⟩,hI,?_⟩
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  rw [←sourceKBasis_symm_action_zAnchor,InvertibleKernel.action_symm_action]

/-- The literal retained identity becomes Z, so the full ordinary criterion
is equivalent to the current reduced criterion used by the actual evaluator. -/
theorem tract_iff_current : Tract (family G P) ↔
    TractX (familyAction sourceKBasis (CurrentFrontierClosure.currentFamily G P)) := by
  rw [tract_iff_tractX_of_zAnchor_mem (z_member G P),family_exact,native_family]

def originalComputes (tract : Tract (family G P)) :=
  StablePaletteTractability.originalComputes G P ((tract_iff_current G P).mp tract)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopOrdinarySource
end
