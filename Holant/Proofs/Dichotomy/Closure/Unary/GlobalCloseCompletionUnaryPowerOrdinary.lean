import Holant.Proofs.Dichotomy.Closure.Unary.GlobalCloseCompletionUnaryPowerNative

/-! Full ordinary source for extracting a unary from any actual nonzero
scalar tensor power of it. Exact inverse-K transport, residue grouping, both
coefficient-codec conversions and the return to ordinary coordinates are
composed before exposing the literal old table and new unary. No Eq4,
common-one-sided exclusion or independent-unary hardness premise is used. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerOrdinary
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity FixedGadgetSubstitution
open BinaryCompose Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.LocalDrafts.RemoteWork.HardnessChainV1
open Holant.LocalDrafts.BinaryInterpolation.SingularExtraction
namespace P
export GlobalCloseCompletionUnaryPowerNative (native vector power nativeSource)
end P
namespace S
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.SourceCodec
  (signatures field presentation encoding value)
end S
namespace O
export Holant.LocalDrafts.BinaryInterpolation.SingularExtraction.Composition.OriginalField
  (coefficient algebraic presentation encoding value value_exact)
end O
namespace U
export GlobalCloseCompletionUnaryNativeSource
  (field presentation table value tables_exact family ordinaryToNative nativeCodec retained_literal)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 16384
set_option Elab.async false
variable {r : ℕ} {b : ℕ→ℕ}
variable (H : (i : Fin r)→Signature AlgebraicComplex (b i.val))
abbrev inputEncoding := RawClosedNetwork.validatedEncoding r 1 b

def recoverComputes : Computes (KSourceTransport.nativePresentation H).encoding (O.encoding (P.native H))
    (FamilyAnswerTransport.recover (O.coefficient (P.native H)) (KSourceTransport.nativeCoefficient H)) :=
  FamilyAnswerTransport.computes _ _ (O.algebraic (P.native H))
    (OriginalFamily.coefficient_algebraic (P.native H) KSourceTransport.nativeEdges)

theorem recover_value (q : ExactSignatureTables.Input r 1 b) :
    O.value (P.native H) q=FamilyAnswerTransport.recover (O.coefficient (P.native H))
      (KSourceTransport.nativeCoefficient H) (KSourceTransport.nativeValue H q) := by
  symm
  apply FamilyAnswerTransport.recover_exact
  rw [O.value_exact,OriginalFamily.value_exact]
  rfl

def oldCodec : LengthControlledOracleReduction (inputEncoding (r:=r) (b:=b)) (O.encoding (P.native H))
    (inputEncoding (r:=r) (b:=b)) (KSourceTransport.nativePresentation H).encoding
    (O.value (P.native H)) (KSourceTransport.nativeValue H) :=
  controlledOneQueryOfEq (identityComputes (inputEncoding (r:=r) (b:=b))) (recoverComputes H)
    ((OriginalFamily.tables (P.native H) KSourceTransport.nativeEdges).outputBound
      (KSourceTransport.nativePresentation H)) (O.value (P.native H)) (recover_value H)

def oldOrdinary := Programme.compose (oldCodec H) (KSourceTransport.fromNative H)

variable {n : ℕ} (N : Network AlgebraicComplex n) (NL : Labelling N.shape r 1 b)
variable (exactN : LabelledNetwork.Exact H N NL) (ordinaryN : ∀e,N.edge e=Signature.equality)
variable (positive : 0<n) (u : Bool→AlgebraicComplex) (c : AlgebraicComplex) (nonzero : c≠0)
variable (form : N.denote=fun x=>c*Signature.unaryPower u n x)

abbrev nativeTable := S.signatures (P.native H) (P.vector u) (P.vector u)
abbrev arity := Tables.adjoinedArity r b 1 1
abbrev field := U.field (nativeTable H u)
abbrev presentation := U.presentation (nativeTable H u)
abbrev table := U.table (nativeTable H u)
abbrev family := U.family (nativeTable H u)

def nativeControlled := Programme.compose (P.nativeSource H N NL exactN ordinaryN positive u c nonzero form)
  (oldOrdinary H)

def controlled : LengthControlledOracleReduction
    (RawClosedNetwork.validatedEncoding (r+2) 1 (arity (r:=r) (b:=b))) (presentation H u).encoding
    (inputEncoding (r:=r) (b:=b)) (KSourceTransport.originalPresentation H).encoding
    ((QuaternaryOrdinaryCompanion.tables (presentation H u) (table H u)).evaluate (presentation H u))
    (KSourceTransport.originalValue H) := by
  rw [U.tables_exact]
  exact Programme.compose (U.ordinaryToNative (nativeTable H u))
    (Programme.compose (U.nativeCodec (nativeTable H u))
      (nativeControlled H N NL exactN ordinaryN positive u c nonzero form))

private theorem signature_pair_eq {m n : ℕ} (f : Signature AlgebraicComplex m)
    (g : Signature AlgebraicComplex n) (hn : m=n)
    (hv : ∀x,f x=g (fun i=>x (Fin.cast hn.symm i))) :
    (⟨m,f⟩ : AnySignature AlgebraicComplex)=⟨n,g⟩ := by
  cases hn
  exact congrArg (Sigma.mk m) (funext hv)

theorem native_old (i : Fin r) :
    (⟨arity (r:=r) (b:=b) i.val,nativeTable H u ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨b i.val,P.native H i⟩ := by
  have h : arity (r:=r) (b:=b) i.val=b i.val := by
    simp [arity,Tables.adjoinedArity,show i.val≠r by omega,show i.val≠r+1 by omega]
  apply signature_pair_eq _ _ h
  exact Tables.typed_old (P.native H) (P.vector u) (P.vector u) i h

theorem old_included : UniversalPairReduction.FiniteFamily.family H⊆family H u := by
  rintro f ⟨i,rfl⟩
  refine ⟨⟨i.val,by omega⟩,?_⟩
  have h := U.retained_literal (nativeTable H u) ⟨i.val,by omega⟩ (P.native H i) (native_old (n:=0) H u i)
  simpa only [P.native,KSourceTransport.nativeSignatures,InvertibleKernel.action_symm_action] using h

theorem vector_signature : (fun x : Fin 1→Bool=>P.vector u (x 0))=
    sourceKBasis.symm.action (fun x=>u (x 0)) := by
  funext x
  unfold InvertibleKernel.action Signature.coordinateAction
  rw [←(Equiv.funUnique (Fin 1) Bool).symm.sum_comp]
  simp [P.vector,InvertibleKernel.symm,Fin.prod_univ_one,Fintype.sum_bool]

theorem unary_member : (⟨1,fun x=>u (x 0)⟩ : AnySignature AlgebraicComplex)∈family H u := by
  have hn : arity (r:=r) (b:=b) r=1 := by simp [arity,Tables.adjoinedArity]
  have hv := funext (Tables.typed_left (A:=arity (r:=r) (b:=b)) (P.native H) (P.vector u) (P.vector u))
  have powerSigma (v : Bool→AlgebraicComplex) (k : ℕ) (hk : k=1) :
      (⟨k,Signature.unaryPower v k⟩ : AnySignature AlgebraicComplex)=⟨1,fun x=>v (x 0)⟩ := by
    subst k
    congr 1
    funext x
    simp [Signature.unaryPower]
  have literal : (⟨arity (r:=r) (b:=b) r,nativeTable H u ⟨r,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨1,fun x=>P.vector u (x 0)⟩ := by
    exact (congrArg (fun f : Signature AlgebraicComplex (arity (r:=r) (b:=b) r)=>
      (⟨_,f⟩ : AnySignature AlgebraicComplex)) hv).trans (powerSigma _ _ hn)
  refine ⟨⟨r,by omega⟩,?_⟩
  have h := U.retained_literal (nativeTable H u) ⟨r,by omega⟩ _ literal
  rw [vector_signature] at h
  simpa only [InvertibleKernel.action_symm_action] using h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionUnaryPowerOrdinary
end
