import Holant.Proofs.Dichotomy.Closure.Stop.GlobalCloseCompletionStopInfiniteField

/-! A complete actual two-unary supply at every infinite structural stop.
The new finite source contains all old current rows, the chosen rank-one H,
and its exact two nonzero unary factors. Singular extraction is inlined into
length-controlled spectral interpolation and the SAME original-G programme.
This is actual source access, not an unconditional hardness classification. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteSource
open Computability Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation Holant.Complexity.UniversalPairReduction
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionStopInfiniteSpectral
namespace SC
export SingularExtraction.Composition.SourceCodec (signatures field presentation value value_exact)
end SC
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s : ℕ} {a : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (a i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G)
variable (B : Binary (K:=OI.K G)) (actual : ActualNonsingular P.family B)
variable (infinite : ¬ProjectivelyFinite (transfer B))

theorem mapped_identity : RetainsIdentity (UnifiedSource.gamma (mapped G P)) := by
  obtain ⟨i,hi⟩ := P.equality
  refine ⟨i,?_⟩
  change RingHomRealization.mapAny (embedding G) (⟨P.arity i.val,P.table i⟩ : AnySignature (OI.K G))=_
  refine (congrArg (RingHomRealization.mapAny (embedding G)) hi).trans ?_
  apply congrArg (fun f : Signature AlgebraicComplex 2=>(⟨2,f⟩ : AnySignature AlgebraicComplex))
  funext z
  cases h0 : z 0 <;> cases h1 : z 1 <;>
    simp [RingHomRealization.mapSignature,binarySignature,
      Holant.Certificates.MatchingContractionClosure.binarySignature,
      Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,Signature.equality,h0,h1]

theorem adjoined_identity : RetainsIdentity (UnifiedSource.gamma (adjoined G P B actual infinite)) := by
  rw [RetainsIdentity,adjoined_family]
  exact Or.inl (mapped_identity G P)

theorem two_sided : ¬CommonOneSided (UnifiedSource.gamma (adjoined G P B actual infinite)) := by
  rintro (h|h)
  · have hh := h ⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩
      (adjoined_identity G P B actual infinite) (fun _=>false)
      (by simp [Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,Signature.equality])
    norm_num [Holant.charge,Holant.weight] at hh
  · have hh := h ⟨2,Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature⟩
      (adjoined_identity G P B actual infinite) (fun _=>true)
      (by simp [Holant.OpenNetworkComposition.OrdinaryNormalization.identitySignature,Signature.equality])
    norm_num [Holant.charge,Holant.weight] at hh

abbrev left := (factors G P B actual infinite).left
abbrev right := (factors G P B actual infinite).right
abbrev count := (P.count+1)+2
abbrev arity := SingularExtraction.Tables.adjoinedArity (P.count+1)
  (extendedArity P.count P.arity) 1 1
abbrev table := SC.signatures (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite)
abbrev field := SC.field (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite)
abbrev presentation := SC.presentation (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite)
abbrev value := SC.value (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite)
abbrev inputEncoding := RawClosedNetwork.validatedEncoding (count G P) 1 (arity G P)

private theorem signature_pair_eq {m n : ℕ} (hn : m=n)
    (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (hv : ∀z,f z=g (fun i=>z (Fin.cast hn.symm i))) :
    (⟨m,f⟩ : AnySignature AlgebraicComplex)=⟨n,g⟩ := by
  cases hn
  exact congrArg (Sigma.mk m) (funext hv)

private theorem unaryPower_sigma (u : Bool→AlgebraicComplex) (n : ℕ) (hn : n=1) :
    (⟨n,Signature.unaryPower u n⟩ : AnySignature AlgebraicComplex)=⟨1,fun z=>u (z 0)⟩ := by
  subst n
  congr 1
  funext z
  simp [Signature.unaryPower]

theorem old_adjoined_literal (i : Fin (P.count+1)) :
    (⟨arity G P i.val,table G P B actual infinite ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨extendedArity P.count P.arity i.val,adjoined G P B actual infinite i⟩ := by
  have ha : arity G P i.val=extendedArity P.count P.arity i.val := by
    simp [arity,SingularExtraction.Tables.adjoinedArity,show i.val≠P.count+1 by omega,
      show i.val≠(P.count+1)+1 by omega]
  apply signature_pair_eq ha
  exact SingularExtraction.Tables.typed_old (adjoined G P B actual infinite)
    (left G P B actual infinite) (right G P B actual infinite) i ha

theorem old_literal (i : Fin P.count) :
    (⟨arity G P i.val,table G P B actual infinite ⟨i.val,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨P.arity i.val,mapped G P i⟩ :=
  (old_adjoined_literal G P B actual infinite ⟨i.val,by omega⟩).trans
    (adjoined_old G P B actual infinite i)

theorem left_literal :
    (⟨arity G P (P.count+1),table G P B actual infinite ⟨P.count+1,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨1,fun z=>left G P B actual infinite (z 0)⟩ := by
  have h := funext (SingularExtraction.Tables.typed_left (A:=arity G P)
    (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite))
  exact (congrArg (fun f : Signature AlgebraicComplex (arity G P (P.count+1))=>
    (⟨_,f⟩ : AnySignature AlgebraicComplex)) h).trans
      (unaryPower_sigma _ _ (by simp [arity,SingularExtraction.Tables.adjoinedArity]))

theorem right_literal :
    (⟨arity G P ((P.count+1)+1),table G P B actual infinite ⟨(P.count+1)+1,by omega⟩⟩ : AnySignature AlgebraicComplex)=
      ⟨1,fun z=>right G P B actual infinite (z 0)⟩ := by
  have h := funext (SingularExtraction.Tables.typed_right (A:=arity G P)
    (adjoined G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite))
  exact (congrArg (fun f : Signature AlgebraicComplex (arity G P ((P.count+1)+1))=>
    (⟨_,f⟩ : AnySignature AlgebraicComplex)) h).trans
      (unaryPower_sigma _ _ (by simp [arity,SingularExtraction.Tables.adjoinedArity]))

theorem left_nonzero : (fun z : Fin 1→Bool=>left G P B actual infinite (z 0))≠0 := by
  intro zero
  apply (factors G P B actual infinite).left_nonzero
  funext b
  exact congrFun zero (fun _=>b)

theorem right_nonzero : (fun z : Fin 1→Bool=>right G P B actual infinite (z 0))≠0 := by
  intro zero
  apply (factors G P B actual infinite).right_nonzero
  funext b
  exact congrFun zero (fun _=>b)

/-- Every stage is a concrete constructed length-controlled caller. No
unary oracle, future compiler or arbitrary query-safety proof is an input. -/
def toOriginal : LengthControlledOracleReduction
    (inputEncoding G P) (presentation G P B actual infinite).encoding
    (OriginalForestSource.inputEncoding (s:=s) (arity:=a)) (OriginalForestSource.presentation G).encoding
    (value G P B actual infinite) (OriginalForestSource.value G) :=
  Programme.compose
    (SingularExtraction.Composition.SourceEndpoint.controlled (adjoined G P B actual infinite)
      (two_sided G P B actual infinite) (left G P B actual infinite) (right G P B actual infinite)
      (factors G P B actual infinite).left_nonzero (factors G P B actual infinite).right_nonzero
      (outer_in_adjoined G P B actual infinite))
    (GlobalCloseCompletionStopInfiniteField.toOriginal G P B actual infinite)

def physical := PhysicalProgramme.ofControlled (toOriginal G P B actual infinite)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteSource
end
