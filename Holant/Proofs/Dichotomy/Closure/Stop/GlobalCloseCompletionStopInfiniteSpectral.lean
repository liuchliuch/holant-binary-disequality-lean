import Holant.Proofs.BinaryInterpolation.UnifiedSource
import Holant.Proofs.Dichotomy.Retained.StableHigherCurrentFamilyTransport

/-! Exact spectral extraction from an actual infinite-order stopped binary at
an arbitrary current palette. The old binary and every old coefficient are
faithfully embedded; the rank-one pencil and its two nonzero unary factors
are produced internally. H is a new interpolation-accessible source label,
never asserted to be a gadget in the old family. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteSpectral
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
open Holant.Complexity.BinaryInterpolation Holant.Complexity.UniversalPairReduction
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure hiding binarySignature
open Holant.LocalDrafts.BinaryInterpolation Holant.LocalDrafts.MainChain
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
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

abbrev mapped := StableHigherCurrentPurePinsCore.mapped G P
abbrev embedding := ClosureSourceRows.embedding G
abbrev mappedBinary := B.map (embedding G)

theorem family_eq : RingHomRealization.mapFamily (embedding G) P.family=
    UnifiedSource.gamma (mapped G P) := by
  ext f
  constructor
  · rintro ⟨g,⟨i,rfl⟩,rfl⟩
    exact ⟨i,rfl⟩
  · rintro ⟨i,rfl⟩
    exact ⟨⟨P.arity i.val,P.table i⟩,⟨i,rfl⟩,rfl⟩

include actual in
theorem mapped_actual : ActualNonsingular (UnifiedSource.gamma (mapped G P)) (mappedBinary G B) := by
  refine ⟨?_,?_⟩
  · rw [←family_eq]
    exact RingHomRealization.realizes_map (embedding G) actual.1
  · have det : Matrix.det (mappedBinary G B)=embedding G (Matrix.det B) := by
      rw [det_entries,det_entries]
      simp [mappedBinary,Matrix.map_apply]
    rw [det]
    exact (map_ne_zero (embedding G)).mpr actual.2

theorem mapped_transfer : (transfer B).map (embedding G)=transfer (mappedBinary G B) := by
  have hX : (X : Binary (K:=OI.K G)).map (embedding G)=X := by
    ext i j
    cases i <;> cases j <;> simp [X,Signature.disequality]
  change (B*X).map (embedding G)=mappedBinary G B*X
  rw [Matrix.map_mul,hX]

include infinite in
theorem mapped_infinite : ¬ProjectivelyFinite (transfer (mappedBinary G B)) := by
  rw [←mapped_transfer]
  exact fun h=>infinite ((SourceTransport.projectivelyFinite_map_iff (embedding G) (transfer B)).mp h)

include actual in
theorem mapped_nonzero : mappedBinary G B≠0 := by
  intro zero
  exact (mapped_actual G P B actual).2 (by simp [zero])

def spectralMacro := Classical.choose (UnifiedSource.infinite_case (mapped G P) (mappedBinary G B)
  (mapped_nonzero G P B actual) (mapped_actual G P B actual).1
  (UnifiedSource.transfer_nonsingular _ (mapped_actual G P B actual).2) (mapped_infinite G B infinite))
def pencil := Classical.choose (Classical.choose_spec
  (UnifiedSource.infinite_case (mapped G P) (mappedBinary G B)
    (mapped_nonzero G P B actual) (mapped_actual G P B actual).1
    (UnifiedSource.transfer_nonsingular _ (mapped_actual G P B actual).2) (mapped_infinite G B infinite)))

abbrev H (i j : Bool) : AlgebraicComplex :=
  ⟨(pencil G P B actual infinite).H i j,(pencil G P B actual infinite).H_algebraic i j |>.isIntegral⟩

theorem H_map : SourceTransport.binary (H G P B actual infinite)=(pencil G P B actual infinite).H := rfl

theorem H_nonzero : H G P B actual infinite≠0 := by
  intro zero
  apply (pencil G P B actual infinite).H_nonzero
  ext i j
  exact congrArg (fun A : Binary (K:=AlgebraicComplex)=>(A i j : ℂ)) zero

theorem H_det : Matrix.det (H G P B actual infinite)=0 := by
  have hd : Matrix.det (pencil G P B actual infinite).H=0 := by
    by_contra hn
    have hr := Matrix.rank_of_det_ne_zero hn
    rw [(pencil G P B actual infinite).H_rank] at hr
    norm_num at hr
  apply SourceTransport.inclusion.injective
  rw [←SourceTransport.determinant_map,H_map,hd,map_zero]

structure Factors where
  left : Bool→AlgebraicComplex
  right : Bool→AlgebraicComplex
  left_nonzero : left≠0
  right_nonzero : right≠0
  equation : H G P B actual infinite=Matrix.vecMulVec left right

def factors : Factors G P B actual infinite := Classical.choice (by
  obtain ⟨u,v,hu,hv,he⟩ := singular_binary_factors (H G P B actual infinite)
    (H_nonzero G P B actual infinite) (H_det G P B actual infinite)
  exact ⟨⟨u,v,hu,hv,he⟩⟩)

abbrev adjoined := BinaryFamily.signatures (mapped G P) (H G P B actual infinite)

private theorem signature_pair_eq {m n : ℕ} (hn : m=n)
    (f : Signature AlgebraicComplex m) (g : Signature AlgebraicComplex n)
    (hv : ∀z,f z=g (fun i=>z (Fin.cast hn.symm i))) :
    (⟨m,f⟩ : AnySignature AlgebraicComplex)=⟨n,g⟩ := by
  cases hn
  exact congrArg (Sigma.mk m) (funext hv)

theorem adjoined_old (i : Fin P.count) :
    (⟨extendedArity P.count P.arity i.val,adjoined G P B actual infinite ⟨i.val,by omega⟩⟩ :
      AnySignature AlgebraicComplex)=⟨P.arity i.val,mapped G P i⟩ := by
  apply signature_pair_eq (by simp [extendedArity,i.isLt])
  intro z
  simp [adjoined,BinaryFamily.signatures,i.isLt]

theorem adjoined_new :
    (⟨extendedArity P.count P.arity P.count,adjoined G P B actual infinite ⟨P.count,by omega⟩⟩ :
      AnySignature AlgebraicComplex)=⟨2,binarySignature (H G P B actual infinite)⟩ := by
  apply signature_pair_eq (by simp [extendedArity])
  intro z
  simp [adjoined,BinaryFamily.signatures,Chains.binarySignature,binarySignature]

theorem adjoined_family : UnifiedSource.gamma (adjoined G P B actual infinite)=
    UnifiedSource.gamma (mapped G P) ∪ {⟨2,binarySignature (H G P B actual infinite)⟩} := by
  ext f
  constructor
  · rintro ⟨i,rfl⟩
    by_cases hi : i.val<P.count
    · exact Or.inl ⟨⟨i.val,hi⟩,(adjoined_old G P B actual infinite ⟨i.val,hi⟩).symm⟩
    · have eq : i=⟨P.count,by omega⟩ := Fin.ext (by change i.val=P.count; have := i.isLt; omega)
      exact Or.inr (by rw [eq]; exact adjoined_new G P B actual infinite)
  · rintro (⟨i,rfl⟩|he)
    · exact ⟨⟨i.val,by omega⟩,adjoined_old G P B actual infinite i⟩
    · exact ⟨⟨P.count,by omega⟩,(adjoined_new G P B actual infinite).trans he.symm⟩

theorem outer_in_adjoined : Gadget.Realizes (UnifiedSource.gamma (adjoined G P B actual infinite))
    .disequality (SingularExtraction.outerSignature (factors G P B actual infinite).left
      (factors G P B actual infinite).right) := by
  have h := Gadget.realizes_of_mem (UnifiedSource.gamma (adjoined G P B actual infinite)) .disequality
    (binarySignature (H G P B actual infinite)) ⟨⟨P.count,by omega⟩,adjoined_new G P B actual infinite⟩
  have he : binarySignature (H G P B actual infinite)=SingularExtraction.outerSignature
      (factors G P B actual infinite).left (factors G P B actual infinite).right := by
    funext z
    exact congrFun₂ (factors G P B actual infinite).equation (z 0) (z 1)
  rwa [he] at h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionStopInfiniteSpectral
end
