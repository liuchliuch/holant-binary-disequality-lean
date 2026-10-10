import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicRepresentatives
import Holant.Proofs.Closure.ClosureSourceRowsMatching

/-! Every literal Platonic coefficient test is a scalar-rescaled actual
current raw card. Full source realizability and its exact nonzero multiplier
are retained, including zero tests; no preserved-cone premise is imported. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option Elab.async false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicCards
open Holant Holant.Tractable Holant.Marked
open Holant.Projective.BoundedTorsion Holant.Projective.FiniteGroupFacts
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

private theorem mul_eq_multiply (A B : Matrix Bool Bool ℂ) : A*B=multiply A B := by
  ext u v
  simp [Matrix.mul_apply,multiply,add_comm]

theorem model_matrix_iff (p : PlatonicModel) (U : ComplexGL) :
    pglMk ℂ U∈modelPGL p ↔ groupDirection p (U : ComplexMatrix) := by
  constructor
  · rintro ⟨V,hV,he⟩
    obtain ⟨c,hc,he⟩ := projectiveClass_eq_iff.mp
      (pglMk_eq_iff_projectiveClass_eq.mp he.symm)
    rw [he]
    exact groupDirection_smul p hV hc
  · intro hU
    exact ⟨U,hU,rfl⟩

theorem x_direction (p : PlatonicModel) :
    groupDirection p (Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix) := by
  have h := groupDirection_right_X p (model_projectiveMatrixGroup p).one_mem
  have hx : Holant.Certificates.MatchingProductBridge.X =
      (Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix) := rfl
  rw [hx] at h
  simpa only [←mul_eq_multiply,Matrix.one_mul] using h

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (p : PlatonicModel) (literal : group phi F torsion=modelPGL p)

include literal in
theorem actual_direction (B : Matrix Bool Bool L) (actual : ActualNonsingular F B) :
    groupDirection p (B.map (complexEmbedding phi)) := by
  let A := B.map (complexEmbedding phi)
  have ha : ActualNonsingular (mapFamily (complexEmbedding phi) F) A :=
    ClosureFieldBridgeGroups.actual_map (complexEmbedding phi) actual
  have hd : (transfer A).det≠0 := by
    rw [transfer,Matrix.det_mul]
    exact mul_ne_zero ha.2 det_X_ne_zero
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero (transfer A) hd
  have hv : pglMk ℂ V∈group phi F torsion :=
    ⟨V,⟨A,ha,1,one_ne_zero,(one_smul ℂ _).symm⟩,rfl⟩
  rw [literal] at hv
  have hg := (model_matrix_iff p V).mp hv
  change groupDirection p (transfer A) at hg
  apply (groupDirection_right_X_iff p A).mp
  have hx : (Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix)=
      Holant.Certificates.MatchingProductBridge.X := rfl
  simpa only [transfer,hx,mul_eq_multiply] using hg

include literal in
theorem kernel_alignment (K : ComplexMatrix) (member : groupDirection p K) :
    ∃ j : completeGroup F torsion, ∃ c : ℂ, c≠0 ∧
      (actualRepresentative F torsion j).map (complexEmbedding phi)=c • nativePair K := by
  have hd := groupDirection_mul p (x_direction p) member
  let V := Matrix.GeneralLinearGroup.mkOfDetNeZero
    ((Holant.Certificates.MatchingContractionClosure.X : ComplexMatrix)*K)
    (groupDirection_det_ne_zero p hd)
  have hv : pglMk ℂ V∈group phi F torsion := by
    rw [literal]
    exact (model_matrix_iff p V).mpr hd
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionPlatonicRepresentatives.representative_for_transfer
    phi F torsion V hv
  exact ⟨j,c,hc,he⟩

def coefficientCard (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4))
    (K : ComplexMatrix) : ComplexMatrix :=
  fun u v => ∑ a : Bool, ∑ b : Bool, K a b * q (fun i=>![a,b,u,v] (e.symm i))

def LiteralDeck (p : PlatonicModel) (q : Signature ℂ 4) : Prop :=
  ∀ e K, groupDirection p K → coefficientCard q e K=0 ∨ groupDirection p (coefficientCard q e K)

theorem coefficientCard_scale (q : Signature ℂ 4) (e : Equiv.Perm (Fin 4))
    (K : ComplexMatrix) (c : ℂ) : coefficientCard q e (c • K)=c • coefficientCard q e K := by
  ext u v
  simp [coefficientCard,mul_add,mul_assoc]

omit [NumberField L] in
theorem mapped_card (psi : L→+*ℂ) (q : Signature L 4)
    (e : Equiv.Perm (Fin 4)) (B : Matrix Bool Bool L) :
    (binaryMatrix (ClosureSourceRows.originalOrderedCard q e B)).map psi=
      coefficientCard (RingHomRealization.mapSignature psi q) e (nativePair (B.map psi)) := by
  ext u v
  have hwords (a b : Bool) :
      (Fin.cons a (Fin.cons b (![u,v] : Fin 2→Bool)) : Fin 4→Bool)=![a,b,u,v] := by
    ext i
    fin_cases i <;> rfl
  simp only [ClosureSourceRows.originalOrderedCard,binaryMatrix,Matrix.map_apply,
    Signature.contract,Tensor.reindex,map_sum,map_mul,hwords,coefficientCard,RingHomRealization.mapSignature]
  apply Finset.sum_congr rfl
  intro a _
  apply Finset.sum_congr rfl
  intro b _
  congr 1
  exact congrArg psi (nativePair_apply B a b) |>.trans (nativePair_apply (B.map psi) a b).symm

variable {s : ℕ} {arity : ℕ→ℕ}
variable (G : (i : Fin s)→Signature AlgebraicComplex (arity i.val))
local instance : NumberField (OI.K G) := OI.numberField G
variable (P : Palette G) (tau : ResidualTorsion P.family)
variable (model : group (ClosureSourceRows.embedding G) P.family tau=modelPGL p)
variable (q : Signature (OI.K G) 4) (core : MinimumCore P.family)
variable (same : core.signature=⟨4,q⟩)
variable (stable : ∀f∈rawDeck P.family tau q,MatchingOrZero (actualTransfers P.family) f)

include model core same stable in
theorem current_literal_deck : LiteralDeck p
    (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) := by
  intro e K member
  obtain ⟨j,c,hc,he⟩ := kernel_alignment (ClosureSourceRows.embedding G) P.family tau p model K member
  let B := actualRepresentative P.family tau j
  have hb := actualRepresentative_actual P.family tau j
  have hpair : nativePair (B.map (complexEmbedding (ClosureSourceRows.embedding G)))=c • K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair K (!a) (!b)=c*K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hcard := mapped_card (complexEmbedding (ClosureSourceRows.embedding G)) q e B
  rw [hpair,coefficientCard_scale] at hcard
  rcases ClosureSourceRows.actualCard_actual_or_zero G P tau q stable core same e B hb with zero|actual
  · left
    have hz : c • coefficientCard (RingHomRealization.mapSignature (complexEmbedding (ClosureSourceRows.embedding G)) q) e K=0 := by
      rw [←hcard,zero]
      ext a b
      simp [binaryMatrix]
    exact (smul_eq_zero.mp hz).resolve_left hc
  · right
    have safe := actual_direction (ClosureSourceRows.embedding G) P.family tau p model _ actual
    rw [hcard] at safe
    have unscaled := groupDirection_smul p safe (inv_ne_zero hc)
    simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using unscaled


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionPlatonicCards
end
