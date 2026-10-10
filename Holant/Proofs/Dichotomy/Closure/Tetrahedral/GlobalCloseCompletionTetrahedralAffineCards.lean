import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicCards
import Holant.Certificates.TetrahedralAffine.Binaries
import Holant.Platonic.StabilizerShortening.AffineTools

/-! Affinity of actual current tetrahedral matching cards at every arity.
The finite binary affine witnesses are combined on the literal matching
ports. Scalar saturation is resolved through its actual binary witness. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralAffineCards
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

 theorem affine_of_complex {n : ℕ} (f : Signature AlgebraicComplex n)
    (affine : ComplexAffine (fun x=>(f x : ℂ))) : Affine f := by
  classical
  by_cases zero : f=0
  · rw [zero]
    exact affine_zero n
  obtain ⟨x,hx⟩ : ∃x,f x≠0 := Function.ne_iff.mp zero
  obtain ⟨c,g,hg,he⟩ := affine
  have hgx : (g x : ℂ)≠0 := by
    intro hz
    have h := he x
    rw [hz,mul_zero] at h
    exact hx (Subtype.val_injective h)
  have hc : c=(f x : ℂ)/(g x : ℂ) := (eq_div_iff hgx).mpr (he x).symm
  have exactValue : f=(fun y=>(f x/g x)*g y) := by
    funext y
    apply Subtype.val_injective
    simpa only [IntermediateField.coe_mul,IntermediateField.coe_div,hc] using he y
  rw [exactValue]
  exact hg.scale (f x/g x)

 theorem direction_affine (U : Matrix Bool Bool ℂ) (member : groupDirection .tetrahedral U) :
    ComplexAffine (Holant.Projective.BoundedTorsion.binarySignature U) := by
  obtain ⟨c,hc,K,hK,he⟩ := groupDirection_right_X .tetrahedral member
  obtain ⟨r,rfl⟩ := Holant.Certificates.TetrahedralAffine.base_covered hK
  have hu : U=c • Holant.Certificates.TetrahedralAffine.complexBinary r := by
    rw [←multiply_X_twice U,he]
    ext a b
    simp [multiply,Holant.Certificates.TetrahedralAffine.complexBinary,mul_add,mul_assoc]
  refine ⟨c,Holant.Certificates.TetrahedralAffine.binary r,
    Holant.Certificates.TetrahedralAffine.binary_affine r,?_⟩
  intro x
  rw [hu]
  simp only [Holant.Projective.BoundedTorsion.binarySignature,Pi.smul_apply,smul_eq_mul,
    Holant.Certificates.TetrahedralAffine.coe_binary]

 theorem presentation_affine {n : ℕ} (M : Presentation ℂ (Fin n))
    (member : ∀e,groupDirection .tetrahedral (M.matrix e)) : ComplexAffine M.tensor := by
  classical
  have hf (e : Fin M.edges) : ComplexAffine
      (fun x : Word n => M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true)))) := by
    apply affine_complex_precompose (direction_affine _ (member e))
      (fun x => ![x (M.ports (e,false)),x (M.ports (e,true))])
    intro x y
    ext i
    fin_cases i <;> simp [AffinePhase.xor,origin]
  have product (S : Finset (Fin M.edges)) : ComplexAffine
      (fun x : Word n => ∏e∈S,M.matrix e (x (M.ports (e,false))) (x (M.ports (e,true)))) := by
    induction S using Finset.induction_on with
    | empty =>
        exact ⟨1,fun _=>1,affine_constant n 1,by intro x; simp⟩
    | @insert e S he ih =>
        simpa only [Finset.prod_insert he] using affine_complex_mul (hf e) ih
  exact (product Finset.univ).scale M.scalar

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL .tetrahedral)

include literal in
 theorem safe_direction (B : Matrix Bool Bool L) (safe : SafeBinary (actualTransfers F) B) :
    groupDirection .tetrahedral (B.map (complexEmbedding phi)) := by
  obtain ⟨C,hC,c,hc,he⟩ := safe
  have hB : B=c • C := by
    have ht := congrArg (fun A : Matrix Bool Bool L=>
      A*(Holant.Certificates.MatchingContractionClosure.X : Matrix Bool Bool L)) he
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using ht
  have h := GlobalCloseCompletionPlatonicCards.actual_direction phi F torsion
    .tetrahedral literal C hC
  rw [hB]
  have hm : (c • C).map (complexEmbedding phi)=complexEmbedding phi c • C.map (complexEmbedding phi) := by
    ext a b
    change (complexEmbedding phi) (c*C a b)=complexEmbedding phi c*complexEmbedding phi (C a b)
    exact map_mul _ _ _
  rw [hm]
  exact groupDirection_smul .tetrahedral h ((map_ne_zero _).mpr hc)

include literal in
 theorem matching_affine {n : ℕ} (f : Signature L n)
    (matching : MatchingOrZero (actualTransfers F) f) :
    ComplexAffine (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
  rcases matching with rfl | ⟨M,hM,_,rfl⟩
  · have hz : RingHomRealization.mapSignature (complexEmbedding phi) (0 : Signature L n)=0 := by
      funext x
      exact map_zero _
    rw [hz]
    exact affine_zero_complex
  let N : Presentation ℂ (Fin n) :=
    ⟨M.edges,M.ports,fun e=>(M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
  have hN : ∀e,groupDirection .tetrahedral (N.matrix e) :=
    fun e=>safe_direction phi F torsion literal (M.matrix e) (hM e)
  have he : RingHomRealization.mapSignature (complexEmbedding phi) M.tensor=N.tensor := by
    ext x
    simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]
  rw [he]
  exact presentation_affine N hN

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralAffineCards
end
