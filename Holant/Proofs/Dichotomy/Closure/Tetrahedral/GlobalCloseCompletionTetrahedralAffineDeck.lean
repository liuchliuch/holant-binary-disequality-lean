import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralAffineCards
import Holant.Platonic.TetrahedralLocalization.OneStep
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralMarking

/-! Actual current internal-T primes with at least eight ports are affine
whenever every smaller raw card is affine. This form supports induction over
the real retained card factor trees after the six-port case has been closed.
The original-field representatives, ordered ports and multipliers are exact. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralAffineDeck
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.MatchingProductBridge
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.TetrahedralLocalization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL .tetrahedral)
variable {m : ℕ} (f : Signature L (m+2))
variable (stable : ∀g∈rawDeck F torsion f,Affine (RingHomRealization.mapSignature phi g))

include literal stable in
theorem pair_affine (p : (Bool ⊕ Fin m)≃Fin (m+2))
    (K : Matrix Bool Bool ℂ) (member : groupDirection .tetrahedral K) :
    ComplexAffine (pairCard p K (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionPlatonicCards.kernel_alignment
    phi F torsion .tetrahedral literal K member
  let B := actualRepresentative F torsion j
  let e : Equiv.Perm (Fin (m+2)) := (firstPair m).symm.trans p
  let key : RawCardKey m (completeGroup F torsion) := (fun _=>none,e,j,false)
  have hraw : rawCard F torsion f key=
      Signature.contract (nativePair B) (Tensor.reindex e.symm f) := by
    simp only [rawCard,key,orientBinary,Bool.false_eq_true,ite_false,ClosureSourceRows.dress_none]
    rfl
  have hpair : nativePair (B.map (complexEmbedding phi))=c • K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair K (!a) (!b)=c*K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hkernel (a b : Bool) : complexEmbedding phi (nativePair B a b)=c*K a b := by
    rw [nativePair_apply]
    have hh := congrFun (congrFun hpair a) b
    rw [nativePair_apply] at hh
    change complexEmbedding phi (B (!a) (!b))=c*K a b at hh
    exact hh
  have hword (a b : Bool) (x : Word m) :
      (fun i : Fin (m+2)=>(Fin.cons a (Fin.cons b x) : Word (m+2)) (e.symm i))=
        pairInsert p a b x := by
    ext i
    obtain ⟨u,rfl⟩ := p.surjective i
    cases u with
    | inl t => cases t <;> simp [e,firstPair,pairInsert]
    | inr j => simp [e,firstPair,pairInsert]
  have mapped : RingHomRealization.mapSignature (complexEmbedding phi) (rawCard F torsion f key)=
      c • pairCard p K (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
    rw [hraw]
    ext x
    simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
      hkernel,hword,pairCard,LinearMap.coe_mk,AddHom.coe_mk,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have affine := complexAffine_of_affine (stable _ (Or.inr ⟨key,rfl⟩))
  change ComplexAffine (RingHomRealization.mapSignature (complexEmbedding phi)
    (rawCard F torsion f key)) at affine
  rw [mapped] at affine
  exact (affine_complex_scale_iff c hc _).mp affine

include literal stable in
theorem prime_higher_affine (large : 8≤m+2)
    (prime : Prime (⟨m+2,f⟩ : AnySignature L)) :
    ComplexAffine (RingHomRealization.mapSignature (complexEmbedding phi) f) := by
  classical
  let g := RingHomRealization.mapSignature (complexEmbedding phi) f
  have hp : Prime (⟨m+2,g⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff (complexEmbedding phi) (⟨m+2,f⟩ : AnySignature L)).mpr prime
  by_contra ha
  rcases factor_or_nonaffine_pair g large ha with factor | card
  · obtain ⟨a,b,ha,hb,p,u,v,_,_,he⟩ := factor
    apply hp.2
    exact ⟨⟨a,u⟩,⟨b,v⟩,⟨{
      left_pos:=ha
      right_pos:=hb
      ports:=p
      scale:=1
      equation:=by
        funext x
        change g x=(1 : ℂ)*(u (fun i=>x (p (.inl i)))*v (fun i=>x (p (.inr i))))
        simpa only [Tensor.reindex,Tensor.tensor,one_mul] using congrFun he x }⟩⟩
  · obtain ⟨n,p,r,_,hnonaffine⟩ := card
    have hn : n=m := by have := pair_arity p; omega
    subst n
    exact hnonaffine (pair_affine phi F torsion literal f stable p _
      ⟨1,one_ne_zero,_,Holant.Certificates.TetrahedralAffine.kernel_base r,by simp⟩)

include literal stable in
theorem prime_higher_algebraic_affine (large : 8≤m+2)
    (prime : Prime (⟨m+2,f⟩ : AnySignature L)) :
    Affine (RingHomRealization.mapSignature phi f) :=
  GlobalCloseCompletionTetrahedralAffineCards.affine_of_complex _
    (prime_higher_affine phi F torsion literal f stable large prime)

include stable in
theorem semantic_prime_higher_affine
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : Holant.LocalDrafts.FinitePGL2.HasModel
      (ClosureMarkedReversalOvergroup.Ambient.overgroup phi F torsion) (.platonic .tetrahedral))
    (large : 8≤m+2) (prime : Prime (⟨m+2,f⟩ : AnySignature L)) :
    Affine (RingHomRealization.mapSignature phi f) :=
  prime_higher_algebraic_affine phi F torsion
    (GlobalCloseCompletionTetrahedralMarking.semantic_tetrahedral_literal
      phi F torsion identity semantic) f stable large prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralAffineDeck
end
