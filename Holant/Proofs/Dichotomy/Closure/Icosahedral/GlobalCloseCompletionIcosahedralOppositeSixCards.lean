import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicSixCards

/-! The opposite-I six-port deck, viewed through its exact diagonal
coefficient identity. Every tested original kernel comes from the actual
opposite group with its original-field representative and nonzero scalar. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.OppositeSixCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.OppositeIcosahedral
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

theorem analytical_apply {n : ℕ} (f : Signature ℂ n) (x : Fin n → Bool) :
    analytical f x=(OppositeIcosahedral.weight x)⁻¹*f x := by
  have he := congrFun (transport_analytical f) x
  rw [transport_eq_tensor] at he
  change OppositeIcosahedral.weight x*analytical f x=f x at he
  calc
    analytical f x=(OppositeIcosahedral.weight x)⁻¹*(OppositeIcosahedral.weight x*analytical f x) := by
      rw [←mul_assoc,inv_mul_cancel₀ (OppositeIcosahedral.weight_ne_zero x),one_mul]
    _ = (OppositeIcosahedral.weight x)⁻¹*f x := by rw [he]

theorem binaryTransport_kappa (U : Matrix Bool Bool ℂ) : binaryTransport (kappa U)=U := by
  simpa only [binaryTransport,unkappa,D_transpose] using unkappa_kappa U

theorem kappa_direction {U : Matrix Bool Bool ℂ} (hu : Direction U) :
    groupDirection .icosahedral (kappa U) := by
  have ht : Direction (binaryTransport (kappa U)*OppositeIcosahedral.X) := by
    rw [binaryTransport_kappa]
    exact (Dictionary.right_X true U).mpr hu
  exact (Dictionary.right_X false (kappa U)).mp ((output_transfer_iff _).mp ht)

theorem kappa_apply (U : Matrix Bool Bool ℂ) (a b : Bool) :
    kappa U a b=(diagonalWeight a*diagonalWeight b)⁻¹*U a b := by
  have he := congrArg (fun M : Matrix Bool Bool ℂ => M a b) (binaryTransport_kappa U)
  have hw : binaryTransport (kappa U) a b=
      (diagonalWeight a*diagonalWeight b)*kappa U a b := by
    cases a <;> cases b <;>
      simp [binaryTransport,D_weight,Matrix.mul_apply,Signature.equality] <;> ring
  rw [hw] at he
  have hn := mul_ne_zero (diagonalWeight_ne_zero a) (diagonalWeight_ne_zero b)
  calc
    kappa U a b=(diagonalWeight a*diagonalWeight b)⁻¹*
      ((diagonalWeight a*diagonalWeight b)*kappa U a b) := by
        rw [←mul_assoc,inv_mul_cancel₀ hn,one_mul]
    _ = (diagonalWeight a*diagonalWeight b)⁻¹*U a b := by rw [he]

def analyticalPresentation {n : ℕ} (M : Presentation ℂ (Fin n)) : Presentation ℂ (Fin n) :=
  ⟨M.edges,M.ports,fun e => kappa (M.matrix e),M.scalar⟩

theorem presentation_weight {n : ℕ} (M : Presentation ℂ (Fin n)) (x : Fin n → Bool) :
    (∏ e,diagonalWeight (x (M.ports (e,false)))*diagonalWeight (x (M.ports (e,true))))=OppositeIcosahedral.weight x := by
  have h := M.ports.prod_comp (fun j => diagonalWeight (x j))
  simpa only [OppositeIcosahedral.weight,Fintype.prod_prod_type,Fintype.prod_bool,mul_comm] using h

theorem analytical_presentation {n : ℕ} (M : Presentation ℂ (Fin n)) :
    analytical M.tensor=(analyticalPresentation M).tensor := by
  funext x
  rw [analytical_apply,←presentation_weight M x]
  simp only [Presentation.tensor,productValue,analyticalPresentation,kappa_apply,
    Finset.prod_mul_distrib,Finset.prod_inv_distrib,mul_inv_rev]
  ring

theorem presentation_cone (M : Presentation ℂ (Fin 4))
    (hm : ∀e,Direction (M.matrix e)) : matchingCone .icosahedral (analytical M.tensor) := by
  rw [analytical_presentation]
  apply GlobalCloseCompletionPlatonicMatchingCone.presentation .icosahedral
  intro e
  exact kappa_direction (hm e)

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=Dictionary.group true)

include literal in
theorem safe_direction (B : Matrix Bool Bool L) (safe : SafeBinary (actualTransfers F) B) :
    Direction (B.map (complexEmbedding phi)) := by
  obtain ⟨C,hC,c,hc,he⟩ := safe
  have hB : B=c • C := by
    have ht := congrArg (fun A : Matrix Bool Bool L =>
      A*(MatchingContractionClosure.X : Matrix Bool Bool L)) he
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using ht
  have h := Cards.actual_direction phi F torsion true literal C hC
  rw [hB]
  have hm : (c • C).map (complexEmbedding phi)=complexEmbedding phi c • C.map (complexEmbedding phi) := by
    ext a b
    change complexEmbedding phi (c*C a b)=complexEmbedding phi c*complexEmbedding phi (C a b)
    exact map_mul _ _ _
  rw [hm]
  exact h.smul ((map_ne_zero _).mpr hc)

include literal in
theorem matching_cone (q : Signature L 4) (hq : MatchingOrZero (actualTransfers F) q) :
    matchingCone .icosahedral (analytical (RingHomRealization.mapSignature (complexEmbedding phi) q)) := by
  rcases hq with rfl | ⟨M,hM,_,rfl⟩
  · left
    have hz : RingHomRealization.mapSignature (complexEmbedding phi) (0 : Signature L 4)=0 := by
      funext x
      exact map_zero _
    rw [hz]
    exact Signature.coordinateAction_zero _
  · let N : Presentation ℂ (Fin 4) :=
      ⟨M.edges,M.ports,fun e => (M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    have hn : ∀e,Direction (N.matrix e) := fun e => safe_direction phi F torsion literal _ (hM e)
    have he : RingHomRealization.mapSignature (complexEmbedding phi) M.tensor=N.tensor := by
      ext x
      simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]
    rw [he]
    exact presentation_cone N hn

include literal in
theorem all_pairs (f : Signature L 6)
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q) :
    GlobalCloseCompletionPlatonicSix.AllPairs .icosahedral
      (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  intro p K hk
  change matchingCone .icosahedral
    (card p (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)) K)
  have hk' : Dictionary.direction true (kappa K) := (kernel_membership_iff K).mpr hk
  obtain ⟨j,c,hc,he⟩ := Cards.kernel_alignment phi F torsion true literal (kappa K) hk'
  let B := actualRepresentative F torsion j
  let key : RawCardKey 4 (completeGroup F torsion) := (fun _ => none,p.symm,j,false)
  have hraw : rawCard F torsion f key=
      Signature.contract (nativePair B) (Tensor.reindex p f) := by
    simp only [rawCard,key,orientBinary,Bool.false_eq_true,ite_false,ClosureSourceRows.dress_none]
    rfl
  have hpair : nativePair (B.map (complexEmbedding phi))=c • kappa K := by
    rw [he]
    ext a b
    rw [nativePair_apply]
    change c*nativePair (kappa K) (!a) (!b)=c*kappa K a b
    rw [nativePair_apply,Bool.not_not,Bool.not_not]
  have hkernel (a b : Bool) : complexEmbedding phi (nativePair B a b)=c*kappa K a b := by
    rw [nativePair_apply]
    have hh := congrFun (congrFun hpair a) b
    rw [nativePair_apply] at hh
    exact hh
  have mapped : RingHomRealization.mapSignature (complexEmbedding phi) (rawCard F torsion f key)=
      c • card p (RingHomRealization.mapSignature (complexEmbedding phi) f) (kappa K) := by
    rw [hraw]
    ext x
    simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
      hkernel,card,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have h := matching_cone phi F torsion literal _ (stable _ (Or.inr ⟨key,rfl⟩))
  rw [mapped,analytical_smul,card_covariance,analytical_transport] at h
  have hu := matchingCone_smul .icosahedral h c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.OppositeSixCards
end
