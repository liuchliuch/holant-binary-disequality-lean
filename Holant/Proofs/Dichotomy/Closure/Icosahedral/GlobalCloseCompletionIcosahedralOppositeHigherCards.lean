import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralOppositeSixCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicNamedPairTransport

/-! The full opposite-I raw deck supplies every named card of the exact
analytical tensor at all arities. No diagonal matrix is declared available;
original actual representatives and every nonzero multiplier remain explicit. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.OppositeHigherCards
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.OppositeIcosahedral
open Holant.Projective.BoundedTorsion
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.StabilizerShortening Holant.Platonic.TetrahedralLocalization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open OppositeSixCards GlobalCloseCompletionPlatonicHigherCards
open GlobalCloseCompletionPlatonicNamedCards (pairPorts)
open scoped BigOperators
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=Dictionary.group true)

include literal in
theorem matching {m : ℕ} (q : Signature L m) (hq : MatchingOrZero (actualTransfers F) q) :
    MatchingOrZero (directions .icosahedral)
      (analytical (RingHomRealization.mapSignature (complexEmbedding phi) q)) := by
  rcases hq with rfl | ⟨M,hM,hs,rfl⟩
  · left
    have hz : RingHomRealization.mapSignature (complexEmbedding phi) (0 : Signature L m)=0 := by
      funext x
      exact map_zero _
    rw [hz]
    exact Signature.coordinateAction_zero _
  · let N : Presentation ℂ (Fin m) :=
      ⟨M.edges,M.ports,fun e => (M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    let A := analyticalPresentation N
    refine Or.inr ⟨A,?_,(map_ne_zero _).mpr hs,?_⟩
    · intro e
      apply (directions_safe_iff .icosahedral _).mpr
      exact kappa_direction (safe_direction phi F torsion literal _ (hM e))
    · have he : RingHomRealization.mapSignature (complexEmbedding phi) M.tensor=N.tensor := by
        ext x
        simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]
      rw [he,analytical_presentation]

include literal in
theorem ordered_card {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Equiv.Perm (Fin (m+2))) (K : Matrix Bool Bool ℂ) (hk : groupDirection .icosahedral K) :
    MatchingOrZero (directions .icosahedral) (Signature.contract K (Tensor.reindex p
      (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)))) := by
  change MatchingOrZero (directions .icosahedral)
    (card p (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)) K)
  have hk' : Dictionary.direction true (kappa K) := (kernel_membership_iff K).mpr hk
  obtain ⟨j,c,hc,he⟩ := Cards.kernel_alignment phi F torsion true literal (kappa K) hk'
  let B := actualRepresentative F torsion j
  let key : RawCardKey m (completeGroup F torsion) := (fun _ => none,p.symm,j,false)
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
  have h := matching phi F torsion literal _ (stable _ (Or.inr ⟨key,rfl⟩))
  rw [mapped,analytical_smul,card_covariance,analytical_transport] at h
  have hu := matching_scale _ _ h c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu


include literal in
theorem cardMap_matching {m : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Bool ⊕ P ≃ Fin (m+2)) (K : Matrix Bool Bool ℂ) (hk : groupDirection .icosahedral K) :
    MatchingOrZero (directions .icosahedral)
      (cardMap p (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)) K) := by
  classical
  have hc : Fintype.card P=m := by
    have h := Fintype.card_congr p
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  let e : Fin m ≃ P := (Fintype.equivFinOfCardEq hc).symm
  let p' : Bool ⊕ Fin m ≃ Fin (m+2) := (Equiv.sumCongr (Equiv.refl Bool) e).trans p
  let order : Equiv.Perm (Fin (m+2)) := p'.symm.trans (firstPair m)
  have h := ordered_card phi F torsion literal f stable order K hk
  have he : cardMap p (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)) K=
      Tensor.reindex e (Signature.contract K (Tensor.reindex order
        (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f)))) := by
    ext x
    have hw (a b : Bool) :
        pairAssignment p a b x=(fun i : Fin (m+2) =>
          (Fin.cons a (Fin.cons b (fun j => x (e j))) : Fin (m+2) → Bool) (order i)) := by
      ext i
      obtain ⟨j,rfl⟩ := p.surjective i
      cases j with
      | inl t => cases t <;> simp [pairAssignment,order,p',firstPair]
      | inr j => simp [pairAssignment,order,p',firstPair]
    simp only [cardMap,LinearMap.coe_mk,AddHom.coe_mk,Signature.contract,Tensor.reindex,hw]
  rw [he]
  exact h.reindex e


include literal in
theorem every_named_pair {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (u v : Fin (m+2)) (huv : u≠v) (K : Matrix Bool Bool ℂ) (hk : groupDirection .icosahedral K) :
    MatchingOrZero (directions .icosahedral)
      (contractPair u v K (analytical (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  apply GlobalCloseCompletionPlatonicNamedPairTransport.matching
    (directions .icosahedral) _ u v huv K
  exact cardMap_matching phi F torsion literal f stable (pairPorts u v huv) K hk

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.OppositeHigherCards
end
