import Holant.Proofs.Dichotomy.Closure.External.GlobalCloseCompletionExternalTetrahedralCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicNamedCards
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralRigidity
import Holant.Platonic.RankDeficientLocalization.ActualDomain

/-! Full original-field deck adapter for the literal external-T alternative.
All named pair cards retain the original actual representatives and their
nonzero multipliers. No analytic chart is installed as a physical resource. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalDeck
open Holant Holant.Tractable Holant.Certificates
open Holant.Certificates.MatchingProductBridge Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.OctahedralSeparator
open Holant.Projective.BoundedTorsion
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.RankDeficientLocalization
open Holant.Platonic.TetrahedralLocalization Holant.Platonic.StabilizerShortening
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
open scoped BigOperators

def directions : Set (Matrix Bool Bool ℂ) := {U | RainbowOrbit.External.Direction U}

theorem directions_group : ProjectiveMatrixGroup directions where
  one_mem := RainbowOrbit.External.direction_one
  mul_mem U hU V hV := hU.mul hV
  inverse_mem U hU := ⟨U⁻¹,hU.inverse,
    Matrix.mul_nonsing_inv U (isUnit_iff_ne_zero.mpr hU.det_ne_zero),
    Matrix.nonsing_inv_mul U (isUnit_iff_ne_zero.mpr hU.det_ne_zero)⟩
  scalar_mem U hU c hc := hU.smul hc

theorem directions_safe_iff (U : Matrix Bool Bool ℂ) : SafeBinary directions U ↔ RainbowOrbit.External.Direction U :=
  GlobalCloseCompletionExternalTetrahedralCards.direction_right_X U

theorem directions_X : (MatchingContractionClosure.X : Matrix Bool Bool ℂ)∈directions :=
  GlobalCloseCompletionExternalTetrahedralCards.direction_X

theorem directions_reversal : ReversalStable directions := by
  intro U hU
  exact (directions_X.mul hU.transpose).mul directions_X

def dictionary : Holant.Certificates.PlatonicIncidence.Mat≃ₗ[ℂ]Holant.Certificates.PlatonicIncidence.Mat := GlobalCloseCompletionOctahedralGeometry.RankFour.thetaLinearEquiv 2

theorem dictionary_representative (i : Fin 12) :
    dictionary (RainbowOrbit.representative .tetrahedral i)=RainbowOrbit.External.representative i :=
  (RainbowOrbit.External.representative_eq_theta i).symm

theorem dictionary_member (i : Fin 12) : dictionary (RainbowOrbit.representative .tetrahedral i)∈directions := by
  rw [dictionary_representative]
  exact RainbowOrbit.External.Direction.representative i

theorem directions_span : Submodule.span ℂ directions=⊤ := by
  apply top_unique
  rw [←actualDomain_span .tetrahedral dictionary]
  apply Submodule.span_mono
  rintro K ⟨i,rfl⟩
  exact dictionary_member i

export GlobalCloseCompletionPlatonicHigherCards (matching_scale)
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=GlobalCloseCompletionExternalTetrahedralDictionary.group)

include literal in
theorem safe_direction (B : Matrix Bool Bool L) (safe : SafeBinary (actualTransfers F) B) :
    RainbowOrbit.External.Direction (B.map (complexEmbedding phi)) := by
  obtain ⟨C,hC,c,hc,he⟩ := safe
  have hB : B=c • C := by
    have ht := congrArg (fun A : Matrix Bool Bool L=>A*MatchingContractionClosure.X) he
    simpa only [transfer,Matrix.smul_mul,Matrix.mul_assoc,X_mul_X,Matrix.mul_one] using ht
  have h := GlobalCloseCompletionExternalTetrahedralCards.actual_direction phi F torsion literal C hC
  rw [hB]
  have hm : (c • C).map (complexEmbedding phi)=complexEmbedding phi c • C.map (complexEmbedding phi) := by
    funext a b
    exact map_mul (complexEmbedding phi) c (C a b)
  rw [hm]
  exact h.smul ((map_ne_zero _).mpr hc)

include literal in
theorem complex_matching {m : ℕ} (q : Signature L m)
    (hq : MatchingOrZero (actualTransfers F) q) :
    MatchingOrZero directions (RingHomRealization.mapSignature (complexEmbedding phi) q) := by
  rcases hq with rfl | ⟨M,hM,hs,rfl⟩
  · left
    funext x
    exact map_zero _
  · let N : Presentation ℂ (Fin m) :=
      ⟨M.edges,M.ports,fun e => (M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    refine Or.inr ⟨N,?_,(map_ne_zero _).mpr hs,?_⟩
    · intro e
      apply (directions_safe_iff _).mpr
      exact safe_direction phi F torsion literal _ (hM e)
    · ext x
      simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]

include literal in
theorem ordered_card {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Equiv.Perm (Fin (m+2))) (K : Matrix Bool Bool ℂ) (hk : RainbowOrbit.External.Direction K) :
    MatchingOrZero directions (Signature.contract K
      (Tensor.reindex p (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  obtain ⟨j,c,hc,he⟩ := GlobalCloseCompletionExternalTetrahedralCards.kernel_alignment phi F torsion literal K hk
  let B := actualRepresentative F torsion j
  let key : RawCardKey m (completeGroup F torsion) := (fun _ => none,p.symm,j,false)
  have hraw : rawCard F torsion f key=
      Signature.contract (nativePair B) (Tensor.reindex p f) := by
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
    exact hh
  have mapped : RingHomRealization.mapSignature (complexEmbedding phi) (rawCard F torsion f key)=
      c • Signature.contract K (Tensor.reindex p
        (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
    rw [hraw]
    ext x
    simp only [RingHomRealization.mapSignature,Signature.contract,Tensor.reindex,map_sum,map_mul,
      hkernel,Pi.smul_apply,smul_eq_mul,Finset.mul_sum,mul_assoc]
  have h := complex_matching phi F torsion literal _ (stable _ (Or.inr ⟨key,rfl⟩))
  rw [mapped] at h
  have hu := matching_scale _ _ h c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu

include literal in
theorem cardMap_matching {m : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Bool ⊕ P ≃ Fin (m+2)) (K : Matrix Bool Bool ℂ) (hk : RainbowOrbit.External.Direction K) :
    MatchingOrZero directions
      (cardMap p (RingHomRealization.mapSignature (complexEmbedding phi) f) K) := by
  classical
  have hc : Fintype.card P=m := by
    have h := Fintype.card_congr p
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  let e : Fin m ≃ P := (Fintype.equivFinOfCardEq hc).symm
  let p' : Bool ⊕ Fin m ≃ Fin (m+2) := (Equiv.sumCongr (Equiv.refl Bool) e).trans p
  let order : Equiv.Perm (Fin (m+2)) := p'.symm.trans (firstPair m)
  have h := ordered_card phi F torsion literal f stable order K hk
  have he : cardMap p (RingHomRealization.mapSignature (complexEmbedding phi) f) K=
      Tensor.reindex e (Signature.contract K (Tensor.reindex order
        (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
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
private theorem named_transport {n : ℕ} (q : Signature ℂ n)
    (u v : Fin n) (huv : u≠v) (K : Matrix Bool Bool ℂ)
    (h : MatchingOrZero directions
      (cardMap (GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv) q K)) :
    MatchingOrZero directions (contractPair u v K q) := by
  classical
  let p:=GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv
  rw [cardMap_eq_contractPair] at h
  have hr:=h.reindex (pairRemaining p)
  simpa [Tensor.reindex,p,GlobalCloseCompletionPlatonicNamedCards.pairPorts] using hr

include literal in
theorem every_named_pair {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (u v : Fin (m+2)) (huv : u≠v) (K : Matrix Bool Bool ℂ) (hk : RainbowOrbit.External.Direction K) :
    MatchingOrZero directions
      (contractPair u v K (RingHomRealization.mapSignature (complexEmbedding phi) f)) := by
  classical
  let p := GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv
  have h := cardMap_matching phi F torsion literal f stable p K hk
  exact named_transport (RingHomRealization.mapSignature (complexEmbedding phi) f) u v huv K h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalDeck
end
