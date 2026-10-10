import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralChartCards
import Holant.Proofs.Dichotomy.Closure.Platonic.GlobalCloseCompletionPlatonicNamedCards

/-! Full matching decks at arbitrary arity survive the four exact O charts.
The original scalar and matching incidence are retained, giving all named
pair tests needed by coefficient localization. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 200000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralHigherDeck
open Holant Holant.Tractable Holant.Certificates Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.Platonic.RainbowLocalization.Physical
open Holant.Platonic.StabilizerLine Holant.Platonic.StabilizerShortening
open Holant.Platonic.TetrahedralLocalization
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry ClosureMarkedDihedral.Source
open GlobalCloseCompletionOctahedralChart
open GlobalCloseCompletionPlatonicHigherCards
open scoped BigOperators
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (form : Form) (literal : group phi F torsion=Coordinates.Models.group form)

include literal in
theorem chart_matching {n : ℕ} (q : Signature L n)
    (matching : MatchingOrZero (actualTransfers F) q) :
    MatchingOrZero (directions .octahedral)
      (action form (RingHomRealization.mapSignature (complexEmbedding phi) q)) := by
  rcases matching with rfl | ⟨M,hM,hs,rfl⟩
  · left
    have hz : RingHomRealization.mapSignature (complexEmbedding phi) (0 : Signature L n)=0 := by
      funext x;exact map_zero _
    rw [hz,action,Signature.coordinateAction_zero]
  · let N : Presentation ℂ (Fin n) :=
      ⟨M.edges,M.ports,fun e=>(M.matrix e).map (complexEmbedding phi),complexEmbedding phi M.scalar⟩
    let Q : Presentation ℂ (Fin n) :=
      ⟨N.edges,N.ports,fun e=>H form*N.matrix e*(H form).transpose,N.scalar⟩
    have he : RingHomRealization.mapSignature (complexEmbedding phi) M.tensor=N.tensor := by
      ext x
      simp [RingHomRealization.mapSignature,Presentation.tensor,productValue,N,map_prod]
    refine Or.inr ⟨Q,?_,(map_ne_zero _).mpr hs,?_⟩
    · intro e
      apply (directions_safe_iff .octahedral _).mpr
      exact factor_direction form (N.matrix e)
        (GlobalCloseCompletionOctahedralChartCards.safe_direction phi F torsion form literal _ (hM e))
    · rw [he,presentation_action]

private theorem chart_scale {n : ℕ} (form : Form) (c : ℂ) (q : Signature ℂ n) :
    action form (c • q)=c • action form q := by
  funext x
  unfold action Signature.coordinateAction
  change (∑y,(∏j,H form (x j) (y j))*(c*q y))=c*(∑y,(∏j,H form (x j) (y j))*q y)
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

include literal in
theorem pair_matching {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : (Bool ⊕ Fin m)≃Fin (m+2)) (K : Matrix Bool Bool ℂ)
    (member : groupDirection .octahedral K) :
    MatchingOrZero (directions .octahedral)
      (pairCard p K (action form (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  obtain ⟨q,hq,c,hc,he⟩ := GlobalCloseCompletionOctahedralChartCards.actual_pair
    phi F torsion form literal f stable p ((H form).transpose*K*H form) (pair_direction form K member)
  have hm := chart_matching phi F torsion form literal q hq
  rw [he,chart_scale] at hm
  rw [GlobalCloseCompletionOctahedralChartCards.pair_action]
  have hu := matching_scale _ _ hm c⁻¹
  simpa only [smul_smul,inv_mul_cancel₀ hc,one_smul] using hu

include literal in
theorem ordered_card {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (order : Equiv.Perm (Fin (m+2))) (K : Matrix Bool Bool ℂ)
    (member : groupDirection .octahedral K) :
    MatchingOrZero (directions .octahedral)
      (Signature.contract K (Tensor.reindex order
        (action form (RingHomRealization.mapSignature (complexEmbedding phi) f)))) := by
  have h := pair_matching phi F torsion form literal f stable
    ((firstPair m).trans order.symm) K member
  rw [GlobalCloseCompletionOctahedralChartCards.pair_as_contract] at h
  have eqe : (((firstPair m).trans order.symm).symm.trans (firstPair m))=order := by
    apply Equiv.ext
    intro i
    change (firstPair m) ((firstPair m).symm (order i))=order i
    exact (firstPair m).apply_symm_apply _
  rw [eqe] at h
  exact h

include literal in
theorem cardMap_matching {m : ℕ} {P : Type*} [Fintype P] [DecidableEq P]
    (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (p : Bool ⊕ P ≃ Fin (m+2)) (K : Matrix Bool Bool ℂ) (hk : groupDirection .octahedral K) :
    MatchingOrZero (directions .octahedral)
      (cardMap p (action form (RingHomRealization.mapSignature (complexEmbedding phi) f)) K) := by
  classical
  have hc : Fintype.card P=m := by
    have h := Fintype.card_congr p
    simp only [Fintype.card_sum,Fintype.card_bool,Fintype.card_fin] at h
    omega
  let e : Fin m ≃ P := (Fintype.equivFinOfCardEq hc).symm
  let p' : Bool ⊕ Fin m ≃ Fin (m+2) := (Equiv.sumCongr (Equiv.refl Bool) e).trans p
  let order : Equiv.Perm (Fin (m+2)) := p'.symm.trans (firstPair m)
  have h := ordered_card phi F torsion form literal f stable order K hk
  have he : cardMap p (action form (RingHomRealization.mapSignature (complexEmbedding phi) f)) K=
      Tensor.reindex e (Signature.contract K (Tensor.reindex order
        (action form (RingHomRealization.mapSignature (complexEmbedding phi) f)))) := by
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
    (h : MatchingOrZero (directions .octahedral)
      (cardMap (GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv) q K)) :
    MatchingOrZero (directions .octahedral) (contractPair u v K q) := by
  classical
  let p:=GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv
  rw [cardMap_eq_contractPair] at h
  have hr:=h.reindex (pairRemaining p)
  simpa [Tensor.reindex,p,GlobalCloseCompletionPlatonicNamedCards.pairPorts] using hr

include literal in
theorem every_named_pair {m : ℕ} (f : Signature L (m+2))
    (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
    (u v : Fin (m+2)) (huv : u≠v) (K : Matrix Bool Bool ℂ) (hk : groupDirection .octahedral K) :
    MatchingOrZero (directions .octahedral)
      (contractPair u v K (action form (RingHomRealization.mapSignature (complexEmbedding phi) f))) := by
  classical
  let p := GlobalCloseCompletionPlatonicNamedCards.pairPorts u v huv
  have h := cardMap_matching phi F torsion form literal f stable p K hk
  exact named_transport (action form (RingHomRealization.mapSignature (complexEmbedding phi) f)) u v huv K h

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralHigherDeck
end
