import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralSixClassification
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralOppositeSixCards
import Holant.Proofs.Closure.ClosureFactorTreeAction

/-! Both actual I placements exclude a stable current six-port prime.
The opposite display uses a reversible coefficient identity only; its
proper factor is transported back along the same original port partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.SixCurrent
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure
open Holant.Certificates.OppositeIcosahedral
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open Holant.Pauli.ExoticKlein.Fiber
open ClosureMarkedDihedral.Source

private theorem transport_nonzero {n : ℕ} (f : Signature ℂ n) (hf : f≠0) : transport f≠0 := by
  intro h
  apply hf
  apply transport_injective
  simpa only [transport,Signature.coordinateAction_zero] using h

theorem factor_transport {n : ℕ} (f : Signature ℂ n) (hf : HasProperTensorFactor f) :
    HasProperTensorFactor (transport f) := by
  obtain ⟨a,b,ha,hb,p,u,v,hu,hv,he⟩ := hf
  refine ⟨a,b,ha,hb,p,transport u,transport v,transport_nonzero u hu,transport_nonzero v hv,?_⟩
  rw [he,transport,ClosureFactorTreeAction.coordinateAction_tensor]
  rfl

theorem opposite_prime_impossible (f : Signature ℂ 6)
    (hp : GlobalCloseCompletionPlatonicSix.AllPairs .icosahedral (analytical f))
    (prime : Prime (⟨6,f⟩ : AnySignature ℂ)) : False := by
  rcases Six.factor_or_zero (analytical f) hp with hz | factor
  · have he := congrArg transport hz
    rw [transport_analytical] at he
    exact prime.1 (by simpa only [transport,Signature.coordinateAction_zero] using he)
  · have factor' := factor_transport (analytical f) factor
    rw [transport_analytical] at factor'
    obtain ⟨a,b,ha,hb,p,u,v,_,_,he⟩ := factor'
    apply prime.2
    exact ⟨⟨a,u⟩,⟨b,v⟩,⟨{
      left_pos:=ha
      right_pos:=hb
      ports:=p
      scale:=1
      equation:=by
        funext x
        change f x=(1 : ℂ)*(u (fun i=>x (p (.inl i)))*v (fun i=>x (p (.inr i))))
        simpa only [Tensor.reindex,Tensor.tensor,one_mul] using congrFun he x }⟩⟩

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (f : Signature L 6)
variable (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)

include stable in
theorem literal_prime_six_impossible (opposite : Bool)
    (literal : group phi F torsion=Dictionary.group opposite)
    (prime : Prime (⟨6,f⟩ : AnySignature L)) : False := by
  have hp : Prime (⟨6,RingHomRealization.mapSignature (complexEmbedding phi) f⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff (complexEmbedding phi) (⟨6,f⟩ : AnySignature L)).mpr prime
  cases opposite
  · exact Six.prime_impossible _
      (GlobalCloseCompletionPlatonicSix.actual_all_pairs phi F torsion .icosahedral literal f stable) hp
  · exact opposite_prime_impossible _ (OppositeSixCards.all_pairs phi F torsion literal f stable) hp

include stable in
theorem semantic_prime_six_impossible
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : Holant.LocalDrafts.FinitePGL2.HasModel
      (ClosureMarkedReversalOvergroup.Ambient.overgroup phi F torsion) (.platonic .icosahedral))
    (prime : Prime (⟨6,f⟩ : AnySignature L)) : False := by
  rcases Placement.current_two_displays phi F torsion identity semantic with standard | opposite
  · exact literal_prime_six_impossible phi F torsion f stable false standard prime
  · exact literal_prime_six_impossible phi F torsion f stable true opposite prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.SixCurrent
end
