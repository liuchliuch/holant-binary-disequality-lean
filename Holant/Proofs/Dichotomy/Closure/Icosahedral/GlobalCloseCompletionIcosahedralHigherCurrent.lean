import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralHigherCoefficients
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralOppositeHigherCards
import Holant.Proofs.Dichotomy.Closure.Icosahedral.GlobalCloseCompletionIcosahedralSixCurrent

/-! Both actual I placements exclude a stable current prime with at least
six ports. Every original-field raw test keeps its representative multiplier;
the opposite display transports the resulting proper factor back through
its unchanged original port partition. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.HigherCurrent
open Holant Holant.Certificates Holant.Certificates.MatchingProductBridge
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.OppositeIcosahedral
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source

variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable {m : ℕ} (f : Signature L (m+2)) (hm : 6≤m+2)
variable (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)
variable (prime : Prime (⟨m+2,f⟩ : AnySignature L))

include hm stable prime in
theorem literal_prime_high_impossible (opposite : Bool)
    (literal : group phi F torsion=Dictionary.group opposite) : False := by
  let q := RingHomRealization.mapSignature (complexEmbedding phi) f
  have hp : Prime (⟨m+2,q⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff (complexEmbedding phi) (⟨m+2,f⟩ : AnySignature L)).mpr prime
  cases opposite
  · exact HigherCoefficients.prime_impossible q hm
      (fun u v huv K hk => GlobalCloseCompletionPlatonicNamedCards.every_named_pair
        phi F torsion .icosahedral literal f stable u v huv K hk) hp
  · have hd := fun u v huv K hk => OppositeHigherCards.every_named_pair
      phi F torsion literal f stable u v huv K hk
    rcases HigherCoefficients.factor_or_zero (analytical q) hm hd with hz | factor
    · have he := congrArg transport hz
      rw [transport_analytical] at he
      exact hp.1 (by simpa only [transport,Signature.coordinateAction_zero] using he)
    · have hf := SixCurrent.factor_transport (analytical q) factor
      rw [transport_analytical] at hf
      exact HigherCoefficients.prime_no_factor q hp hf

include hm stable prime in
theorem semantic_prime_high_impossible
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : Holant.LocalDrafts.FinitePGL2.HasModel
      (ClosureMarkedReversalOvergroup.Ambient.overgroup phi F torsion) (.platonic .icosahedral)) : False := by
  rcases Placement.current_two_displays phi F torsion identity semantic with standard | opposite
  · exact literal_prime_high_impossible phi F torsion f hm stable prime false standard
  · exact literal_prime_high_impossible phi F torsion f hm stable prime true opposite


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionIcosahedral.HigherCurrent
end
