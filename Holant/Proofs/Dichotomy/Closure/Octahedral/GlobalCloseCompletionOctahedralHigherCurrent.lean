import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralHigherDeck
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralHigherCoefficients
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralChartFactors
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalCurrent

/-! No prepared semantic-O prime has arity≥6. Full O rows use their exact
Gram-corrected deck charts; the genuine external-T alternative uses its
actual no-rainbow obstruction. Both conclusions return to the original tensor. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralHigherCurrent
open Holant Holant.Tractable Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure Holant.Certificates.MatchingProductBridge
open Holant.Certificates.OctahedralSeparator
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open GlobalCloseCompletionOctahedralGeometry ClosureMarkedDihedral.Source
open ClosureMarkedReversalOvergroup.Ambient
open GlobalCloseCompletionOctahedralChart
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable {m : ℕ} (f : Signature L (m+2))
variable (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)

include stable in
theorem marked_prime_impossible (form : Form)
    (literal : group phi F torsion=Coordinates.Models.group form)
    (large : 6≤m+2) (prime : Prime (⟨m+2,f⟩ : AnySignature L)) : False := by
  let q := RingHomRealization.mapSignature (complexEmbedding phi) f
  have hp : Prime (⟨m+2,q⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff (complexEmbedding phi) (⟨m+2,f⟩ : AnySignature L)).mpr prime
  have deck := GlobalCloseCompletionOctahedralHigherDeck.every_named_pair
    phi F torsion form literal f stable
  rcases GlobalCloseCompletionOctahedralHigherCoefficients.factor_or_zero
    (action form q) large deck with zero | factor
  · have hh := congrArg (inverse form) zero
    rw [inverse_action] at hh
    exact hp.1 (by simpa only [inverse,Signature.coordinateAction_zero] using hh)
  · exact prime_no_chart_factor form q hp factor

include stable in
theorem semantic_prime_impossible
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : HasModel (overgroup phi F torsion) (.platonic .octahedral))
    (large : 6≤m+2) (prime : Prime (⟨m+2,f⟩ : AnySignature L)) : False := by
  rcases GlobalCloseCompletionOctahedralPlacement.actual_cases phi F torsion identity semantic with
    ⟨form,literal⟩ | external
  · exact marked_prime_impossible phi F torsion f stable form literal large prime
  · exact GlobalCloseCompletionOctahedralExternalCurrent.prime_higher_impossible
      phi F torsion external f stable large prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralHigherCurrent
end
