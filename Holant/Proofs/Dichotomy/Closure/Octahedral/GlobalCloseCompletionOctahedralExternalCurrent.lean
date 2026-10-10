import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralExternalCoefficients
import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralPlacement

/-! The actual external-T alternative beneath a semantic O marking excludes
prepared primes at every arity≥6. Every coefficient hypothesis is produced
from the original full raw deck, and the factor contradiction returns to the
same original tensor by the faithful source-field embedding. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCurrent
open Holant Holant.Tractable Holant.Certificates
open Holant.Certificates.MatchingContractionClosure
open Holant.Projective.BoundedTorsion
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2 Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L→+*Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (literal : group phi F torsion=GlobalCloseCompletionExternalTetrahedralDictionary.group)
variable {m : ℕ} (f : Signature L (m+2))
variable (stable : ∀q∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) q)

include literal stable in
theorem prime_higher_impossible (large : 6≤m+2) (prime : Prime (⟨m+2,f⟩ : AnySignature L)) : False := by
  have hp : Prime (⟨m+2,RingHomRealization.mapSignature (complexEmbedding phi) f⟩ : AnySignature ℂ) :=
    (prime_mapSignature_iff (complexEmbedding phi) (⟨m+2,f⟩ : AnySignature L)).mpr prime
  exact GlobalCloseCompletionOctahedralExternalCoefficients.prime_impossible _ large
    (GlobalCloseCompletionOctahedralExternalDeck.every_named_pair phi F torsion literal f stable) hp

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralExternalCurrent
end
