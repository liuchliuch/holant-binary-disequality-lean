import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralSixClassification
import Holant.Proofs.Dichotomy.Closure.Tetrahedral.GlobalCloseCompletionTetrahedralMarking

/-! Actual current six-port internal-T primes are affine in their original
coordinates. The input is the unchanged complete raw deck and its exact
original-field transfers; all classification is derived in the source. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSixCurrent
open Holant Holant.Tractable
open Holant.Projective.BoundedTorsion
open Holant.Certificates.MatchingContractionClosure
open Holant.LocalDrafts.MainChain RingHomRealization
open Holant.LocalDrafts.FinitePGL2.Stabilization
open Holant.LocalDrafts.RemoteWork.StableClosureV2
open ClosureMarkedDihedral.Source
variable {L : Type*} [Field L] [NumberField L]
variable (phi : L →+* Holant.Marked.Scalar) (F : SignatureFamily L) (torsion : ResidualTorsion F)
variable (f : Signature L 6)
variable (stable : ∀g∈rawDeck F torsion f,MatchingOrZero (actualTransfers F) g)

include stable in
theorem prime_six_algebraic_affine
    (literal : group phi F torsion=Holant.Projective.FiniteGroupFacts.modelPGL .tetrahedral)
    (prime : Prime (⟨6,f⟩ : AnySignature L)) : Affine (RingHomRealization.mapSignature phi f) := by
  apply GlobalCloseCompletionTetrahedralAffineCards.affine_of_complex
  apply GlobalCloseCompletionTetrahedralSix.prime_affine
  · exact GlobalCloseCompletionTetrahedralSix.actual_all_pairs phi F torsion literal f stable
  · exact (prime_mapSignature_iff (complexEmbedding phi) (⟨6,f⟩ : AnySignature L)).mpr prime

include stable in
theorem semantic_prime_six_affine
    (identity : (⟨2,Holant.Projective.BoundedTorsion.binarySignature
      (Signature.equality : Matrix Bool Bool L)⟩ : AnySignature L)∈F)
    (semantic : Holant.LocalDrafts.FinitePGL2.HasModel
      (ClosureMarkedReversalOvergroup.Ambient.overgroup phi F torsion) (.platonic .tetrahedral))
    (prime : Prime (⟨6,f⟩ : AnySignature L)) : Affine (RingHomRealization.mapSignature phi f) :=
  prime_six_algebraic_affine phi F torsion f stable
    (GlobalCloseCompletionTetrahedralMarking.semantic_tetrahedral_literal phi F torsion identity semantic)
    prime


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTetrahedralSixCurrent
end
