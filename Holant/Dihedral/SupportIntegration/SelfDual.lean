import Holant.Dihedral.SupportIntegration.Dimension
import Holant.Dihedral.SupportIntegration.ExactProjection
import Holant.ReedMuller.LowArity.HalfDimension

/-! Constructive global support integration up to self-duality. The direction,
its half dimension and all original-pair projection maps are derived from
literal local endpoint cosets and their matching extensions. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
variable {K : Type*} [Field K] {n : ℕ}

 theorem LocalAtlas.selfDual {F : BinaryVector (n+2) → K} (A : LocalAtlas F) (hn : 4<n+2) :
    SelfDual A.direction :=
  selfDual_of_selfOrthogonal_halfDimension A.direction
    (local_atlas_selfOrthogonal A hn).2 A.half_dimension

/-- The global affine code is a conclusion and is shared across all original
coordinate sets by proved reindexing. No self-dual-code witness is an input. -/
 theorem source_global_affine_selfDual {F : BinaryVector (n+2) → K}
    (A : LocalAtlas F) (hn : 4<n+2) :
    fullCoset F A.direction A.offset ∧ SelfDual A.direction ∧
    2*Module.finrank (ZMod 2) A.direction=n+2 ∧
    ExactMatchingProjections A.direction ∧
    ∀ o : Equiv.Perm (Fin (n+2)),A.direction=reindexCode o (A.patch o).code :=
  ⟨A.full_support,A.selfDual hn,A.half_dimension,A.exactMatchingProjections,A.direction_at⟩

end Holant.Dihedral.SupportIntegration
