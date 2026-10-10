import Holant.ReedMuller.AffinePatching.CubePatching
import Holant.ReedMuller.AffinePatching.Reconstruction

/-! Source Lemma 7.18. Actual affine orbit sums yield affine masked Walsh
restrictions; their support and phase patch globally, and exact inversion
returns the original tensor in the manuscript's affine class. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem affine_of_hyperplane_affine (hn : 7≤n) (F : Signature AlgebraicComplex n)
    (hF : HyperplaneAffine F) : Affine F :=
  affine_of_support_ternary_of_supported_cube F
    (global_support_ternary (by omega) F hF) (global_supported_cube hn F hF)

/-- The unnormalized source orbit sum, on the actual original Boolean ports. -/
def orbitPlus (v : BinaryVector n) (g : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => g x+g (AffinePhase.xor x (wordVector v))

/-- The source assumptions are sufficient as written. No global affine support,
phase, Walsh normal form, or reconstruction witness is an input. -/
theorem source_affine_hyperplane_patching (hn : 10≤n) (_heven : Even n)
    (g : Signature AlgebraicComplex n)
    (h : ∀ v : BinaryVector n,Accessible v → Affine (orbitPlus v g)) : Affine g := by
  apply (walsh_affine_iff g).mp
  apply affine_of_hyperplane_affine (by omega)
  intro v hv
  exact affine_hyperplaneMask_of_orbit_sum g (wordVector v) (h v hv)

end
end Holant.ReedMuller.AffinePatching
