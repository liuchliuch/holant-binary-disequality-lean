import Holant.Dihedral.SupportIntegration.LocalData
import Holant.Dihedral.TwoCardLocalization.ResidualOrder

/-! All local matching projections belong to the single reconstructed global
direction. Matching coordinates are transported through actual original
surviving port IDs, rather than equated across different residual sets. -/
noncomputable section
namespace Holant.Dihedral.SupportIntegration
open Holant Holant.Dihedral.EndpointParallelogram Holant.ReedMuller.LowArity
open Holant.Dihedral.CompatibleClosure
set_option backward.isDefEq.respectTransparency false
variable {K : Type*} [Field K] {n : ℕ}

 theorem LocalAtlas.matchingProjections {F : BinaryVector (n+2) → K} (A : LocalAtlas F) :
    MatchingProjections A.direction := by
  intro i j hij
  let o := pairOrder i j
  let D := A.patch o
  let p := D.ports.trans (Holant.Dihedral.TwoCardLocalization.remainingOrder i j hij)
  refine ⟨D.edges,p,?_⟩
  intro x hx he e
  have hn : pull o x ∈ D.code := by
    rw [A.direction_at o] at hx
    exact hx
  have hxy : pull o x 0=pull o x 1 := by
    simpa only [pull_apply,o,pairOrder_first i j hij,pairOrder_second] using he
  have hp := D.equal_projection (pull o x) hn hxy
  have hh := (Pairing.ofPorts_code D.ports _).mp hp e
  exact hh

/-- The global affine direction is explicitly constructed from local support
data before self-orthogonality is deduced. -/
 theorem local_atlas_selfOrthogonal {F : BinaryVector (n+2) → K}
    (A : LocalAtlas F) (hn : 4<n+2) :
    fullCoset F A.direction A.offset ∧
    ∀ x : BinaryVector (n+2),x ∈ A.direction →
      ∀ y : BinaryVector (n+2),y ∈ A.direction → dot x y=0 :=
  ⟨A.full_support,selfOrthogonal_of_matchingProjections A.direction hn A.matchingProjections⟩

end Holant.Dihedral.SupportIntegration
