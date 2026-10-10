import Holant.Certificates.TetrahedralOrientation.PhysicalDenotation
import Holant.Certificates.TetrahedralOrientation.ActualLegs
import Holant.Certificates.TetrahedralOrientation.Coefficients

/-! The exact physical output uses just the supplied ancestor and actual
binary resources from the tetrahedral transfer group. -/
namespace Holant.Certificates.TetrahedralOrientation
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section

/-- The literal source resource condition is [UX] in the tetrahedral group. -/
def tetrahedralResources (s : Orientation) : SignatureFamily ℂ :=
  {p | p = ⟨6,ancestor s⟩ ∨ ∃ U : Binary,
    groupDirection .tetrahedral (multiply U X) ∧ p = ⟨2,binarySignature U⟩}

theorem resources_subset (s : Orientation) : resources s ⊆ tetrahedralResources s := by
  intro p hp
  rcases hp with h | h | ⟨j,h⟩
  · exact Or.inl h
  · exact Or.inr ⟨Q0,equality_actual,h⟩
  · exact Or.inr ⟨nativeLeg (legs s j),nativeLeg_actual s j,h⟩

theorem dressed_realizes (s : Orientation) :
    Gadget.Realizes (tetrahedralResources s) .disequality (dressed s) :=
  (terminal_realizes s).mono (resources_subset s)

theorem normalized_realizesUpTo (s : Orientation) :
    Gadget.RealizesUpTo (tetrahedralResources s) .disequality (terminal s) := by
  refine ⟨rawScale s,rawScale_ne_zero s,?_⟩
  have h := dressed_realizes s
  rwa [dressed_exact] at h

/-- Eight-vertex allows vanishing internal even entries, while both constant
words must survive. This is the source's endpoint-nondegenerate condition. -/
def EndpointNondegenerateEightVertex (f : FourTensor) : Prop :=
  (∀ x, (x 0 ^^ x 1 ^^ x 2 ^^ x 3) = true → f x = 0) ∧
    f (fun _ => false) ≠ 0 ∧ f (fun _ => true) ≠ 0

theorem dressed_eightVertex (s : Orientation) : EndpointNondegenerateEightVertex (dressed s) :=
  ⟨dressed_odd_zero s,dressed_endpoints_nonzero s⟩

end
end Holant.Certificates.TetrahedralOrientation
