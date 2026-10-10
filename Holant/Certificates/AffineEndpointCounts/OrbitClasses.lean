import Holant.Certificates.AffineEndpointCounts.OrbitCounts
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000

/-- Actual diagonal orbit among all endpoint-nondegenerate complex-algebraic
signatures, not a class of finite candidate labels. -/
def diagonalClass (h : Signature AlgebraicComplex 4) : Set (Signature AlgebraicComplex 4) :=
  {g | EndpointEven g ∧ DiagonalOrbit h g}

def referenceOrbits (n : Nat) : Set (Set (Signature AlgebraicComplex 4)) :=
  diagonalClass '' referenceSizeSet n

def invariantClass (J : InvariantIndex → AlgebraicComplex) : Set (Signature AlgebraicComplex 4) :=
  {g | EndpointEven g ∧ diagonalInvariant g=J}

theorem referenceSize_endpoint {n : Nat} {h : Signature AlgebraicComplex 4}
    (hh : h ∈ referenceSizeSet n) : EndpointEven h := by
  obtain ⟨r,hr,rfl⟩ := referenceSizeSet_eq_image n ▸ hh
  exact reference_endpoint_even r

theorem diagonalClass_eq_invariantClass (h : Signature AlgebraicComplex 4) (hh : EndpointEven h) :
    diagonalClass h=invariantClass (diagonalInvariant h) := by
  ext g
  constructor
  · rintro ⟨hg,hg'⟩
    exact ⟨hg,((diagonalInvariant_complete h g hh hg).mpr hg').symm⟩
  · rintro ⟨hg,hg'⟩
    exact ⟨hg,(diagonalInvariant_complete h g hh hg).mp hg'.symm⟩

theorem referenceOrbits_eq_image (n : Nat) :
    referenceOrbits n=invariantClass '' referenceInvariantSet n := by
  rw [referenceOrbits,referenceInvariantSet,Set.image_image]
  apply Set.image_congr
  intro h hh
  exact diagonalClass_eq_invariantClass h (referenceSize_endpoint hh)

theorem invariantClass_injOn (n : Nat) : Set.InjOn invariantClass (referenceInvariantSet n) := by
  rintro J ⟨h,hh,rfl⟩ K hK he
  have hm : h ∈ invariantClass (diagonalInvariant h) := ⟨referenceSize_endpoint hh,rfl⟩
  rw [he] at hm
  exact hm.2

theorem referenceOrbit_count (n : Nat) :
    (referenceOrbits n).ncard=(referenceInvariantSet n).ncard := by
  rw [referenceOrbits_eq_image,(invariantClass_injOn n).ncard_image]

theorem reference_orbit_histogram :
    (referenceOrbits 2).ncard=1 ∧ (referenceOrbits 4).ncard=24 ∧
      (referenceOrbits 8).ncard=256 := by
  simpa only [referenceOrbit_count] using reference_invariant_histogram

end
end Holant.Certificates.AffineEndpointCounts
