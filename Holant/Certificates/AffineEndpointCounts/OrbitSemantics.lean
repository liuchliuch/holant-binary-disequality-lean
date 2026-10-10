import Holant.Certificates.AffineEndpointCounts.OrbitChecks
import Holant.Certificates.AffineEndpoint.ReferenceCounts

/-! The checked integer keys are complete for the actual complex diagonal
orbits, with every original central port word kept in its source order. -/
namespace Holant.Certificates.AffineEndpointCounts
open Holant Holant.Tractable Holant.EightVertex.ProductAnchor
open Holant.Certificates.AffineEndpoint Holant.Certificates.OctahedralSeparator IntegerValues
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false

def invariantPairEquiv : Fin 21 ≃ InvariantIndex := Equiv.ofBijective invariantPair invariantPair_bijective

def keyMeaning (k : Fin (5^21)) : InvariantIndex → AlgebraicComplex := fun p =>
  alg (invariantPalette (finFunctionFinEquiv.symm k (invariantPairEquiv.symm p)))

theorem keyMeaning_injective : Function.Injective keyMeaning := by
  intro k l h
  apply finFunctionFinEquiv.symm.injective
  funext j
  apply invariantPalette_injective
  apply alg_injective
  have H := congrFun h (invariantPairEquiv j)
  simpa only [keyMeaning,Equiv.symm_apply_apply] using H

theorem referenceInteger_alg (r : Fin 612) (x : Fin 16) :
    alg (referenceInteger r x) = reference r (codeWord x) := by
  rw [referenceInteger,fastIntegerInput_eq,integerInput_alg]
  rfl

theorem referenceInvariant_key (r : Fin 612) :
    diagonalInvariant (reference r) = keyMeaning (boundedOrbitKey r) := by
  funext p
  obtain ⟨j,rfl⟩ := invariantPair_bijective.2 p
  have h := congrArg alg (orbit_coefficient_check r j)
  simp only [alg_mul,referenceInteger_alg,centralCode_word,oneCode_word] at h
  have he : invariantPairEquiv j = invariantPair j := rfl
  change _ = alg (invariantPalette (finFunctionFinEquiv.symm (boundedOrbitKey r)
    (invariantPairEquiv.symm (invariantPair j))))
  rw [←he,Equiv.symm_apply_apply]
  simp only [diagonalInvariant,reference_origin,one_mul]
  exact (eq_div_iff (reference_endpoint_even r).2.1).mpr h |>.symm

theorem reference_orbit_iff_key (r s : Fin 612) :
    DiagonalOrbit (reference r) (reference s) ↔ orbitKey r = orbitKey s := by
  rw [←diagonalInvariant_complete _ _ (reference_endpoint_even r) (reference_endpoint_even s),
    referenceInvariant_key,referenceInvariant_key,keyMeaning_injective.eq_iff]
  exact Fin.ext_iff

def referenceInvariantSet (n : Nat) : Set (InvariantIndex → AlgebraicComplex) :=
  diagonalInvariant '' referenceSizeSet n

def referenceKeySet (n : Nat) : Finset (Fin (5^21)) :=
  (referenceSizeIndices n).image boundedOrbitKey

theorem referenceInvariantSet_eq (n : Nat) :
    referenceInvariantSet n = keyMeaning '' (referenceKeySet n : Set (Fin (5^21))) := by
  rw [referenceInvariantSet,referenceSizeSet_eq_image,Set.image_image]
  simp only [referenceKeySet,Finset.coe_image,Set.image_image]
  congr 1
  funext r
  exact referenceInvariant_key r

theorem referenceInvariant_count (n : Nat) :
    (referenceInvariantSet n).ncard = (referenceKeySet n).card := by
  rw [referenceInvariantSet_eq,Set.ncard_image_of_injective _ keyMeaning_injective,Set.ncard_coe_finset]

end
end Holant.Certificates.AffineEndpointCounts
