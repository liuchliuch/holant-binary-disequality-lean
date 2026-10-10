import Holant.Certificates.AffineEndpoint.SupportCatalogMaps

/-! Kernel-checked validation of each literal linear chart. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
open Holant.Tractable Holant.Tractable.AffinePhase
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem linear_catalog_eq : linearCatalog 4 = Finset.univ.image linearWords := by
  decide +kernel

theorem linear_codes_card : ∀ l : LinearIndex, (linearRows l).codes.card = 2 ^ linearDim l := by
  decide +kernel

theorem linear_codes_distinct : Function.Injective (fun l : LinearIndex => (linearRows l).codes) := by
  decide +kernel

theorem linear_canonical_basis : ∀ l : LinearIndex,
    List.ofFn (linearRows l).generators = sourceCanonicalBasis (linearRows l).codes (linearDim l) := by
  intro l
  fin_cases l <;> decide +kernel

theorem linear_basis_spans : ∀ l : LinearIndex,
    codeSpan (List.ofFn (linearRows l).generators) = (linearRows l).codes := by
  decide +kernel

theorem linear_coordinates_chart : ∀ l : LinearIndex, ∀ y : Word (linearDim l),
    linearCoordinates l (linearChart l y) = y := by
  intro l
  fin_cases l <;> decide +kernel

theorem linear_chart_coordinates_iff : ∀ l : LinearIndex, ∀ x : Word 4,
    linearChart l (linearCoordinates l x) = x ↔ x ∈ linearWords l := by
  intro l
  fin_cases l <;> decide +kernel

theorem linear_system_holds : ∀ l : LinearIndex, ∀ x : Word 4,
    (linearSystem l).Holds x ↔ x ∈ linearWords l := by
  intro l
  fin_cases l <;> decide +kernel

end Holant.Certificates.AffineEndpoint.SupportCatalog
