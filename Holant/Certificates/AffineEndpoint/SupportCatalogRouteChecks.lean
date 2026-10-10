import Holant.Certificates.AffineEndpoint.SupportCatalogMaps

/-! Small routing and source-normalization checks. These avoid evaluating the
large deduplicated affine catalog as a single closed expression. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
set_option maxRecDepth 1000000
set_option maxHeartbeats 100000000

theorem translation_route_codes : ∀ l : LinearIndex, ∀ a : Fin 16,
    (supportRows (translationRoute l a)).codes = (linearRows l).codes.image (codeXor a) := by
  intro l
  fin_cases l <;> decide +kernel

theorem support_route_retract : ∀ s : SupportIndex,
    translationRoute (supportRows s).linearIndex (supportRows s).originCode = s := by
  decide +kernel

theorem support_origin_checked : ∀ s : SupportIndex,
    (supportRows s).originCode ∈ (supportRows s).codes ∧
      ∀ a ∈ (supportRows s).codes, (supportRows s).originCode ≤ a := by
  decide +kernel

theorem support_dimension_counts :
    (Finset.univ.filter (fun s : SupportIndex => supportDim s = 0)).card = 16 ∧
    (Finset.univ.filter (fun s : SupportIndex => supportDim s = 1)).card = 120 ∧
    (Finset.univ.filter (fun s : SupportIndex => supportDim s = 2)).card = 140 ∧
    (Finset.univ.filter (fun s : SupportIndex => supportDim s = 3)).card = 30 ∧
    (Finset.univ.filter (fun s : SupportIndex => supportDim s = 4)).card = 1 := by
  decide +kernel

end Holant.Certificates.AffineEndpoint.SupportCatalog
