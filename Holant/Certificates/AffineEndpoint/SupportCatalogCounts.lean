import Holant.Certificates.AffineEndpoint.SupportCatalog

/-! Exact dimension counts for the actual structurally enumerated supports. -/
namespace Holant.Certificates.AffineEndpoint.SupportCatalog
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000

theorem dimension_filter_card (d : ℕ) :
    ((affineCatalog 4).filter (fun S => S.card = 2 ^ d)).card =
      (Finset.univ.filter (fun s : SupportIndex => supportDim s = d)).card := by
  rw [affine_catalog_eq, Finset.filter_image,
    Finset.card_image_of_injective _ supportWords_injective]
  congr 1
  ext s
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, supportWords_card]
  exact Nat.pow_right_inj (by decide : 1 < 2)

theorem affine_support_dimension_counts :
    ((affineCatalog 4).filter (fun S => S.card = 1)).card = 16 ∧
    ((affineCatalog 4).filter (fun S => S.card = 2)).card = 120 ∧
    ((affineCatalog 4).filter (fun S => S.card = 4)).card = 140 ∧
    ((affineCatalog 4).filter (fun S => S.card = 8)).card = 30 ∧
    ((affineCatalog 4).filter (fun S => S.card = 16)).card = 1 := by
  obtain ⟨h0, h1, h2, h3, h4⟩ := support_dimension_counts
  exact ⟨by simpa using (dimension_filter_card 0).trans h0,
    by simpa using (dimension_filter_card 1).trans h1,
    by simpa using (dimension_filter_card 2).trans h2,
    by simpa using (dimension_filter_card 3).trans h3,
    by simpa using (dimension_filter_card 4).trans h4⟩

end Holant.Certificates.AffineEndpoint.SupportCatalog
