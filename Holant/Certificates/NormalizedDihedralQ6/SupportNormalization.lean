import Holant.Certificates.NormalizedDihedralQ6.Normalization
import Holant.Certificates.NormalizedDihedralQ6.SourceParameters

namespace Holant.Certificates.NormalizedDihedralQ6

/-- Permuting the free fixed-edge bit merely permutes the four actual words. -/
theorem sectorWords_transform (ε : Bool) (d₀ d₁ : Sector) :
    transform (normalPerm d₀.1) (normalFlip d₀) (sectorWords ε d₁).toFinset =
      (sectorWords ε (normalizeOdd d₀ d₁)).toFinset := by
  simp only [transform,sectorWords,List.toFinset_cons,List.toFinset_nil,
    Finset.image_insert,Finset.image_empty,sectorWord_normalize]
  cases hc : fixedBitShift d₀ d₁ <;> ext x <;> simp [hc,or_assoc,or_comm,or_left_comm]

/-- Exact normalization of the full original eight-word support. -/
theorem normalize_support (d₀ d₁ : Sector) :
    transform (normalPerm d₀.1) (normalFlip d₀) (support d₀ d₁) =
      canonicalSupport (normalizeOdd d₀ d₁) := by
  change transform (normalPerm d₀.1) (normalFlip d₀)
    (((sectorWords false d₀)++(sectorWords true d₁)).toFinset) = _
  rw [List.toFinset_append]
  change ((sectorWords false d₀).toFinset ∪ (sectorWords true d₁).toFinset).image _ = _
  rw [Finset.image_union]
  change transform (normalPerm d₀.1) (normalFlip d₀) (sectorWords false d₀).toFinset ∪
    transform (normalPerm d₀.1) (normalFlip d₀) (sectorWords true d₁).toFinset = _
  rw [sectorWords_transform,sectorWords_transform,normalize_self]
  simp [canonicalSupport,support,List.toFinset_append]

/-- Every original sector-zero choice has exactly the same canonical case counts. -/
def normalizedChoices : (Sector × Sector) ≃ (Sector × Sector) where
  toFun d := (d.1,normalizeOdd d.1 d.2)
  invFun d := (d.1,denormalizeOdd d.1 d.2)
  left_inv d := by cases d; simp [denormalize_normalize]
  right_inv d := by cases d; simp [normalize_denormalize]

/-- Exact48-fold multiplicity for any property of the normalized odd data. -/
def normalizedPropertyEquiv (P : Sector → Prop) :
    {d : Sector × Sector // P (normalizeOdd d.1 d.2)} ≃ Sector × {d : Sector // P d} where
  toFun d := (d.1.1,⟨normalizeOdd d.1.1 d.1.2,d.2⟩)
  invFun d := ⟨(d.1,denormalizeOdd d.1 d.2.1),by simpa [normalize_denormalize] using d.2.2⟩
  left_inv d := by apply Subtype.ext; simp [denormalize_normalize]
  right_inv d := by simp [normalize_denormalize]

theorem normalized_property_card (P : Sector → Prop) [DecidablePred P] :
    Fintype.card {d : Sector × Sector // P (normalizeOdd d.1 d.2)} =
      48 * Fintype.card {d : Sector // P d} := by
  rw [Fintype.card_congr (normalizedPropertyEquiv P),Fintype.card_prod,sector_card]

end Holant.Certificates.NormalizedDihedralQ6
