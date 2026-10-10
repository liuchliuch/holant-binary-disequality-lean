import Holant.Certificates.PlatonicAtlas.QuotientFibers

/-! The bucket histogram equals a histogram of distinct actual projective
quotient directions, including their complete finite fibers. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
attribute [local instance] Classical.propDecidable
local instance quotientSpectrumPointDecidable : DecidableEq Point := Classical.decEq _
set_option backward.isDefEq.respectTransparency false

 def quotientDirections (D : Finset Point) (p : Point) :
    Finset (Projectivization ℂ (FourTensor ⧸ p.submodule)) := by
  classical
  exact (D.erase p).attach.image (fun q => quotientDirection p q.val (Finset.mem_erase.mp q.property).1)

 def quotientClass (D : Finset Point) (p : Point)
    (d : Projectivization ℂ (FourTensor ⧸ p.submodule)) : Finset Point :=
  D.filter (fun r => ∃hr : r≠p,quotientDirection p r hr=d)

 theorem quotientBuckets_spectrum (D : Finset Point) (p : Point) :
    quotientBuckets D p=(quotientDirections D p).image (quotientClass D p) := by
  classical
  rw [quotientDirections,Finset.image_image]
  rfl

 theorem quotientClass_injective (D : Finset Point) (p : Point) :
    Set.InjOn (quotientClass D p) (quotientDirections D p : Set _) := by
  classical
  intro d hd e he hh
  obtain ⟨⟨q,hq⟩,_,rfl⟩ := Finset.mem_image.mp hd
  have hmem : q∈quotientClass D p (quotientDirection p q (Finset.mem_erase.mp hq).1) :=
    Finset.mem_filter.mpr ⟨(Finset.mem_erase.mp hq).2,_,rfl⟩
  rw [hh] at hmem
  obtain ⟨_,hq',heq⟩ := Finset.mem_filter.mp hmem
  exact heq

/-- Equality to the literal finite spectrum of the complex projective quotient.
Thus counting buckets neither identifies distinct directions nor duplicates one. -/
 theorem quotientMultiplicity_spectrum (D : Finset Point) (p : Point) (n : ℕ) :
    quotientMultiplicity D p n=
      ((quotientDirections D p).filter (fun d => (quotientClass D p d).card=n)).card := by
  classical
  rw [quotientMultiplicity,quotientBuckets_spectrum,Finset.filter_image]
  exact Finset.card_image_iff.mpr ((quotientClass_injective D p).mono (Finset.filter_subset _ _))

end
end Holant.Certificates.PlatonicAtlas
