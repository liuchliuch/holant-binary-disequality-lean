import Holant.Certificates.PlatonicIncidence.SpanTransport

/-! Every secant is obtained by actual multiplication by a literal group
representative. Finite rows are interpreted as complete intersections with a
complex two-dimensional vector span. -/
namespace Holant.Certificates.PlatonicIncidence
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 4000000

def translatedLine (g : PlatonicModel) (i : Fin (size g)) (b : Fin (baseCount g)) :
    Finset (Fin (size g)) := (baseLine g b).image (productIndex g i)

theorem mem_translated_product (g : PlatonicModel) (i k : Fin (size g))
    (b : Fin (baseCount g)) : productIndex g i k∈translatedLine g i b ↔ k∈baseLine g b :=
  Finset.mem_image.trans ⟨fun ⟨j,hj,h⟩ => (left_product_injective g i h) ▸ hj,
    fun h => ⟨k,h,rfl⟩⟩

theorem product_span_iff (g : PlatonicModel) (i j k : Fin (size g)) :
    representative g (productIndex g i k)∈Submodule.span ℂ
      ({representative g i,representative g (productIndex g i j)} : Set Mat) ↔
    representative g k∈Submodule.span ℂ ({(1 : Mat),representative g j} : Set Mat) := by
  exact mul_span_scaled_iff _ _ _ _ _ (representative_det_ne_zero g i)
    (productScale g i j : ℂ) (productScale g i k : ℂ)
    (Int.cast_ne_zero.mpr (raw_certificate g i j).1)
    (Int.cast_ne_zero.mpr (raw_certificate g i k).1)
    (mul_exact g i j) (mul_exact g i k)

theorem translatedLine_iff (g : PlatonicModel) (i k : Fin (size g))
    (b : Fin (baseCount g)) : k∈translatedLine g i b ↔
    representative g k∈Submodule.span ℂ
      ({representative g i,representative g (productIndex g i (baseAnchor g b))} : Set Mat) := by
  obtain ⟨j,rfl⟩ := (leftPermutation g i).surjective k
  rw [leftPermutation_apply,mem_translated_product,baseLine_iff,product_span_iff]

theorem translated_endpoints_ne (g : PlatonicModel) (i : Fin (size g))
    (b : Fin (baseCount g)) : i≠productIndex g i (baseAnchor g b) := by
  intro h
  apply (base_anchors g b).1
  apply left_product_injective g i
  rw [←h,product_identity_right]

theorem base_span_same (g : PlatonicModel) (j : Fin (size g)) (hj : j≠identityIndex g) :
    Submodule.span ℂ ({(1 : Mat),representative g (baseAnchor g (baseLineOf g j))} : Set Mat)=
    Submodule.span ℂ ({(1 : Mat),representative g j} : Set Mat) := by
  have ha : representative g (baseAnchor g (baseLineOf g j))∈
      Submodule.span ℂ ({(1 : Mat),representative g j} : Set Mat) := by
    apply (baseSecant_iff g _ _ hj).mp
    rw [base_certificate g j hj]
    exact (base_anchors g _).2.2.2
  have hb : representative g j∈Submodule.span ℂ
      ({(1 : Mat),representative g (baseAnchor g (baseLineOf g j))} : Set Mat) := by
    apply (baseLine_iff g _ _).mp
    rw [←base_certificate g j hj]
    exact (baseSecant_iff g _ _ hj).mpr (Submodule.subset_span (by simp))
  apply le_antisymm <;> apply Submodule.span_le.mpr <;> intro x hx
  · rcases hx with rfl|hx
    · exact Submodule.subset_span (by simp)
    · simpa only [Set.mem_singleton_iff] using hx ▸ ha
  · rcases hx with rfl|hx
    · exact Submodule.subset_span (by simp)
    · simpa only [Set.mem_singleton_iff] using hx ▸ hb

theorem secant_complete (g : PlatonicModel) (i j : Fin (size g)) (hij : i≠j) :
    ∃b : Fin (baseCount g),∀k : Fin (size g),
      k∈translatedLine g i b ↔ representative g k∈Submodule.span ℂ
        ({representative g i,representative g j} : Set Mat) := by
  obtain ⟨a,ha⟩ := (leftPermutation g i).surjective j
  have hane : a≠identityIndex g := by
    intro he
    rw [he,leftPermutation_apply,product_identity_right] at ha
    exact hij ha
  refine ⟨baseLineOf g a,?_⟩
  intro k
  obtain ⟨c,rfl⟩ := (leftPermutation g i).surjective k
  rw [leftPermutation_apply,mem_translated_product,baseLine_iff,base_span_same g a hane]
  rw [←ha,leftPermutation_apply,product_span_iff]

end
end Holant.Certificates.PlatonicIncidence
