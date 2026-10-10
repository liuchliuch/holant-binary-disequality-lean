import Holant.Dihedral.SectorRuling.SupportCounting

/-! The source m=3 exception is ruled out by literal coefficient ratios:
cancellation forces a ratio in -mu_3, disjoint from mu_3. -/
noncomputable section
namespace Holant.Dihedral.SectorRuling
open Holant.Marked

theorem negative_cube_root_not_root {z : Scalar} (hz : Roots 3 z) : ¬ Roots 3 (-z) := by
  intro hn
  change z^3=1 at hz
  change (-z)^3=1 at hn
  have he : (-z)^3=-(z^3) := by ring
  rw [he,hz] at hn
  norm_num at hn

/-- The minus sign is forced by cancellation at an actual common word. -/
theorem cancellation_ratio (a b x w v y : Scalar) (hb : b ≠ 0) (hw : w ≠ 0) (hy : y ≠ 0)
    (hcancel : a*w+b*v=0) :
    (a*x)/(b*y) = -((x/w)*(v/y)) := by
  field_simp [hb,hw,hy]
  linear_combination x*hcancel

/-- Three nonzero sampled matching tensors cannot realize this support switch.
Each ratio premise concerns two actual nonzero coefficients of one sample. -/
theorem cube_ratio_obstruction (a b x w v y : Scalar) (hb : b ≠ 0) (hw : w ≠ 0) (hy : y ≠ 0)
    (hcancel : a*w+b*v=0) (h₀ : Roots 3 (x/w)) (h₁ : Roots 3 (v/y))
    (h₂ : Roots 3 ((a*x)/(b*y))) : False := by
  rw [cancellation_ratio a b x w v y hb hw hy hcancel] at h₂
  exact negative_cube_root_not_root (h₀.mul h₁) h₂

end Holant.Dihedral.SectorRuling
