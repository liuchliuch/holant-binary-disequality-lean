import Holant.ReedMuller.TwoChart.LocalizedOutput

/-! The bounded candidate output retains the actual nonaffine chart
obstruction: three supported points and a missing fourth, or a forbidden
fourth-root layer ratio. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ} {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

 def twoChartSum (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2)) : Signature AlgebraicComplex n :=
  fun x => (liftChart F 0 C₀).eval x+(liftChart F 1 C₁).eval x

 theorem LocalizingData.output_zero_add (L : LocalizingData F C₀ C₁) (s : L.space)
    (hv : dot s.val F.v=0) :
    L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.zeroPoint+L.coordinates s))=
      signedChartSum (liftChart F 0 C₀) L.isotropic L.character ((liftChart F 0 C₀).shift+s.val) := by
  unfold twoChartSum
  rw [←map_add,L.output_two_charts]
  have he : L.shift+(L.zeroPoint+s).val=(liftChart F 0 C₀).shift+s.val := by
    change L.shift+((liftChart F 0 C₀).shift-L.shift+s.val)=_
    abel
  rw [he,signedChartSum_wrong_layer F 1 C₁ _ _ L.fiber_orthogonal_v]
  · exact add_zero _
  · change dot (RadonFrame.boundaryLift F 0 C₀.shift+s.val) F.v≠1
    rw [dot_add_left,RadonFrame.boundaryLift_layer,hv,zero_add]
    decide

 theorem LocalizingData.output_one_add (L : LocalizingData F C₀ C₁) (s : L.space)
    (hv : dot s.val F.v=0) :
    L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.onePoint+L.coordinates s))=
      signedChartSum (liftChart F 1 C₁) L.isotropic L.character ((liftChart F 1 C₁).shift+s.val) := by
  unfold twoChartSum
  rw [←map_add,L.output_two_charts]
  have he : L.shift+(L.onePoint+s).val=(liftChart F 1 C₁).shift+s.val := by
    change L.shift+((liftChart F 1 C₁).shift-L.shift+s.val)=_
    abel
  rw [he,signedChartSum_wrong_layer F 0 C₀ _ _ L.fiber_orthogonal_v]
  · exact zero_add _
  · change dot (RadonFrame.boundaryLift F 1 C₁.shift+s.val) F.v≠0
    rw [dot_add_left,RadonFrame.boundaryLift_layer,hv,add_zero]
    decide

 theorem LocalizingData.output_zero_nonzero (L : LocalizingData F C₀ C₁) :
    L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.zeroPoint))≠0 := by
  unfold twoChartSum
  rw [L.output_at_zero]
  exact signedChartSum_shift_nonzero _ _ _ L.character_zero

 theorem LocalizingData.output_one_nonzero (L : LocalizingData F C₀ C₁) :
    L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.onePoint))≠0 := by
  unfold twoChartSum
  rw [L.output_at_one]
  exact signedChartSum_shift_nonzero _ _ _ L.character_one

 theorem LocalizingData.output_nonaffine_different (L : LocalizingData F C₀ C₁)
    (hne : C₀.direction≠C₁.direction) : ¬Affine (L.output (twoChartSum F C₀ C₁)) := by
  obtain ⟨s,t,hsS,htS,hsC,hsn,htC,hst⟩ := L.separator hne
  let s' : L.space := ⟨s,hsS⟩
  have hv : dot s'.val F.v=0 := (mem_liftDirection F C₀.direction s).mp hsC |>.1
  refine nonaffine_of_missing_parallelogram _ (L.coordinates L.zeroPoint) (L.coordinates s')
    (L.coordinates L.onePoint) L.output_zero_nonzero ?_ L.output_one_nonzero ?_
  · rw [L.output_zero_add s' hv]
    exact signedChartSum_shift_add_nonzero _ _ _ L.character_zero s hsC
  · rw [L.output_one_add s' hv]
    apply signedChartSum_separating_zero _ _ _ L.character_one s t htC hst
    intro j
    rw [dot_comm]
    exact L.orthogonal t htS j.val j.property

 theorem LocalizingData.output_ratio_fourth (L : LocalizingData F C₀ C₁)
    (hD : C₀.direction=C₁.direction) :
    (L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.onePoint))/
      L.output (twoChartSum F C₀ C₁) (wordVector (L.coordinates L.zeroPoint)))^4=
      (C₁.scalar/C₀.scalar)^4 := by
  unfold twoChartSum
  rw [L.output_at_zero,L.output_at_one]
  exact signedChartSum_shift_ratio_fourth _ _ (congrArg (liftDirection F) hD)
    L.isotropic L.character L.character_zero L.character_one

 theorem LocalizingData.output_nonaffine (L : LocalizingData F C₀ C₁)
    (h : C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) :
    ¬Affine (L.output (twoChartSum F C₀ C₁)) := by
  by_cases hD : C₀.direction=C₁.direction
  · have hr := h.resolve_left (fun hh => hh hD)
    apply nonaffine_of_forbidden_ratio _
      (wordVector (L.coordinates L.zeroPoint)) (wordVector (L.coordinates L.onePoint))
      L.output_zero_nonzero L.output_one_nonzero
    rwa [L.output_ratio_fourth hD]
  · exact L.output_nonaffine_different hD

end
end Holant.ReedMuller.TwoChart
