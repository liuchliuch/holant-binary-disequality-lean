import Holant.ReedMuller.TwoChart.LocalizingData

/-! Exact candidate boundary sums before their physical context realization.
The literal original chart layers are retained in every finite fiber. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon Holant.ReedMuller.RadonAccess
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ} {F : RadonAccess.RadonFrame n} {C₀ C₁ : Chart (n-2)}

 def LocalizingData.output (L : LocalizingData F C₀ C₁) (g : Signature AlgebraicComplex n) :
    Signature AlgebraicComplex L.outputSize := by
  letI : Fintype L.isotropic := Fintype.ofFinite _
  exact fun y => ∑ j : L.isotropic,fourthRootPhase (evenLift (L.character j.val))*
    g (wordVector (L.shift+(L.coordinates.symm (vectorWord y)).val+j.val))

 def LocalizingData.zeroPoint (L : LocalizingData F C₀ C₁) : L.space :=
  ⟨(liftChart F 0 C₀).shift-L.shift,L.shift_zero_mem⟩
 def LocalizingData.onePoint (L : LocalizingData F C₀ C₁) : L.space :=
  ⟨(liftChart F 1 C₁).shift-L.shift,L.shift_one_mem⟩

 theorem LocalizingData.output_two_charts (L : LocalizingData F C₀ C₁) (s : L.space) :
    L.output (fun x => (liftChart F 0 C₀).eval x+(liftChart F 1 C₁).eval x)
      (wordVector (L.coordinates s))=
      signedChartSum (liftChart F 0 C₀) L.isotropic L.character (L.shift+s.val)+
      signedChartSum (liftChart F 1 C₁) L.isotropic L.character (L.shift+s.val) := by
  simp only [LocalizingData.output,vector_word,LinearEquiv.symm_apply_apply,mul_add,Finset.sum_add_distrib]
  rfl

 theorem signedChartSum_wrong_layer (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (C : Chart (n-2)) (J : BinaryCode n) (chi : Character n)
    (hJ : ∀ j : J,dot j.val F.v=0) (x : BinaryVector n) (hx : dot x F.v≠d) :
    signedChartSum (liftChart F d C) J chi x=0 := by
  unfold signedChartSum
  apply Finset.sum_eq_zero
  intro j _
  rw [liftChart_eval]
  have hd : dot (vectorWord (wordVector (x+j.val))) F.v≠d := by
    rw [vector_word,dot_add_left,hJ,add_zero]
    exact hx
  rw [if_neg hd,mul_zero]

 theorem LocalizingData.fiber_orthogonal_v (L : LocalizingData F C₀ C₁) (j : L.isotropic) :
    dot j.val F.v=0 := by
  rw [dot_comm]
  exact L.orthogonal F.v L.v_mem j.val j.property

 theorem LocalizingData.output_at_zero (L : LocalizingData F C₀ C₁) :
    L.output (fun x => (liftChart F 0 C₀).eval x+(liftChart F 1 C₁).eval x)
      (wordVector (L.coordinates L.zeroPoint))=
      signedChartSum (liftChart F 0 C₀) L.isotropic L.character (liftChart F 0 C₀).shift := by
  rw [L.output_two_charts]
  have he : L.shift+L.zeroPoint.val=(liftChart F 0 C₀).shift := by
    change L.shift+((liftChart F 0 C₀).shift-L.shift)=_
    abel
  rw [he,signedChartSum_wrong_layer F 1 C₁ _ _ L.fiber_orthogonal_v]
  · exact add_zero _
  · change dot (RadonFrame.boundaryLift F 0 C₀.shift) F.v≠1
    rw [RadonFrame.boundaryLift_layer]
    decide

 theorem LocalizingData.output_at_one (L : LocalizingData F C₀ C₁) :
    L.output (fun x => (liftChart F 0 C₀).eval x+(liftChart F 1 C₁).eval x)
      (wordVector (L.coordinates L.onePoint))=
      signedChartSum (liftChart F 1 C₁) L.isotropic L.character (liftChart F 1 C₁).shift := by
  rw [L.output_two_charts]
  have he : L.shift+L.onePoint.val=(liftChart F 1 C₁).shift := by
    change L.shift+((liftChart F 1 C₁).shift-L.shift)=_
    abel
  rw [he,signedChartSum_wrong_layer F 0 C₀ _ _ L.fiber_orthogonal_v]
  · exact zero_add _
  · change dot (RadonFrame.boundaryLift F 1 C₁.shift) F.v≠0
    rw [RadonFrame.boundaryLift_layer]
    decide

end
end Holant.ReedMuller.TwoChart
