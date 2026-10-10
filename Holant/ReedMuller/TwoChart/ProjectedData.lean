import Holant.ReedMuller.TwoChart.ChartEnvelope

/-! Common projected shifts and matching fiber characters, all in the original
coordinates. These are consequences of the retained space, not source premises. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon Holant.ReedMuller.RadonAccess
open Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def orthogonalProjection (S : BinaryCode n)
    (hS : ((dotBilinear (n:=n)).restrict S).Nondegenerate) : BinaryVector n →ₗ[ZMod 2] BinaryVector n :=
  ((dotBilinear (n:=n)).orthogonal S).projection S
    ((dotBilinear (n:=n)).isCompl_orthogonal_of_restrict_nondegenerate
      dotBilinear_symmetric.isRefl hS).symm

 theorem orthogonalProjection_zero (S : BinaryCode n)
    (hS : ((dotBilinear (n:=n)).restrict S).Nondegenerate) (x : BinaryVector n) (hx : x∈S) :
    orthogonalProjection S hS x=0 :=
  (((dotBilinear (n:=n)).orthogonal S).projection_apply_eq_zero_iff _).mpr hx

 theorem orthogonalProjection_fix (S : BinaryCode n)
    (hS : ((dotBilinear (n:=n)).restrict S).Nondegenerate) (x : BinaryVector n)
    (hx : x∈(dotBilinear (n:=n)).orthogonal S) : orthogonalProjection S hS x=x :=
  ((dotBilinear (n:=n)).orthogonal S).projection_apply_of_mem_left _ hx

 theorem sub_orthogonalProjection_mem (S : BinaryCode n)
    (hS : ((dotBilinear (n:=n)).restrict S).Nondegenerate) (x : BinaryVector n) :
    x-orthogonalProjection S hS x∈S :=
  ((dotBilinear (n:=n)).orthogonal S).sub_projection_mem _ x

 theorem common_orthogonalProjection (S : BinaryCode n)
    (hS : ((dotBilinear (n:=n)).restrict S).Nondegenerate) (a b : BinaryVector n)
    (hab : b-a∈S) : orthogonalProjection S hS a=orthogonalProjection S hS b := by
  have h := orthogonalProjection_zero S hS (b-a) hab
  rw [map_sub,sub_eq_zero] at h
  exact h.symm

 theorem lifted_shift_difference_mem (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2))
    (U : Submodule (ZMod 2) F.complement) (hΔ : chartDelta F C₀ C₁∈U) :
    (liftChart F 1 C₁).shift-(liftChart F 0 C₀).shift∈RadonGeometry.retainedSpace F U := by
  have hδ := RadonGeometry.mem_retainedSpace_of_mem F U _ hΔ
  have he : (liftChart F 1 C₁).shift-(liftChart F 0 C₀).shift=
      F.r+(chartDelta F C₀ C₁).val := by
    simp only [liftChart,RadonFrame.boundaryLift,one_smul,zero_smul,zero_add,chartDelta,map_sub]
    change F.r+(F.ordinaryBoundaryLinearEquiv.symm C₁.shift).val-
      (F.ordinaryBoundaryLinearEquiv.symm C₀.shift).val=
      F.r+((F.ordinaryBoundaryLinearEquiv.symm C₁.shift).val-
        (F.ordinaryBoundaryLinearEquiv.symm C₀.shift).val)
    abel
  rw [he]
  exact (RadonGeometry.retainedSpace F U).add_mem (RadonGeometry.r_mem_retainedSpace F U) hδ

 theorem lifted_characters_agree_on_orthogonal (F : RadonAccess.RadonFrame n)
    (C₀ C₁ : Chart (n-2)) (U : Submodule (ZMod 2) F.complement)
    (hρ : chartRho F C₀ C₁∈U) (x : BinaryVector n)
    (hx : x∈(dotBilinear (n:=n)).orthogonal (RadonGeometry.retainedSpace F U)) :
    (liftChart F 0 C₀).character x=(liftChart F 1 C₁).character x := by
  have hvx : dot x F.v=0 := by
    rw [dot_comm]
    exact hx F.v (RadonGeometry.v_mem_retainedSpace F U)
  have hρv : dot (chartRho F C₀ C₁).val F.v=0 := by
    rw [dot_comm]
    exact (chartRho F C₀ C₁).property.2
  have hzero : dot (chartRho F C₀ C₁).val x=0 :=
    hx _ (RadonGeometry.mem_retainedSpace_of_mem F U _ hρ)
  have hprojection : RadonFrame.boundaryProjection F (chartRho F C₀ C₁).val=
      PhaseNetwork.coefficients (C₀.character+C₁.character) := by
    have H := RadonFrame.projection_of_lift F 0 0 (chartRho F C₀ C₁)
    simpa only [zero_smul,zero_add,add_zero,chartRho,LinearEquiv.apply_symm_apply] using H
  rw [←RadonFrame.boundaryProjection_dot F _ _ hρv hvx,hprojection] at hzero
  have he : C₀.character (RadonFrame.boundaryProjection F x)+
      C₁.character (RadonFrame.boundaryProjection F x)=0 := by
    have H := PhaseNetwork.character_expansion (C₀.character+C₁.character)
      (RadonFrame.boundaryProjection F x)
    exact H.trans hzero
  exact (show ∀ a b : ZMod 2,a+b=0 → a=b from by decide) _ _ he

end
end Holant.ReedMuller.TwoChart
