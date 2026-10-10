import Holant.ReedMuller.TwoChart.ChartLift
import Holant.ReedMuller.TwoChart.Geometry

/-! The bounded retained quotient space is constructed from the actual two
chart shifts and characters. Different directions retain actual separating
vectors; no bounded-completion witness is added to the source hypothesis. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon Holant.ReedMuller.RadonAccess
open Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 def chartDelta (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2)) : F.complement :=
  F.ordinaryBoundaryLinearEquiv.symm (C₁.shift-C₀.shift)

 def chartRho (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2)) : F.complement :=
  F.ordinaryBoundaryLinearEquiv.symm (PhaseNetwork.coefficients (C₀.character+C₁.character))

 theorem chartRho_dot (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2))
    (w : F.complement) :
    dot (chartRho F C₀ C₁).val w.val=
      C₀.character (F.ordinaryBoundaryLinearEquiv w)+C₁.character (F.ordinaryBoundaryLinearEquiv w) := by
  rw [←F.ordinaryBoundaryLinearEquiv_isometry]
  simp only [chartRho,LinearEquiv.apply_symm_apply]
  exact (PhaseNetwork.character_expansion (C₀.character+C₁.character)
    (F.ordinaryBoundaryLinearEquiv w)).symm

 theorem exists_chart_envelope (F : RadonAccess.RadonFrame n) (hn : Even n)
    (C₀ C₁ : Chart (n-2)) :
    ∃ U : Submodule (ZMod 2) F.complement,
      chartDelta F C₀ C₁∈U ∧ chartRho F C₀ C₁∈U ∧
      (((dotBilinear (n:=n)).restrict F.complement).restrict U).Nondegenerate ∧
      Even (Module.finrank (ZMod 2) U) ∧ Module.finrank (ZMod 2) U≤6 ∧
      (C₀.direction=C₁.direction → Module.finrank (ZMod 2) U≤4) ∧
      (C₀.direction≠C₁.direction → ∃ s t : F.complement,s∈U ∧ t∈U ∧
        F.ordinaryBoundaryLinearEquiv s∈C₀.direction ∧
        F.ordinaryBoundaryLinearEquiv s∉C₁.direction ∧
        F.ordinaryBoundaryLinearEquiv t∈C₁.direction ∧ dot s.val t.val=1) := by
  let B := (dotBilinear (n:=n)).restrict F.complement
  have hB : B.IsSymm := dotBilinear_symmetric.restrict _
  have hBn : B.Nondegenerate := RadonGeometry.complement_nondegenerate F
  have hBe := RadonGeometry.complement_even F hn
  by_cases hD : C₀.direction=C₁.direction
  · obtain ⟨U,hΔ,hρ,hU,he,hb⟩ := exists_even_envelope_two B hB hBn hBe
      (chartDelta F C₀ C₁) (chartRho F C₀ C₁)
    change Module.finrank (ZMod 2) U≤4 at hb
    exact ⟨U,hΔ,hρ,hU,he,by omega,fun _ => hb,fun h => False.elim (h hD)⟩
  · obtain ⟨s,t,hs,hsn,ht,hst,hss,htt⟩ := different_direction_witness C₀ C₁ hD
    let s' := F.ordinaryBoundaryLinearEquiv.symm s
    let t' := F.ordinaryBoundaryLinearEquiv.symm t
    have hss' : B s' s'=0 := by
      change dot s'.val s'.val=0
      rw [←F.ordinaryBoundaryLinearEquiv_isometry]
      simpa only [s',LinearEquiv.apply_symm_apply] using hss
    have hst' : B s' t'=1 := by
      change dot s'.val t'.val=1
      rw [←F.ordinaryBoundaryLinearEquiv_isometry]
      simpa only [s',t',LinearEquiv.apply_symm_apply] using hst
    obtain ⟨U,hsU,htU,hΔ,hρ,hU,he,hb⟩ := exists_even_envelope_separating_pair B hB hBn hBe
      s' t' (chartDelta F C₀ C₁) (chartRho F C₀ C₁) hss' hst'
    refine ⟨U,hΔ,hρ,hU,he,hb,fun h => False.elim (hD h),?_⟩
    intro _
    refine ⟨s',t',hsU,htU,?_,?_,?_,hst'⟩
    · simpa only [s',LinearEquiv.apply_symm_apply] using hs
    · simpa only [s',LinearEquiv.apply_symm_apply] using hsn
    · simpa only [t',LinearEquiv.apply_symm_apply] using ht

end
end Holant.ReedMuller.TwoChart
