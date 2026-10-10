import Holant.Certificates.PlatonicIncidence.CoefficientEquivs
import Holant.Certificates.RainbowOrbit.ExternalSource

/-! A.19's literal spanning-kernel displays over the actual complex matrices. -/
namespace Holant.Certificates.PlatonicAtlas
open Holant.Certificates.MatchingProductBridge Holant.Certificates.RainbowOrbit
open Holant.Certificates.PlatonicIncidence
noncomputable section
set_option backward.isDefEq.respectTransparency false

def sourceAxes : Fin 4 → Mat := quaternionBasis

theorem sourceAxes_span : Submodule.span ℂ (Set.range sourceAxes)=⊤ := by
  apply top_unique
  intro U _
  let W := Submodule.span ℂ (Set.range sourceAxes)
  have ha (i : Fin 4) : sourceAxes i∈W := Submodule.subset_span ⟨i,rfl⟩
  have he : U=(quaternionCoefficient U 0) • sourceAxes 0+
      (quaternionCoefficient U 1) • sourceAxes 1+
      (quaternionCoefficient U 2) • sourceAxes 2+
      (quaternionCoefficient U 3) • sourceAxes 3 := by
    calc
      U=assemble (quaternionCoefficient U) := (assemble_coefficient U).symm
      _ = _ := rfl
  rw [he]
  exact W.add_mem (W.add_mem (W.add_mem (W.smul_mem _ (ha 0)) (W.smul_mem _ (ha 1)))
    (W.smul_mem _ (ha 2))) (W.smul_mem _ (ha 3))

theorem sourceAxes_actual (g : PlatonicModel) (i : Fin 4) :
    groupDirection g (sourceAxes i) := quaternion_axis_direction g i

theorem transported_sourceAxes_span (e : Mat ≃ₗ[ℂ] Mat) :
    Submodule.span ℂ (Set.range (fun i => e (sourceAxes i)))=⊤ := by
  apply top_unique
  intro U _
  obtain ⟨V,rfl⟩ := e.surjective U
  let W := Submodule.span ℂ (Set.range (fun i => e (sourceAxes i)))
  have hh : Submodule.span ℂ (Set.range sourceAxes)≤W.comap e.toLinearMap := by
    apply Submodule.span_le.mpr
    rintro x ⟨i,rfl⟩
    exact Submodule.subset_span ⟨i,rfl⟩
  rw [sourceAxes_span] at hh
  exact hh (Submodule.mem_top)

def externalAxes : Fin 4 → Mat := ![Matrix.of Q0,Matrix.of Q1,
  Matrix.of Q2+Matrix.of Q3,Matrix.of Q2-Matrix.of Q3]

theorem externalAxes_actual (i : Fin 4) : External.Direction (externalAxes i) := by
  apply (External.direction_iff_printed _).mpr
  refine ⟨1,one_ne_zero,externalAxes i,?_,by simp⟩
  apply (External.printedBase_literal _).mpr
  fin_cases i
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr (Or.inl ⟨false,by simp [externalAxes,signBit]⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨true,by simp [externalAxes,signBit,sub_eq_add_neg]⟩))

theorem externalAxes_span : Submodule.span ℂ (Set.range externalAxes)=⊤ := by
  apply top_unique
  rw [←sourceAxes_span]
  apply Submodule.span_le.mpr
  rintro U ⟨i,rfl⟩
  let W := Submodule.span ℂ (Set.range externalAxes)
  have ha (i : Fin 4) : externalAxes i∈W := Submodule.subset_span ⟨i,rfl⟩
  fin_cases i
  · exact ha 0
  · exact ha 1
  · change sourceAxes 2∈W
    have he : sourceAxes 2=(1/2 : ℂ) • (externalAxes 2+externalAxes 3) := by
      ext a b
      simp [sourceAxes,externalAxes,quaternionBasis]
      ring
    rw [he]
    exact W.smul_mem _ (W.add_mem (ha 2) (ha 3))
  · change sourceAxes 3∈W
    have he : sourceAxes 3=(1/2 : ℂ) • (externalAxes 2-externalAxes 3) := by
      ext a b
      simp [sourceAxes,externalAxes,quaternionBasis]
      ring
    rw [he]
    exact W.smul_mem _ (W.sub_mem (ha 2) (ha 3))

end
end Holant.Certificates.PlatonicAtlas
