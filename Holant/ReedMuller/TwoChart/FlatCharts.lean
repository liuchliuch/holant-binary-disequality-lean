import Holant.ReedMuller.TwoChart.BoundaryObstruction
import Holant.ReedMuller.AffineRadon.Source

/-! Pure flat quotient charts admit representatives with literally zero
characters. Thus their localizer uses no phase-Bell resource. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n m : ℕ}

 theorem exists_flat_chart (f : Signature AlgebraicComplex n)
    (hf : FlatOrZero (fun x => (f x:ℂ))) : f=0 ∨ ∃ C : Chart n,C.character=0 ∧ f=C.eval := by
  rcases hf with hz|hf
  · left
    funext x
    apply Subtype.ext
    exact congrFun hz x
  obtain ⟨c,a,D,hc,hD,he⟩ := algebraic_flat_witness f hf
  refine Or.inr ⟨⟨c,hc,a,D,0,hD⟩,rfl,?_⟩
  funext x
  rw [he]
  simp only [Chart.eval,LinearMap.zero_apply,TwoTranslate.evenLift_zero,fourthRootPhase_zero,mul_one]

 theorem flat_gluing_obstruction (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (d : Character n) (f₀ f₁ : Signature AlgebraicComplex m)
    (h₀ : FlatOrZero (fun x => (f₀ x:ℂ))) (h₁ : FlatOrZero (fun x => (f₁ x:ℂ)))
    (hna : ¬Affine (glue p d f₀ f₁)) :
    ∃ C₀ C₁ : Chart m,C₀.character=0 ∧ C₁.character=0 ∧
      f₀=C₀.eval ∧ f₁=C₁.eval ∧
      (C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) := by
  rcases exists_flat_chart f₀ h₀ with rfl|⟨C₀,hc₀,rfl⟩
  · rcases exists_flat_chart f₁ h₁ with rfl|⟨C₁,hc₁,rfl⟩
    · apply False.elim
      apply hna
      convert affine_zero n using 1
      funext x
      simp [glue]
    · exact False.elim (hna (affine_glue_zero_left p d C₁))
  rcases exists_flat_chart f₁ h₁ with rfl|⟨C₁,hc₁,rfl⟩
  · exact False.elim (hna (affine_glue_zero_right p d C₀))
  refine ⟨C₀,C₁,hc₀,hc₁,rfl,rfl,?_⟩
  by_cases hD : C₀.direction=C₁.direction
  · right
    intro hratio
    exact hna (affine_glue_same p d C₀ C₁ hD hratio)
  · exact Or.inl hD

 theorem actual_flat_radon_chart_obstruction (F : RadonAccess.RadonFrame n)
    (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,FlatOrZero (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ C₀ C₁ : Chart (n-2),C₀.character=0 ∧ C₁.character=0 ∧
      algebraicRadon F 0 g=C₀.eval ∧ algebraicRadon F 1 g=C₁.eval ∧
      (C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) := by
  apply flat_gluing_obstruction (RadonFrame.boundaryProjection F) (layerLinear F)
    (algebraicRadon F 0 g) (algebraicRadon F 1 g)
  · exact hcards 0
  · exact hcards 1
  · rwa [←orbitPlus_glue]

end
end Holant.ReedMuller.TwoChart
