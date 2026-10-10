import Holant.ReedMuller.TwoChart.OneChart

/-! Actual algebraic chart representatives and the exhaustive obstruction to
nonaffine gluing. Vanishing charts and compatible fourth-root scales are
eliminated by constructed affine formulas. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.CharacterRecognition
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

structure Chart (n : ℕ) where
  scalar : AlgebraicComplex
  nonzero : scalar≠0
  shift : BinaryVector n
  direction : BinaryCode n
  character : Character n
  selfDual : SelfDual direction

def Chart.eval (C : Chart n) : Signature AlgebraicComplex n := fun x =>
  if vectorWord x-C.shift∈C.direction then
    C.scalar*fourthRootPhase (evenLift (C.character (vectorWord x))) else 0

theorem exists_chart (f : Signature AlgebraicComplex n)
    (hf : CFlat (fun x => (f x:ℂ))) : f=0 ∨ ∃ C : Chart n,f=C.eval := by
  by_cases hz : f=0
  · exact Or.inl hz
  obtain ⟨c,a,D,ell,hc,hD,he⟩ := algebraic_character_witness f hz hf
  right
  refine ⟨⟨c,hc,a,D,ell,hD⟩,?_⟩
  funext x
  apply Subtype.ext
  rw [he]
  change (if vectorWord x-a∈D then (c:ℂ)*sign (ell (vectorWord x)) else 0)=
    ((if vectorWord x-a∈D then c*fourthRootPhase (evenLift (ell (vectorWord x))) else 0):AlgebraicComplex)
  by_cases hx : vectorWord x-a∈D
  · rw [if_pos hx,if_pos hx]
    change (c:ℂ)*sign (ell (vectorWord x))=(c:ℂ)*root (evenLift (ell (vectorWord x)))
    rw [root_evenLift]
  · rw [if_neg hx,if_neg hx]
    rfl

def glue (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m) (d : Character n)
    (f₀ f₁ : Signature AlgebraicComplex m) : Signature AlgebraicComplex n := fun x =>
  if d (vectorWord x)=0 then f₀ (wordVector (p (vectorWord x)))
    else f₁ (wordVector (p (vectorWord x)))

 theorem affine_glue_zero_left (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (d : Character n) (C : Chart m) : Affine (glue p d 0 C.eval) := by
  convert affine_one_chart C.scalar p d 1 C.shift C.direction C.character using 1
  funext x
  rcases binary_cases (d (vectorWord x)) with hd|hd
  · simp only [glue,hd,ite_true,Pi.zero_apply,show (0:ZMod 2)≠1 by decide,ite_false]
  · simp only [glue,hd,show (1:ZMod 2)≠0 by decide,ite_false,ite_true,Chart.eval,vector_word]

 theorem affine_glue_zero_right (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (d : Character n) (C : Chart m) : Affine (glue p d C.eval 0) := by
  convert affine_one_chart C.scalar p d 0 C.shift C.direction C.character using 1
  funext x
  simp only [glue,Chart.eval,vector_word,Pi.zero_apply]

 theorem affine_glue_same (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (d : Character n) (C₀ C₁ : Chart m) (hD : C₀.direction=C₁.direction)
    (hratio : (C₁.scalar/C₀.scalar)^4=1) : Affine (glue p d C₀.eval C₁.eval) := by
  obtain ⟨q,hq⟩ := fourthRootPhase_surjective_of_pow_four hratio
  have hc : C₀.scalar*fourthRootPhase q=C₁.scalar := by
    rw [hq]
    field_simp [C₀.nonzero]
  convert affine_same_direction_gluing C₀.scalar q p d C₀.shift C₁.shift
    C₀.direction C₀.character C₁.character using 1
  funext x
  simp only [glue,Chart.eval,vector_word,hD,hc]

/-- Nonaffinity forces two actual nonzero charts and precisely a differing
support direction or a forbidden fourth-root layer ratio. -/
theorem nonaffine_gluing_obstruction (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m)
    (d : Character n) (f₀ f₁ : Signature AlgebraicComplex m)
    (h₀ : CFlat (fun x => (f₀ x:ℂ))) (h₁ : CFlat (fun x => (f₁ x:ℂ)))
    (hna : ¬Affine (glue p d f₀ f₁)) :
    ∃ C₀ C₁ : Chart m,f₀=C₀.eval ∧ f₁=C₁.eval ∧
      (C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) := by
  rcases exists_chart f₀ h₀ with rfl|⟨C₀,rfl⟩
  · rcases exists_chart f₁ h₁ with rfl|⟨C₁,rfl⟩
    · apply False.elim
      apply hna
      convert affine_zero n using 1
      funext x
      simp [glue]
    · exact False.elim (hna (affine_glue_zero_left p d C₁))
  rcases exists_chart f₁ h₁ with rfl|⟨C₁,rfl⟩
  · exact False.elim (hna (affine_glue_zero_right p d C₀))
  refine ⟨C₀,C₁,rfl,rfl,?_⟩
  by_cases hD : C₀.direction=C₁.direction
  · right
    intro hratio
    exact hna (affine_glue_same p d C₀ C₁ hD hratio)
  · exact Or.inl hD

end
end Holant.ReedMuller.TwoChart
