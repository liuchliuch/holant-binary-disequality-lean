import Holant.ReedMuller.TwoChart.ChartObstruction
import Holant.ReedMuller.AffinePatching.Source

/-! The two literal quotient charts reconstruct the original orbit-sum tensor
exactly. Their support/phase obstruction is derived from its nonaffinity. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def algebraicRadon (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (g : Signature AlgebraicComplex n) : Signature AlgebraicComplex (n-2) := fun x =>
  g (wordVector (RadonFrame.boundaryLift F d (vectorWord x)))+
    g (wordVector (RadonFrame.boundaryLift F d (vectorWord x)+F.v))

theorem algebraicRadon_coe (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (g : Signature AlgebraicComplex n) (x : Word (n-2)) :
    (algebraicRadon F d g x:ℂ)=
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x) := rfl

def layerLinear (F : RadonAccess.RadonFrame n) : Character n where
  toFun x := dot x F.v
  map_add' := by intros;exact dot_add_left _ _ _
  map_smul' := by intros;exact dot_smul_left _ _ _

 theorem orbitPlus_glue (F : RadonAccess.RadonFrame n) (g : Signature AlgebraicComplex n) :
    orbitPlus F.v g=glue (RadonFrame.boundaryProjection F) (layerLinear F)
      (algebraicRadon F 0 g) (algebraicRadon F 1 g) := by
  funext x
  apply Subtype.ext
  have hh := RadonFrame.actualRadon_projection F (fun y => (g (wordVector y):ℂ)) (vectorWord x)
  have hword : wordVector (vectorWord x+F.v)=xor x (wordVector F.v) := by
    rw [AffinePatching.word_add,word_vector]
  rcases binary_cases (dot (vectorWord x) F.v) with hd|hd
  · simp only [orbitPlus,glue,layerLinear,LinearMap.coe_mk,AddHom.coe_mk,hd,ite_true]
    rw [algebraicRadon_coe,vector_word,←hd,hh,word_vector,hword]
    rfl
  · simp only [orbitPlus,glue,layerLinear,LinearMap.coe_mk,AddHom.coe_mk,hd,
      show (1:ZMod 2)≠0 by decide,ite_false]
    rw [algebraicRadon_coe,vector_word,←hd,hh,word_vector,hword]
    rfl

/-- Both chart presentations and the entire obstruction are conclusions from
the actual zero-or-character-flat plus cards and original nonaffine orbit sum. -/
theorem actual_radon_chart_obstruction (F : RadonAccess.RadonFrame n)
    (g : Signature AlgebraicComplex n)
    (hcards : ∀ d,CFlat (fun x =>
      RadonFrame.actualRadon F d (fun y => (g (wordVector y):ℂ)) (vectorWord x)))
    (hna : ¬Affine (orbitPlus F.v g)) :
    ∃ C₀ C₁ : Chart (n-2),algebraicRadon F 0 g=C₀.eval ∧
      algebraicRadon F 1 g=C₁.eval ∧
      (C₀.direction≠C₁.direction ∨ (C₁.scalar/C₀.scalar)^4≠1) := by
  apply nonaffine_gluing_obstruction (RadonFrame.boundaryProjection F) (layerLinear F)
    (algebraicRadon F 0 g) (algebraicRadon F 1 g)
  · exact hcards 0
  · exact hcards 1
  · rwa [←orbitPlus_glue]

end
end Holant.ReedMuller.TwoChart
