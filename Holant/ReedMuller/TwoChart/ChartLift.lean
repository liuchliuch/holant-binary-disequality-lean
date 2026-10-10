import Holant.ReedMuller.TwoChart.Relation

/-! Lift each actual quotient chart to its original layer and translation
line. Its direction is self-dual in the full original space, not merely an
abstract isomorphic code. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

 def liftDirection (F : RadonAccess.RadonFrame n) (D : BinaryCode (n-2)) : BinaryCode n :=
  LinearMap.ker (RadonFrame.layerFunctional F) ⊓ D.comap (RadonFrame.boundaryProjection F)

 theorem mem_liftDirection (F : RadonAccess.RadonFrame n) (D : BinaryCode (n-2)) (x : BinaryVector n) :
    x∈liftDirection F D ↔ dot x F.v=0 ∧ RadonFrame.boundaryProjection F x∈D := Iff.rfl

 theorem liftDirection_selfDual (F : RadonAccess.RadonFrame n)
    (D : BinaryCode (n-2)) (hD : SelfDual D) : SelfDual (liftDirection F D) := by
  intro x
  constructor
  · rintro ⟨hx,hPx⟩ y ⟨hy,hPy⟩
    rw [←RadonFrame.boundaryProjection_dot F x y hx hy]
    exact (hD _).mp hPx _ hPy
  · intro hx
    have hv : F.v∈liftDirection F D := ⟨F.dot_vv,by change RadonFrame.boundaryProjection F F.v∈D;rw [RadonFrame.projection_v];exact D.zero_mem⟩
    have hxv := hx F.v hv
    refine ⟨hxv,(hD _).mpr ?_⟩
    intro y hy
    let w := RadonFrame.boundaryLift F 0 y
    have hwv : dot w F.v=0 := RadonFrame.boundaryLift_layer F 0 y
    have hwp : RadonFrame.boundaryProjection F w=y := RadonFrame.boundaryLift_projection F 0 y
    have hw : w∈liftDirection F D := ⟨hwv,by change RadonFrame.boundaryProjection F w∈D;rwa [hwp]⟩
    rw [←hwp,RadonFrame.boundaryProjection_dot F x w hxv hwv]
    exact hx w hw

 theorem liftDirection_coset (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (a : BinaryVector (n-2)) (D : BinaryCode (n-2)) (x : BinaryVector n) :
    x-RadonFrame.boundaryLift F d a∈liftDirection F D ↔
      dot x F.v=d ∧ RadonFrame.boundaryProjection F x-a∈D := by
  rw [mem_liftDirection,map_sub,RadonFrame.boundaryLift_projection]
  have he : dot (x-RadonFrame.boundaryLift F d a) F.v=dot x F.v-d := by
    have hs : dot (x-RadonFrame.boundaryLift F d a) F.v=
        dot x F.v-dot (RadonFrame.boundaryLift F d a) F.v := by
      simp [LowArity.dot,sub_mul,Finset.sum_sub_distrib]
    rw [hs,RadonFrame.boundaryLift_layer]
  rw [he,sub_eq_zero]

 def liftChart (F : RadonAccess.RadonFrame n) (d : ZMod 2) (C : Chart (n-2)) : Chart n where
  scalar := C.scalar
  nonzero := C.nonzero
  shift := RadonFrame.boundaryLift F d C.shift
  direction := liftDirection F C.direction
  character := C.character.comp (RadonFrame.boundaryProjection F)
  selfDual := liftDirection_selfDual F C.direction C.selfDual

 theorem liftChart_eval (F : RadonAccess.RadonFrame n) (d : ZMod 2)
    (C : Chart (n-2)) (x : Word n) :
    (liftChart F d C).eval x=if dot (vectorWord x) F.v=d then
      C.eval (wordVector (RadonFrame.boundaryProjection F (vectorWord x))) else 0 := by
  simp only [Chart.eval,liftChart,LinearMap.comp_apply,vector_word,liftDirection_coset]
  by_cases hl : dot (vectorWord x) F.v=d <;>
    by_cases hs : RadonFrame.boundaryProjection F (vectorWord x)-C.shift∈C.direction <;>
    simp [hl,hs]

 theorem liftDirection_injective (F : RadonAccess.RadonFrame n) :
    Function.Injective (liftDirection F) := by
  intro D E h
  ext y
  have hh := SetLike.ext_iff.mp h (RadonFrame.boundaryLift F 0 y)
  simpa only [mem_liftDirection,RadonFrame.boundaryLift_layer,RadonFrame.boundaryLift_projection,
    true_and] using hh

 theorem orbitPlus_eq_lifted_charts (F : RadonAccess.RadonFrame n)
    (g : Signature AlgebraicComplex n) (C₀ C₁ : Chart (n-2))
    (h₀ : algebraicRadon F 0 g=C₀.eval) (h₁ : algebraicRadon F 1 g=C₁.eval) :
    orbitPlus F.v g=fun x => (liftChart F 0 C₀).eval x+(liftChart F 1 C₁).eval x := by
  rw [orbitPlus_glue,h₀,h₁]
  funext x
  rw [liftChart_eval,liftChart_eval]
  rcases binary_cases (dot (vectorWord x) F.v) with h|h <;>
    simp [glue,layerLinear,h]

end
end Holant.ReedMuller.TwoChart
