import Holant.ReedMuller.TwoChart.AffineCharts

/-! Constructive affine gluing of two character charts with a common support
direction and a fourth-root layer ratio. No phase or support witness is assumed
for the glued tensor; both are built from literal linear maps. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffinePatching
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {m n : ℕ}

 theorem affine_linear_fourth_phase (L : Character n) (q : ZMod 4) :
    Affine (fun x => fourthRootPhase (q*bitLift (L (vectorWord x)))) := by
  apply affine_phase_of_thirdDifference
  intro z u v w
  rw [thirdDifference_mul_const]
  have hh : thirdDifference (fun x => bitLift (L (vectorWord x))) z u v w=0 := by
    simp only [thirdDifference,vector_xor,map_add]
    generalize L (vectorWord z)=a
    generalize L (vectorWord u)=b
    generalize L (vectorWord v)=c
    generalize L (vectorWord w)=d
    fin_cases a <;> fin_cases b <;> fin_cases c <;> fin_cases d <;> decide
  rw [hh,mul_zero]

 theorem affine_bilinear_sign (L M : Character n) :
    Affine (fun x => fourthRootPhase (evenLift (L (vectorWord x)*M (vectorWord x)))) := by
  apply affine_phase_of_thirdDifference
  intro z u v w
  simp only [thirdDifference,vector_xor,map_add]
  generalize L (vectorWord z)=a₀
  generalize L (vectorWord u)=a₁
  generalize L (vectorWord v)=a₂
  generalize L (vectorWord w)=a₃
  generalize M (vectorWord z)=b₀
  generalize M (vectorWord u)=b₁
  generalize M (vectorWord v)=b₂
  generalize M (vectorWord w)=b₃
  fin_cases a₀ <;> fin_cases a₁ <;> fin_cases a₂ <;> fin_cases a₃ <;>
    fin_cases b₀ <;> fin_cases b₁ <;> fin_cases b₂ <;> fin_cases b₃ <;> decide

 theorem affine_linear_pullback_coset (c : AlgebraicComplex) (a : BinaryVector m)
    (D : BinaryCode m) (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m) :
    ∃ S : AffineSystem n,∀ x,S.Holds x ↔ p (vectorWord x)-a∈D := by
  obtain ⟨T,hT⟩ := exists_coset_system a D
  refine ⟨T.pullback (affineBoolean 0 p),?_⟩
  intro x
  rw [AffineSystem.pullback_holds _ _ (affineBoolean_isAffine 0 p),hT]
  simp only [affineBoolean,vector_word,zero_add]

/-- The displayed two-layer function has actual source affine equations and
an actual modulo-four quadratic phase, even when either support shift lies
outside the common direction. -/
theorem affine_same_direction_gluing (c : AlgebraicComplex) (q : ZMod 4)
    (p : BinaryVector n →ₗ[ZMod 2] BinaryVector m) (d : Character n)
    (a₀ a₁ : BinaryVector m) (D : BinaryCode m) (ell₀ ell₁ : Character m) :
    Affine (fun x => if d (vectorWord x)=0 then
      (if p (vectorWord x)-a₀∈D then c*fourthRootPhase (evenLift (ell₀ (p (vectorWord x)))) else 0)
      else (if p (vectorWord x)-a₁∈D then
        (c*fourthRootPhase q)*fourthRootPhase (evenLift (ell₁ (p (vectorWord x)))) else 0)) := by
  let L₀ := ell₀.comp p
  let Lδ := (ell₁-ell₀).comp p
  let P := p-d.smulRight (a₁-a₀)
  obtain ⟨S,hS⟩ := affine_linear_pullback_coset c a₀ D P
  have h := ((((affine_linear_sign L₀).mul (affine_linear_fourth_phase d q)).mul
    (affine_bilinear_sign d Lδ)).scale c).restrict S
  convert h using 1
  funext x
  rcases binary_cases (d (vectorWord x)) with hd|hd
  · have hp : P (vectorWord x)-a₀=p (vectorWord x)-a₀ := by
      simp only [P,LinearMap.sub_apply,LinearMap.smulRight_apply,hd,zero_smul,sub_zero]
    simp only [hd,ite_true,hS,hp,L₀,LinearMap.comp_apply,bitLift_zero,mul_zero,
      fourthRootPhase_zero,zero_mul,evenLift_zero,mul_one]
  · have hp : P (vectorWord x)-a₀=p (vectorWord x)-a₁ := by
      simp only [P,LinearMap.sub_apply,LinearMap.smulRight_apply,hd,one_smul]
      abel
    have he : evenLift (L₀ (vectorWord x))+evenLift (Lδ (vectorWord x))=
        evenLift (ell₁ (p (vectorWord x))) := by
      rw [←evenLift_add]
      simp only [L₀,Lδ,LinearMap.comp_apply,LinearMap.sub_apply,add_sub_cancel]
    simp only [hd,show (1:ZMod 2)≠0 by decide,ite_false,hS,hp,bitLift_one,mul_one,one_mul]
    by_cases hs : p (vectorWord x)-a₁∈D
    · rw [if_pos hs,if_pos hs]
      have hphase : fourthRootPhase (L₀ (vectorWord x) |> evenLift)*
          fourthRootPhase (Lδ (vectorWord x) |> evenLift)=
          fourthRootPhase (evenLift (ell₁ (p (vectorWord x)))) := by
        rw [←fourthRootPhase_add,he]
      rw [←hphase]
      ring
    · rw [if_neg hs,if_neg hs]

end
end Holant.ReedMuller.TwoChart
