import Holant.ReedMuller.TwoChart.Survival

/-! Assemble the bounded original-coordinate localizer from the two actual
quotient charts. Every projection and fiber-character condition is derived. -/
namespace Holant.ReedMuller.TwoChart
open Holant Holant.Tractable Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.CharacterFlat Holant.ReedMuller.AffineRadon Holant.ReedMuller.RadonAccess
open Geometry
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

 theorem complement_mem_liftDirection (F : RadonAccess.RadonFrame n)
    (D : BinaryCode (n-2)) (w : F.complement) :
    w.val∈liftDirection F D ↔ F.ordinaryBoundaryLinearEquiv w∈D := by
  have hp : RadonFrame.boundaryProjection F w.val=F.ordinaryBoundaryLinearEquiv w := by
    simpa only [zero_smul,zero_add,add_zero] using RadonFrame.projection_of_lift F 0 0 w
  have hv : dot w.val F.v=0 := by rw [dot_comm];exact w.property.2
  rw [mem_liftDirection,hv,hp]
  simp

structure LocalizingData (F : RadonAccess.RadonFrame n) (C₀ C₁ : Chart (n-2)) where
  space : BinaryCode n
  isotropic : BinaryCode n
  outputSize : ℕ
  coordinates : space ≃ₗ[ZMod 2] BinaryVector outputSize
  isometry : ∀ s t,dot (coordinates s) (coordinates t)=dot s.val t.val
  size_le : outputSize≤8
  size_even : Even outputSize
  selfOrthogonal : ∀ j∈isotropic,∀ k∈isotropic,dot j k=0
  orthogonal : ∀ s∈space,∀ j∈isotropic,dot s j=0
  halfDimension : outputSize+2*Module.finrank (ZMod 2) isotropic=n
  v_mem : F.v∈space
  r_mem : F.r∈space
  shift : BinaryVector n
  character : Character n
  shift_zero_mem : (liftChart F 0 C₀).shift-shift∈space
  shift_one_mem : (liftChart F 1 C₁).shift-shift∈space
  character_space : ∀ s∈space,character s=0
  character_zero : ∀ j : isotropic,character j.val=(liftChart F 0 C₀).character j.val
  character_one : ∀ j : isotropic,character j.val=(liftChart F 1 C₁).character j.val
  separator : C₀.direction≠C₁.direction → ∃ s t : BinaryVector n,
    s∈space ∧ t∈space ∧ s∈(liftChart F 0 C₀).direction ∧
      s∉(liftChart F 1 C₁).direction ∧ t∈(liftChart F 1 C₁).direction ∧ dot s t=1

 theorem exists_localizingData (F : RadonAccess.RadonFrame n) (hn : Even n)
    (C₀ C₁ : Chart (n-2)) : Nonempty (LocalizingData F C₀ C₁) := by
  obtain ⟨U,hΔ,hρ,hU,heU,hb,hbe,hsep⟩ := exists_chart_envelope F hn C₀ C₁
  let S := RadonGeometry.retainedSpace F U
  have hS := RadonGeometry.retainedSpace_nondegenerate F U hU
  obtain ⟨J,phi,hphi,hJ,hortho,hdim,hJP⟩ := RadonGeometry.exists_localizing_data F hn U hU heU
  let P := orthogonalProjection S hS
  let p := P (liftChart F 0 C₀).shift
  let chi := (liftChart F 0 C₀).character.comp P
  have hsame : P (liftChart F 0 C₀).shift=P (liftChart F 1 C₁).shift :=
    common_orthogonalProjection S hS _ _ (lifted_shift_difference_mem F C₀ C₁ U hΔ)
  refine ⟨{
    space := S
    isotropic := J
    outputSize := Module.finrank (ZMod 2) S
    coordinates := phi
    isometry := hphi
    size_le := RadonGeometry.retainedSpace_finrank_le_eight F U hb
    size_even := RadonGeometry.retainedSpace_even F U heU
    selfOrthogonal := hJ
    orthogonal := hortho
    halfDimension := hdim
    v_mem := RadonGeometry.v_mem_retainedSpace F U
    r_mem := RadonGeometry.r_mem_retainedSpace F U
    shift := p
    character := chi
    shift_zero_mem := sub_orthogonalProjection_mem S hS _
    shift_one_mem := ?_
    character_space := ?_
    character_zero := ?_
    character_one := ?_
    separator := ?_ }⟩
  · change (liftChart F 1 C₁).shift-P (liftChart F 0 C₀).shift∈S
    rw [hsame]
    exact sub_orthogonalProjection_mem S hS _
  · intro s hs
    change (liftChart F 0 C₀).character (P s)=0
    rw [orthogonalProjection_zero S hS s hs,map_zero]
  · intro j
    change (liftChart F 0 C₀).character (P j.val)=_
    rw [orthogonalProjection_fix S hS _ (hJP j.property)]
  · intro j
    change (liftChart F 0 C₀).character (P j.val)=_
    rw [orthogonalProjection_fix S hS _ (hJP j.property)]
    exact lifted_characters_agree_on_orthogonal F C₀ C₁ U hρ _ (hJP j.property)
  · intro hne
    obtain ⟨s,t,hsU,htU,hs,hsn,ht,hst⟩ := hsep hne
    refine ⟨s.val,t.val,RadonGeometry.mem_retainedSpace_of_mem F U s hsU,
      RadonGeometry.mem_retainedSpace_of_mem F U t htU,?_,?_,?_,hst⟩
    · exact (complement_mem_liftDirection F _ s).mpr hs
    · exact fun h => hsn ((complement_mem_liftDirection F _ s).mp h)
    · exact (complement_mem_liftDirection F _ t).mpr ht

end
end Holant.ReedMuller.TwoChart
