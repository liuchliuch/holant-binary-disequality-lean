import Holant.ReedMuller.AffineRadon.Projection
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

/-! Exact dimensions of the literal source-layer direction and its image in
ordinary remaining-port coordinates. The only losses are the kernel of the
layer equation and the actual translation line in the Radon projection. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

/-- The actual source-layer equation as a linear functional. -/
def layerFunctional (F : RadonAccess.RadonFrame n) : BinaryVector n →ₗ[ZMod 2] ZMod 2 where
  toFun x := dot x F.v
  map_add' x y := dot_add_left x y F.v
  map_smul' c x := dot_smul_left c x F.v

/-- Translation direction of the intersection of any nonempty affine support
with a Radon layer. -/
def layerDirection (F : RadonAccess.RadonFrame n) (U : BinaryCode n) : BinaryCode n :=
  U ⊓ LinearMap.ker (layerFunctional F)

@[simp] theorem mem_layerDirection (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (x : BinaryVector n) : x ∈ layerDirection F U ↔ x ∈ U ∧ dot x F.v=0 := Iff.rfl

/-- Its image uses exactly the ordinary surviving ports recorded by the frame. -/
def projectedLayerDirection (F : RadonAccess.RadonFrame n) (U : BinaryCode n) : BinaryCode (n-2) :=
  (layerDirection F U).map (boundaryProjection F)

@[simp] theorem mem_projectedLayerDirection (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (y : BinaryVector (n-2)) :
    y ∈ projectedLayerDirection F U ↔
      ∃ x : BinaryVector n, (x∈U ∧ dot x F.v=0) ∧ boundaryProjection F x=y := Iff.rfl

 theorem layerDirection_eq_of_perpendicular (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hU : ∀ x,x∈U → dot x F.v=0) : layerDirection F U=U := by
  ext x
  exact ⟨fun h => h.1,fun h => ⟨h,hU x h⟩⟩

 theorem layerDimension_of_perpendicular (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hU : ∀ x,x∈U → dot x F.v=0) :
    Module.finrank (ZMod 2) (layerDirection F U)=Module.finrank (ZMod 2) U := by
  rw [layerDirection_eq_of_perpendicular F U hU]

/-- Identifies the kernel inside `U` with the literal ambient intersection. -/
def layerKernelEquiv (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    LinearMap.ker ((layerFunctional F).comp U.subtype) ≃ₗ[ZMod 2] layerDirection F U where
  toFun x := ⟨x.val.val,x.val.property,x.property⟩
  invFun x := ⟨⟨x.val,x.property.1⟩,x.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

 theorem layerDimension_add_one_of_not_perpendicular (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hU : ¬∀ x,x∈U → dot x F.v=0) :
    Module.finrank (ZMod 2) (layerDirection F U)+1=Module.finrank (ZMod 2) U := by
  classical
  obtain ⟨x,hx,hv⟩ : ∃ x,x∈U ∧ dot x F.v≠0 := by simpa using hU
  let l := (layerFunctional F).comp U.subtype
  have hs : Function.Surjective l := by
    intro c
    refine ⟨⟨(c / dot x F.v) • x,U.smul_mem _ hx⟩,?_⟩
    change dot ((c / dot x F.v) • x) F.v=c
    rw [dot_smul_left,div_mul_cancel₀ _ hv]
  have h := l.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hs,finrank_top,Module.finrank_self] at h
  have hk := (layerKernelEquiv F U).finrank_eq
  change Module.finrank (ZMod 2) (LinearMap.ker l)=_ at hk
  omega

 theorem layerDimension_of_not_perpendicular (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hU : ¬∀ x,x∈U → dot x F.v=0) :
    Module.finrank (ZMod 2) (layerDirection F U)=Module.finrank (ZMod 2) U-1 := by
  have h := layerDimension_add_one_of_not_perpendicular F U hU
  omega

 theorem layerDimension_le (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    Module.finrank (ZMod 2) (layerDirection F U)≤Module.finrank (ZMod 2) U :=
  Submodule.finrank_mono inf_le_left

 theorem dimension_le_layerDimension_add_one (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    Module.finrank (ZMod 2) U≤Module.finrank (ZMod 2) (layerDirection F U)+1 := by
  classical
  by_cases h : ∀ x,x∈U → dot x F.v=0
  · rw [layerDimension_of_perpendicular F U h]
    omega
  · exact (layerDimension_add_one_of_not_perpendicular F U h).symm.le

/-- The literal map whose range is the projected layer direction. -/
def layerProjection (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    layerDirection F U →ₗ[ZMod 2] BinaryVector (n-2) :=
  (boundaryProjection F).comp (layerDirection F U).subtype

 theorem layerProjection_range (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    LinearMap.range (layerProjection F U)=projectedLayerDirection F U := by
  ext y
  constructor
  · rintro ⟨x,rfl⟩
    exact ⟨x.val,x.property,rfl⟩
  · rintro ⟨x,hx,hxy⟩
    exact ⟨⟨x,hx⟩,hxy⟩

 theorem layerProjection_ker_of_not_mem (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hv : F.v∉U) : LinearMap.ker (layerProjection F U)=⊥ := by
  apply LinearMap.ker_eq_bot'.mpr
  intro x hx
  obtain ⟨c,hc⟩ := (hyperplane_kernel F x.val x.property.2).mp hx
  have hz : c=0 := by
    by_contra hn
    have hmem : c • F.v∈U := hc.symm ▸ x.property.1
    have hback := U.smul_mem c⁻¹ hmem
    rw [smul_smul,inv_mul_cancel₀ hn,one_smul] at hback
    exact hv hback
  apply Subtype.ext
  simpa [hz] using hc.symm

 theorem projectedLayerDimension_of_not_mem (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hv : F.v∉U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)=
      Module.finrank (ZMod 2) (layerDirection F U) := by
  have h := (layerProjection F U).finrank_range_add_finrank_ker
  rw [layerProjection_range,layerProjection_ker_of_not_mem F U hv,finrank_bot,add_zero] at h
  exact h

 theorem layerProjection_kernelDimension_of_mem (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hv : F.v∈U) :
    Module.finrank (ZMod 2) (LinearMap.ker (layerProjection F U))=1 := by
  let v₀ : LinearMap.ker (layerProjection F U) :=
    ⟨⟨F.v,hv,F.dot_vv⟩,projection_v F⟩
  apply finrank_eq_one v₀
  · intro h
    exact F.v_ne_zero (congrArg (fun z => z.val.val) h)
  · intro x
    obtain ⟨c,hc⟩ := (hyperplane_kernel F x.val.val x.val.property.2).mp x.property
    refine ⟨c,?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hc

 theorem projectedLayerDimension_add_one_of_mem (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hv : F.v∈U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)+1=
      Module.finrank (ZMod 2) (layerDirection F U) := by
  have h := (layerProjection F U).finrank_range_add_finrank_ker
  rwa [layerProjection_range,layerProjection_kernelDimension_of_mem F U hv] at h

 theorem projectedLayerDimension_of_mem (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) (hv : F.v∈U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)=
      Module.finrank (ZMod 2) (layerDirection F U)-1 := by
  have h := projectedLayerDimension_add_one_of_mem F U hv
  omega


 theorem projectedLayerDimension_le_layerDimension (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)≤
      Module.finrank (ZMod 2) (layerDirection F U) := by
  have h := (layerProjection F U).finrank_range_add_finrank_ker
  rw [layerProjection_range] at h
  omega

 theorem layerDimension_le_projectedLayerDimension_add_one (F : RadonAccess.RadonFrame n)
    (U : BinaryCode n) :
    Module.finrank (ZMod 2) (layerDirection F U)≤
      Module.finrank (ZMod 2) (projectedLayerDirection F U)+1 := by
  classical
  by_cases hv : F.v∈U
  · exact (projectedLayerDimension_add_one_of_mem F U hv).symm.le
  · rw [projectedLayerDimension_of_not_mem F U hv]
    omega

 theorem projectedLayerDimension_le (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)≤Module.finrank (ZMod 2) U :=
  (projectedLayerDimension_le_layerDimension F U).trans (layerDimension_le F U)

 theorem dimension_le_projectedLayerDimension_add_one_of_not_mem
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n) (hv : F.v∉U) :
    Module.finrank (ZMod 2) U≤Module.finrank (ZMod 2) (projectedLayerDirection F U)+1 := by
  rw [projectedLayerDimension_of_not_mem F U hv]
  exact dimension_le_layerDimension_add_one F U

 theorem dimension_le_projectedLayerDimension_add_two
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n) :
    Module.finrank (ZMod 2) U≤Module.finrank (ZMod 2) (projectedLayerDirection F U)+2 := by
  have h₁ := dimension_le_layerDimension_add_one F U
  have h₂ := layerDimension_le_projectedLayerDimension_add_one F U
  omega

 theorem projectedLayerDimension_of_perpendicular_not_mem
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ∀ x,x∈U → dot x F.v=0) (hv : F.v∉U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)=Module.finrank (ZMod 2) U := by
  rw [projectedLayerDimension_of_not_mem F U hv,layerDimension_of_perpendicular F U hU]

 theorem projectedLayerDimension_add_one_of_not_perpendicular_not_mem
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ¬∀ x,x∈U → dot x F.v=0) (hv : F.v∉U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)+1=Module.finrank (ZMod 2) U := by
  rw [projectedLayerDimension_of_not_mem F U hv]
  exact layerDimension_add_one_of_not_perpendicular F U hU

 theorem projectedLayerDimension_add_one_of_perpendicular_mem
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ∀ x,x∈U → dot x F.v=0) (hv : F.v∈U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)+1=Module.finrank (ZMod 2) U := by
  rw [projectedLayerDimension_add_one_of_mem F U hv,layerDimension_of_perpendicular F U hU]

 theorem projectedLayerDimension_add_two_of_not_perpendicular_mem
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ¬∀ x,x∈U → dot x F.v=0) (hv : F.v∈U) :
    Module.finrank (ZMod 2) (projectedLayerDirection F U)+2=Module.finrank (ZMod 2) U := by
  have h₁ := projectedLayerDimension_add_one_of_mem F U hv
  have h₂ := layerDimension_add_one_of_not_perpendicular F U hU
  omega

/-- The projection preserves the literal form on the source translation
hyperplane; its one-dimensional kernel there is isotropic. -/
 theorem boundaryProjection_dot (F : RadonAccess.RadonFrame n)
    (x y : BinaryVector n) (hx : dot x F.v=0) (hy : dot y F.v=0) :
    dot (boundaryProjection F x) (boundaryProjection F y)=dot x y := by
  change dot (F.ordinaryBoundaryLinearEquiv (complementProjection F x))
    (F.ordinaryBoundaryLinearEquiv (complementProjection F y))=dot x y
  rw [F.ordinaryBoundaryLinearEquiv_isometry]
  change dot (F.complementPart x) (F.complementPart y)=dot x y
  have hx' : dot F.v x=0 := by rwa [dot_comm]
  have hy' : dot F.v y=0 := by rwa [dot_comm]
  simp only [RadonAccess.RadonFrame.complementPart,RadonAccess.RadonFrame.planePart,
    hx',hy',zero_smul,zero_add,add_zero,dot_add_left,dot_add_right,
    dot_smul_left,dot_smul_right,hx,F.dot_vv,mul_zero,add_zero]

 theorem selfOrthogonal_of_projected_selfOrthogonal
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ∀ x,x∈U → dot x F.v=0)
    (hP : ∀ x,x∈projectedLayerDirection F U →
      ∀ y,y∈projectedLayerDirection F U → dot x y=0) :
    ∀ x,x∈U → ∀ y,y∈U → dot x y=0 := by
  intro x hx y hy
  rw [←boundaryProjection_dot F x y (hU x hx) (hU y hy)]
  exact hP _ ⟨x,⟨hx,hU x hx⟩,rfl⟩ _ ⟨y,⟨hy,hU y hy⟩,rfl⟩

/-- A self-dual projected support forces self-duality upstairs whenever the
source direction is a half-dimensional subspace of the layer hyperplane. -/
 theorem selfDual_of_projected_selfDual
    (F : RadonAccess.RadonFrame n) (U : BinaryCode n)
    (hU : ∀ x,x∈U → dot x F.v=0)
    (hdim : 2*Module.finrank (ZMod 2) U=n)
    (hP : SelfDual (projectedLayerDirection F U)) : SelfDual U := by
  apply selfDual_of_selfOrthogonal_halfDimension U _ hdim
  apply selfOrthogonal_of_projected_selfOrthogonal F U hU
  intro x hx y hy
  exact (hP x).mp hx y hy

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
