import Holant.ReedMuller.RadonAccess.Directions
import Mathlib.Algebra.Field.ZMod
import Mathlib.LinearAlgebra.BilinearForm.Orthogonal

/-! The literal binary dot form is nondegenerate. Consequently a
self-orthogonal code of half the original coordinate dimension is self-dual. -/
namespace Holant.ReedMuller.LowArity
open Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def dotBilinear : LinearMap.BilinForm (ZMod 2) (BinaryVector n) where
  toFun x :=
    { toFun y := dot x y
      map_add' := by intro y z;exact dot_add_right x y z
      map_smul' := by intro c y;exact dot_smul_right c x y }
  map_add' := by intro x y;apply LinearMap.ext;intro z;exact dot_add_left x y z
  map_smul' := by intro c x;apply LinearMap.ext;intro y;exact dot_smul_left c x y

@[simp] theorem dotBilinear_apply (x y : BinaryVector n) : dotBilinear x y=dot x y := rfl

theorem dotBilinear_nondegenerate : (dotBilinear (n:=n)).Nondegenerate := by
  constructor
  · intro x hx
    funext i
    have h := hx (unitWord i)
    change dot x (unitWord i)=0 at h
    exact (dot_unit_right x i).symm.trans h
  · intro x hx
    funext i
    have h := hx (unitWord i)
    change dot (unitWord i) x=0 at h
    exact (dot_unit_left x i).symm.trans h

 theorem selfDual_of_selfOrthogonal_halfDimension (D : BinaryCode n)
    (hD : ∀ x,x∈D → ∀ y,y∈D → dot x y=0)
    (hdim : 2*Module.finrank (ZMod 2) D=n) : SelfDual D := by
  let B := dotBilinear (n:=n)
  have hle : D≤B.orthogonal D := by
    intro x hx y hy
    exact hD y hy x hx
  have ho := LinearMap.BilinForm.finrank_orthogonal (B:=B) dotBilinear_nondegenerate D
  have hv : Module.finrank (ZMod 2) (BinaryVector n)=n := by simp [BinaryVector]
  rw [hv] at ho
  have heq : Module.finrank (ZMod 2) D=Module.finrank (ZMod 2) (B.orthogonal D) := by omega
  have he : D=B.orthogonal D := Submodule.eq_of_le_of_finrank_eq hle heq
  intro x
  constructor
  · exact hD x
  · intro hx
    rw [he]
    intro y hy
    change dot y x=0
    rw [dot_comm]
    exact hx y hy

end
end Holant.ReedMuller.LowArity
