import Holant.ReedMuller.RadonAccess.Coordinates
import Holant.ReedMuller.LowArity.HalfDimension

/-! The actual Radon quotient projection, including its literal kernel on the
source layer hyperplane. All geometry uses the recorded orthogonal frame. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

def complementProjection (F : RadonAccess.RadonFrame n) : BinaryVector n →ₗ[ZMod 2] F.complement where
  toFun x := ⟨F.complementPart x,F.complementPart_mem x⟩
  map_add' := by
    intro x y
    apply Subtype.ext
    change F.complementPart (x+y)=F.complementPart x+F.complementPart y
    simp only [RadonAccess.RadonFrame.complementPart,RadonAccess.RadonFrame.planePart,dot_add_right,add_smul]
    abel
  map_smul' := by
    intro c x
    apply Subtype.ext
    change F.complementPart (c • x)=c • F.complementPart x
    simp only [RadonAccess.RadonFrame.complementPart,RadonAccess.RadonFrame.planePart,
      dot_smul_right,smul_eq_mul,mul_add,smul_add,mul_smul]
    funext i
    simp only [Pi.add_apply,Pi.smul_apply,smul_eq_mul]
    ring

def boundaryProjection (F : RadonAccess.RadonFrame n) : BinaryVector n →ₗ[ZMod 2] BinaryVector (n-2) :=
  F.ordinaryBoundaryLinearEquiv.toLinearMap.comp (complementProjection F)

 theorem projection_zero_iff (F : RadonAccess.RadonFrame n) (x : BinaryVector n) :
    boundaryProjection F x=0 ↔ F.complementPart x=0 := by
  change F.ordinaryBoundaryLinearEquiv (complementProjection F x)=0 ↔ _
  rw [LinearEquiv.map_eq_zero_iff]
  exact Subtype.val_injective.eq_iff.symm

 theorem projection_v (F : RadonAccess.RadonFrame n) : boundaryProjection F F.v=0 := by
  rw [projection_zero_iff]
  simp only [RadonAccess.RadonFrame.complementPart,RadonAccess.RadonFrame.planePart,F.dot_vv,F.dot_rv,zero_smul,add_zero,one_smul,zero_add]
  exact RadonAccess.binary_add_self _

 theorem hyperplane_kernel (F : RadonAccess.RadonFrame n) (x : BinaryVector n)
    (hx : dot x F.v=0) :
    boundaryProjection F x=0 ↔ ∃ t : ZMod 2,t • F.v=x := by
  constructor
  · intro hp
    have hc := (projection_zero_iff F x).mp hp
    refine ⟨dot F.r x,?_⟩
    have H := F.decomposition x
    rw [hc,add_zero] at H
    have hv : dot F.v x=0 := by rwa [dot_comm]
    simpa [RadonAccess.RadonFrame.planePart,hv] using H.symm
  · rintro ⟨t,rfl⟩
    rw [map_smul,projection_v,smul_zero]

 theorem projection_of_lift (F : RadonAccess.RadonFrame n) (ε b : ZMod 2)
    (w : F.complement) :
    boundaryProjection F (ε • F.r+(w:BinaryVector n)+b • F.v)=F.ordinaryBoundaryLinearEquiv w := by
  change F.ordinaryBoundaryLinearEquiv (complementProjection F _)=_
  congr 1
  apply Subtype.ext
  change F.complementPart _=w.val
  simp only [RadonAccess.RadonFrame.complementPart,RadonAccess.RadonFrame.planePart,
    dot_add_right,dot_smul_right,F.dot_rr,F.dot_rv,F.dot_vr,F.dot_vv,
    w.property.1,w.property.2,mul_one,mul_zero,add_zero,zero_add]
  simp only [add_smul]
  abel_nf
  simp

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
