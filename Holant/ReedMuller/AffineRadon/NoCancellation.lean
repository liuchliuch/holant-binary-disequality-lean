import Holant.ReedMuller.AffineRadon.Projection
import Holant.ReedMuller.AffineRadon.SupportDirection
import Holant.ReedMuller.RadonAccess.AffineQuotient

/-! Actual Radon support without overlap: an accessible direction outside the
original affine support direction gives at most one nonzero lift, so no
coefficient cancellation can alter its projected support. -/
namespace Holant.ReedMuller.AffineRadon
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork Holant.ReedMuller.RadonAccess
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def exactSupport (g : BinaryVector n → ℂ) (a : BinaryVector n) (U : BinaryCode n) : Prop :=
  ∀ x,g x≠0 ↔ x-a∈U

 theorem disjoint_support_translate (g : BinaryVector n → ℂ) (a v : BinaryVector n)
    (U : BinaryCode n) (hg : exactSupport g a U) (hv : v∉U) (x : BinaryVector n) :
    ¬(g x≠0 ∧ g (x+v)≠0) := by
  rintro ⟨h0,h1⟩
  have H := U.sub_mem ((hg _).mp h1) ((hg _).mp h0)
  have he : (x+v-a)-(x-a)=v := by abel
  exact hv (he ▸ H)

 theorem nonoverlap_sum_support (g : BinaryVector n → ℂ) (a v : BinaryVector n)
    (U : BinaryCode n) (hg : exactSupport g a U) (hv : v∉U) (x : BinaryVector n) :
    g x+g (x+v)≠0 ↔ x-a∈U ∨ x+v-a∈U := by
  have hd := disjoint_support_translate g a v U hg hv x
  rw [←hg x,←hg (x+v)]
  by_cases h0 : g x=0 <;> by_cases h1 : g (x+v)=0
  · simp [h0,h1]
  · simp [h0,h1]
  · simp [h0,h1]
  · exact False.elim (hd ⟨h0,h1⟩)

namespace RadonFrame

def boundaryLift (F : RadonAccess.RadonFrame n) (ε : ZMod 2) (x : BinaryVector (n-2)) : BinaryVector n :=
  ε • F.r+(F.ordinaryBoundaryLinearEquiv.symm x).val

def actualRadon (F : RadonAccess.RadonFrame n) (ε : ZMod 2) (g : BinaryVector n → ℂ) :
    BinaryVector (n-2) → ℂ := fun x => g (boundaryLift F ε x)+g (boundaryLift F ε x+F.v)

 theorem actualRadon_eq_quotient (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector (n-2)) :
    actualRadon F ε g x=F.radon ε g (F.iota ε (F.ordinaryBoundaryLinearEquiv.symm x)) := rfl

 theorem boundaryLift_layer (F : RadonAccess.RadonFrame n) (ε : ZMod 2) (x : BinaryVector (n-2)) :
    dot (boundaryLift F ε x) F.v=ε := by
  rw [boundaryLift,dot_add_left,dot_smul_left,F.dot_rv,mul_one]
  have hw := (F.ordinaryBoundaryLinearEquiv.symm x).property.2
  rw [dot_comm] at hw
  rw [hw,add_zero]

 theorem boundaryLift_projection (F : RadonAccess.RadonFrame n) (ε : ZMod 2) (x : BinaryVector (n-2)) :
    boundaryProjection F (boundaryLift F ε x)=x := by
  have H := projection_of_lift F ε 0 (F.ordinaryBoundaryLinearEquiv.symm x)
  simpa only [zero_smul,add_zero,LinearEquiv.apply_symm_apply,boundaryLift] using H

 theorem boundary_fiber (F : RadonAccess.RadonFrame n) (ε : ZMod 2) (x : BinaryVector (n-2))
    (y : BinaryVector n) (hy : dot y F.v=ε) :
    boundaryProjection F y=x ↔ y=boundaryLift F ε x ∨ y=boundaryLift F ε x+F.v := by
  constructor
  · intro hp
    have hd : dot (y-boundaryLift F ε x) F.v=0 := by
      have hsub : dot (y-boundaryLift F ε x) F.v=dot y F.v-dot (boundaryLift F ε x) F.v := by
        simp [dot,sub_mul,Finset.sum_sub_distrib]
      rw [hsub,hy,boundaryLift_layer,sub_self]
    have hz : boundaryProjection F (y-boundaryLift F ε x)=0 := by
      rw [map_sub,hp,boundaryLift_projection,sub_self]
    obtain ⟨b,hb⟩ := (hyperplane_kernel F _ hd).mp hz
    have cases2 : ∀ c : ZMod 2,c=0 ∨ c=1 := by decide
    rcases cases2 b with rfl | rfl
    · left
      simpa only [zero_smul,eq_comm,sub_eq_zero] using hb
    · right
      rw [one_smul] at hb
      have H := sub_eq_iff_eq_add.mp hb.symm
      simpa only [add_comm] using H
  · rintro (rfl | rfl)
    · exact boundaryLift_projection F ε x
    · rw [map_add,boundaryLift_projection,projection_v,add_zero]

/-- Literal projected support, with the original affine layer and projection. -/
theorem actualRadon_support_no_overlap (F : RadonAccess.RadonFrame n) (ε : ZMod 2)
    (g : BinaryVector n → ℂ) (a : BinaryVector n) (U : BinaryCode n)
    (hg : exactSupport g a U) (hv : F.v∉U) (x : BinaryVector (n-2)) :
    actualRadon F ε g x≠0 ↔
      ∃ y : BinaryVector n,y-a∈U ∧ dot y F.v=ε ∧ boundaryProjection F y=x := by
  rw [actualRadon,nonoverlap_sum_support g a F.v U hg hv]
  constructor
  · rintro (h | h)
    · exact ⟨boundaryLift F ε x,h,boundaryLift_layer F ε x,boundaryLift_projection F ε x⟩
    · refine ⟨boundaryLift F ε x+F.v,h,?_,?_⟩
      · rw [dot_add_left,boundaryLift_layer,F.dot_vv,add_zero]
      · rw [map_add,boundaryLift_projection,projection_v,add_zero]
  · rintro ⟨y,hy,hl,hp⟩
    rcases (boundary_fiber F ε x y hl).mp hp with rfl | rfl
    · exact Or.inl hy
    · exact Or.inr hy

end RadonFrame
end
end Holant.ReedMuller.AffineRadon
