import Holant.ReedMuller.SignedRadon.Coordinates

/-! Change of recorded frame for the same original-input direction. The
quotient transition is an affine isometry and the sign difference is an actual
linear character plus a recorded constant. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}
namespace RadonFrame

private theorem dot_complement_r (F : RadonAccess.RadonFrame n) (w : F.complement) :
    dot (w : BinaryVector n) F.r=0 := by rw [dot_comm];exact w.property.1
private theorem dot_complement_v (F : RadonAccess.RadonFrame n) (w : F.complement) :
    dot (w : BinaryVector n) F.v=0 := by rw [dot_comm];exact w.property.2

def transitionLinearMap (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) :
    F.complement →ₗ[ZMod 2] G.complement where
  toFun w := ⟨(w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v,by
    constructor
    · rw [dot_add_right,dot_smul_right,G.dot_rv,mul_one,dot_comm G.r]
      exact add_self_zero _
    · rw [dot_add_right,dot_smul_right,G.dot_vv,mul_zero,add_zero,←h]
      exact w.property.2⟩
  map_add' := by
    intro w z
    apply Subtype.ext
    change ((w : BinaryVector n)+(z : BinaryVector n))+dot ((w : BinaryVector n)+(z : BinaryVector n)) G.r • G.v=_
    rw [dot_add_left,add_smul]
    change (w : BinaryVector n)+(z : BinaryVector n)+(dot (w : BinaryVector n) G.r • G.v+dot (z : BinaryVector n) G.r • G.v)=
      ((w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v)+((z : BinaryVector n)+dot (z : BinaryVector n) G.r • G.v)
    abel
  map_smul' := by
    intro c w
    apply Subtype.ext
    change c • (w : BinaryVector n)+dot (c • (w : BinaryVector n)) G.r • G.v=_
    rw [dot_smul_left,mul_smul]
    simp only [RingHom.id_apply,Submodule.coe_smul_of_tower,smul_add]

theorem transitionLinearMap_inverse (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (w : F.complement) : transitionLinearMap G F h.symm (transitionLinearMap F G h w)=w := by
  apply Subtype.ext
  change (w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v+
    dot ((w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v) F.r • F.v=w
  rw [dot_add_left,dot_smul_left,←h,F.dot_vr,mul_one,dot_complement_r,zero_add]
  rw [add_assoc,←add_smul,add_self_zero,zero_smul,add_zero]

def transitionLinear (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) :
    F.complement ≃ₗ[ZMod 2] G.complement where
  __ := transitionLinearMap F G h
  invFun := transitionLinearMap G F h.symm
  left_inv := transitionLinearMap_inverse F G h
  right_inv := transitionLinearMap_inverse G F h.symm

theorem transitionLinear_isometry (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (w z : F.complement) :
    dot (transitionLinear F G h w : BinaryVector n) (transitionLinear F G h z)=
      dot (w : BinaryVector n) z := by
  change dot ((w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v)
    ((z : BinaryVector n)+dot (z : BinaryVector n) G.r • G.v)=_
  rw [←h]
  simp only [dot_add_left,dot_add_right,dot_smul_left,dot_smul_right,
    dot_complement_v,F.dot_vv,z.property.2,mul_zero,add_zero]

def transitionShift (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) (d : ZMod 2) : G.complement :=
  G.quotientCoordinate d ⟨d • F.r,by rw [←h,dot_smul_left,F.dot_rv,mul_one]⟩

def transitionComplement (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) (d : ZMod 2) :
    F.complement ≃ᵃ[ZMod 2] G.complement :=
  (transitionLinear F G h).toAffineEquiv.trans
    (AffineEquiv.vaddConst (ZMod 2) (transitionShift F G h d))

theorem transitionComplement_coordinate (F G : RadonAccess.RadonFrame n)
    (h : F.v=G.v) (d : ZMod 2) (w : F.complement) :
    transitionComplement F G h d w=
      G.quotientCoordinate d ⟨d • F.r+(w : BinaryVector n),by
        rw [←h,dot_add_left,dot_smul_left,F.dot_rv,mul_one,dot_complement_v,add_zero]⟩ := by
  apply Subtype.ext
  change (w : BinaryVector n)+dot (w : BinaryVector n) G.r • G.v+
    (d • F.r+d • G.r+(dot (d • F.r) G.r+d) • G.v)=
    (d • F.r+(w : BinaryVector n))+d • G.r+(dot (d • F.r+(w : BinaryVector n)) G.r+d) • G.v
  simp only [dot_add_left,add_smul]
  abel

def orbitChange (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) (d : ZMod 2) :
    F.Orbit d ≃ᵃ[ZMod 2] G.Orbit d :=
  ((F.quotientAffineEquiv d).symm.trans (transitionComplement F G h d)).trans
    (G.quotientAffineEquiv d)

theorem orbitChange_isometry (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) (d : ZMod 2)
    (w z : F.complement) :
    dot ((orbitChange F G h d).linear w : BinaryVector n) ((orbitChange F G h d).linear z)=
      dot (w : BinaryVector n) z := transitionLinear_isometry F G h w z

theorem orbitChange_iota (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (d : ZMod 2) (w : F.complement) :
    orbitChange F G h d (F.iota d w)=G.orbit d ⟨d • F.r+w,by
      rw [←h,dot_add_left,dot_smul_left,F.dot_rv,mul_one,dot_complement_v,add_zero]⟩ := by
  change G.iota d (transitionComplement F G h d (F.quotientToComplement d (F.iota d w)))=_
  rw [F.quotientToComplement_iota,transitionComplement_coordinate]
  exact G.iota_quotientToComplement d (G.orbit d ⟨d • F.r+(w : BinaryVector n),by
    rw [←h,dot_add_left,dot_smul_left,F.dot_rv,mul_one,dot_complement_v,add_zero]⟩)

/-- This affine transition is the identity on the underlying original-input
orbit. It does not choose a different geometric point of the quotient. -/
theorem orbitChange_orbit (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (d : ZMod 2) (x : F.Hyperplane d) :
    orbitChange F G h d (F.orbit d x)=G.orbit d ⟨x.1,by rw [←h];exact x.property⟩ := by
  conv_lhs => rw [←F.iota_quotientToComplement d (F.orbit d x)]
  rw [orbitChange_iota]
  apply Quotient.sound
  change d • F.r+(F.quotientToComplement d (F.orbit d x) : BinaryVector n)=x.1 ∨
    d • F.r+(F.quotientToComplement d (F.orbit d x) : BinaryVector n)=x.1+G.v
  rw [←h]
  exact Quotient.exact (F.iota_quotientToComplement d (F.orbit d x))

/-- The functional difference vanishes on v, so its restriction is a genuine
linear form on the quotient translation space. -/
def choiceCharacter (F G : RadonAccess.RadonFrame n) (l : ZMod 2) :
    F.complement →ₗ[ZMod 2] ZMod 2 :=
  l • ((selected G).comp F.complement.subtype)

def choiceConstant (F G : RadonAccess.RadonFrame n) (d l : ZMod 2) : ZMod 2 :=
  l*(selected G (d • F.r)+d)

theorem choice_selected_v (F G : RadonAccess.RadonFrame n) (h : F.v=G.v) :
    (selected F+selected G) F.v=0 := by
  change selected F F.v+selected G F.v=0
  rw [selected_v,h,selected_v,add_self_zero]

theorem signedValue_change (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (l : ZMod 2) (g : BinaryVector n → ℂ) (x : BinaryVector n) :
    signedValue G l g x=sign (l*(selected G x+selected F x))*signedValue F l g x := by
  unfold signedValue numerator
  rw [h,mul_add l (selected G x) (selected F x),sign_add]
  have hs := sign_square (l*selected F x)
  linear_combination -sign (l*selected G x)*(g x+sign l*g (x+G.v))*hs

theorem signedCard_change (F G : RadonAccess.RadonFrame n) (h : F.v=G.v)
    (d l : ZMod 2) (g : BinaryVector n → ℂ) (w : F.complement) :
    signedCard G d l g (orbitChange F G h d (F.iota d w))=
      sign (choiceConstant F G d l)*sign (choiceCharacter F G l w)*
        signedCard F d l g (F.iota d w) := by
  rw [orbitChange_iota]
  change signedValue G l g (d • F.r+w)=_ * _ * signedValue F l g (d • F.r+w)
  rw [signedValue_change F G h]
  have hs : l*(selected G (d • F.r+w)+selected F (d • F.r+w))=
      choiceConstant F G d l+choiceCharacter F G l w := by
    simp only [map_add,map_smul,selected_r,selected_complement,smul_eq_mul,mul_one,add_zero,
      choiceConstant,choiceCharacter,LinearMap.smul_apply,LinearMap.comp_apply,Submodule.subtype_apply]
    ring
  rw [hs,sign_add]

end RadonFrame
end
end Holant.ReedMuller.SignedRadon
