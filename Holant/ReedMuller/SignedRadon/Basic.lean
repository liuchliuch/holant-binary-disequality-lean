import Holant.ReedMuller.RadonAccess.PairCoordinates
import Holant.ReedMuller.CharacterFlat.Bell

/-! Literal signed Radon functions on the genuine two-point orbit quotient.
The exterior sign is indispensable for the minus card to descend. -/
namespace Holant.ReedMuller.SignedRadon
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.RadonAccess Holant.ReedMuller.CharacterFlat
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

namespace RadonFrame

def selected (F : RadonAccess.RadonFrame n) : Character n where
  toFun x := F.A x F.i
  map_add' := by intros;simp
  map_smul' := by intros;simp

@[simp] theorem selected_apply (F : RadonAccess.RadonFrame n) (x : BinaryVector n) :
    selected F x=F.A x F.i := rfl
@[simp] theorem selected_v (F : RadonAccess.RadonFrame n) : selected F F.v=1 := by
  simp [selected,F.distinct]
@[simp] theorem selected_r (F : RadonAccess.RadonFrame n) : selected F F.r=1 := by
  simp [selected]

theorem selected_eq_dot (F : RadonAccess.RadonFrame n) (x : BinaryVector n) :
    selected F x=dot x F.r := by
  change F.A x F.i=dot x F.r
  rw [←dot_unit_right (F.A x) F.i,OrthogonalMap.adjoint]
  rfl

@[simp] theorem selected_complement (F : RadonAccess.RadonFrame n) (w : F.complement) :
    selected F w=0 := by
  rw [selected_eq_dot,dot_comm]
  exact w.property.1

def numerator (F : RadonAccess.RadonFrame n) (l : ZMod 2) (g : BinaryVector n → ℂ)
    (x : BinaryVector n) : ℂ := g x+sign l*g (x+F.v)

def signedValue (F : RadonAccess.RadonFrame n) (l : ZMod 2) (g : BinaryVector n → ℂ)
    (x : BinaryVector n) : ℂ := sign (l*selected F x)*numerator F l g x

theorem signedValue_translate (F : RadonAccess.RadonFrame n) (l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector n) :
    signedValue F l g (x+F.v)=signedValue F l g x := by
  simp only [signedValue,numerator,map_add,selected_v,mul_add,mul_one,sign_add,
    add_assoc,binary_add_self,add_zero]
  have hs := sign_square l
  linear_combination sign (l*selected F x)*g x*hs

def signedCard (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) : F.Orbit d → ℂ :=
  Quotient.lift (fun x : F.Hyperplane d => signedValue F l g x.1) (by
    intro x y h
    rcases h with h|h
    · rw [h]
    · rw [h,signedValue_translate])

@[simp] theorem signedCard_orbit (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : F.Hyperplane d) :
    signedCard F d l g (F.orbit d x)=
      sign (l*F.A x.1 F.i)*(g x.1+sign l*g (x.1+F.v)) := rfl

@[simp] theorem signedValue_plus (F : RadonAccess.RadonFrame n) (g : BinaryVector n → ℂ)
    (x : BinaryVector n) : signedValue F 0 g x=g x+g (x+F.v) := by
  simp [signedValue,numerator]
@[simp] theorem signedValue_minus (F : RadonAccess.RadonFrame n) (g : BinaryVector n → ℂ)
    (x : BinaryVector n) : signedValue F 1 g x=sign (F.A x F.i)*(g x-g (x+F.v)) := by
  simp [signedValue,numerator,sub_eq_add_neg]

theorem strip_sign (F : RadonAccess.RadonFrame n) (l : ZMod 2)
    (g : BinaryVector n → ℂ) (x : BinaryVector n) :
    sign (l*F.A x F.i)*signedValue F l g x=g x+sign l*g (x+F.v) := by
  change sign (l*selected F x)*(sign (l*selected F x)*numerator F l g x)=_
  rw [←mul_assoc,sign_square,one_mul]
  rfl

@[simp] theorem signedCard_iota (F : RadonAccess.RadonFrame n) (d l : ZMod 2)
    (g : BinaryVector n → ℂ) (w : F.complement) :
    signedCard F d l g (F.iota d w)=
      sign (l*d)*(g (d • F.r+w)+sign l*g (d • F.r+w+F.v)) := by
  change signedValue F l g (d • F.r+w)=_
  simp only [signedValue,numerator,map_add,map_smul,selected_r,selected_complement,
    smul_eq_mul,mul_one,add_zero]

theorem support_equation (F : RadonAccess.RadonFrame n) (x : BinaryVector n) :
    F.A x F.i+F.A x F.j=dot x F.v := by
  rw [←dot_unit_right (F.A x) F.i,←dot_unit_right (F.A x) F.j,
    ←dot_add_right,F.A.adjoint]
  rfl

/-- The input and the two Bell X attachments cancel the global complement
exactly; this uses the actual orthogonal map's fixed all-one vector. -/
theorem native_coordinate (F : RadonAccess.RadonFrame n) (x : BinaryVector n) (i : Fin n) :
    F.A (x+ones n) i+1=F.A x i := by
  rw [F.A.map_add,F.A.fixes_ones]
  change (F.A x i+1)+1=F.A x i
  rw [add_assoc,add_self_zero,add_zero]

end RadonFrame
end
end Holant.ReedMuller.SignedRadon
