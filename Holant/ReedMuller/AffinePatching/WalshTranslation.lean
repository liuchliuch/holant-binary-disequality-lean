import Holant.ReedMuller.AffinePatching.WalshInversion
import Holant.ReedMuller.CharacterFlat.Basic

/-! Exact orbit-sum/annihilating-hyperplane correspondence for the source
unnormalized Walsh transform, including its factor2. -/
namespace Holant.ReedMuller.AffinePatching
open Holant Holant.Tractable Holant.Tractable.AffinePhase
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {n : ℕ}

def binaryDot (x y : Word n) : ZMod 2 :=
  ∑ i,bitValue (ZMod 2) (x i)*bitValue (ZMod 2) (y i)
def algebraicSign (a : ZMod 2) : AlgebraicComplex := (CharacterFlat.intSign a : AlgebraicComplex)

theorem algebraicSign_add (a b : ZMod 2) : algebraicSign (a+b)=algebraicSign a*algebraicSign b := by
  simp only [algebraicSign,CharacterFlat.intSign_add,Int.cast_mul]

theorem algebraicSign_sum {I : Type*} (s : Finset I) (f : I → ZMod 2) :
    algebraicSign (∑ i∈s,f i)=∏ i∈s,algebraicSign (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => norm_num [algebraicSign,CharacterFlat.intSign]
  | @insert i s hi ih => simp [hi,algebraicSign_add,ih]

theorem hadamard_sign (a b : Bool) :
    hadamard a b=algebraicSign (bitValue (ZMod 2) a*bitValue (ZMod 2) b) := by
  cases a <;> cases b <;> norm_num [hadamard,algebraicSign,CharacterFlat.intSign,bitValue]

theorem walshKernel_dot (x y : Word n) : walshKernel x y=algebraicSign (binaryDot x y) := by
  simp only [walshKernel,hadamard_sign,binaryDot,algebraicSign_sum]

theorem hadamard_xor (a b c : Bool) : hadamard a (b^^c)=hadamard a b*hadamard a c := by
  cases a <;> cases b <;> cases c <;> norm_num [hadamard]

theorem walshKernel_xor (x y v : Word n) :
    walshKernel x (xor y v)=walshKernel x y*walshKernel x v := by
  simp only [walshKernel,AffinePhase.xor,hadamard_xor,Finset.prod_mul_distrib]

def xorEquiv (v : Word n) : Word n ≃ Word n where
  toFun y := xor y v
  invFun y := xor y v
  left_inv y := xor_cancel_right y v
  right_inv y := xor_cancel_right y v

theorem walsh_translate (f : Signature AlgebraicComplex n) (v x : Word n) :
    walsh (fun y => f (xor y v)) x=walshKernel x v*walsh f x := by
  unfold walsh
  rw [←(xorEquiv v).sum_comp]
  simp only [xorEquiv,Equiv.coe_fn_mk,xor_cancel_right,walshKernel_xor]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro y _
  ring

def hyperplaneMask (v : Word n) (f : Signature AlgebraicComplex n) : Signature AlgebraicComplex n :=
  fun x => if binaryDot x v=0 then f x else 0

theorem walsh_orbit_sum (f : Signature AlgebraicComplex n) (v : Word n) :
    walsh (fun y => f y+f (xor y v))=fun x => 2*hyperplaneMask v (walsh f) x := by
  funext x
  have h : walsh (fun y => f y+f (xor y v)) x=walsh f x+walsh (fun y => f (xor y v)) x := by
    simp only [walsh,mul_add,Finset.sum_add_distrib]
  rw [h,walsh_translate,walshKernel_dot]
  simp only [hyperplaneMask,algebraicSign,CharacterFlat.intSign]
  split_ifs <;> push_cast <;> ring

 theorem affine_hyperplaneMask_of_orbit_sum (f : Signature AlgebraicComplex n) (v : Word n)
    (h : Affine (fun y => f y+f (xor y v))) : Affine (hyperplaneMask v (walsh f)) := by
  have H := (walsh_affine _ h).scale (1/2)
  rw [walsh_orbit_sum] at H
  convert H using 1
  funext x
  ring

end
end Holant.ReedMuller.AffinePatching
