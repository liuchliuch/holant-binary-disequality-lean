import Holant.ReedMuller.SupportReconstruction.Cards
import Holant.ReedMuller.LowArity.HalfDimension

/-! The source equal-pair slice code, with its literal parity lift on the
original deleted ports and the actual residual matching incidence. -/
noncomputable section
namespace Holant.ReedMuller.SupportReconstruction
open Holant.ReedMuller.LowArity Holant.ReedMuller.ZeroCardGraph
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n r : ℕ} {i j : Fin n}

 def sliceWord (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) : BinaryVector n :=
  fun k=>if hi : k=i then ∑e,t e else if hj : k=j then ∑e,t e else t (p.symm ⟨k,hi,hj⟩).1

 @[simp] theorem sliceWord_left (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) :
    sliceWord p t i=∑e,t e := by simp [sliceWord]
 @[simp] theorem sliceWord_right (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r) :
    sliceWord p t j=∑e,t e := by by_cases h : j=i <;> simp [sliceWord,h]
 @[simp] theorem sliceWord_port (p : (Fin r × Bool) ≃ Remaining i j) (t : BinaryVector r)
    (e : Fin r) (b : Bool) : sliceWord p t (p (e,b)).val=t e := by
  simp [sliceWord,(p (e,b)).property.1,(p (e,b)).property.2]

 def sliceLinear (p : (Fin r × Bool) ≃ Remaining i j) : BinaryVector r →ₗ[ZMod 2] BinaryVector n where
  toFun := sliceWord p
  map_add' := by
    intro x y
    funext k
    by_cases hi : k=i
    · simp [sliceWord,hi,Finset.sum_add_distrib]
    · by_cases hj : k=j <;> simp [sliceWord,hi,hj,Finset.sum_add_distrib]
  map_smul' := by
    intro c x
    funext k
    by_cases hi : k=i
    · simp [sliceWord,hi,Finset.mul_sum]
    · by_cases hj : k=j <;> simp [sliceWord,hi,hj,Finset.mul_sum]

 theorem sliceLinear_injective (p : (Fin r × Bool) ≃ Remaining i j) : Function.Injective (sliceLinear p) := by
  intro x y h
  funext e
  have hh := congrFun h (p (e,false)).val
  simpa only [sliceLinear,LinearMap.coe_mk,AddHom.coe_mk,sliceWord_port] using hh

 def sliceCode (p : (Fin r × Bool) ≃ Remaining i j) : BinaryCode n := LinearMap.range (sliceLinear p)

 theorem mem_sliceCode (p : (Fin r × Bool) ≃ Remaining i j) (x : BinaryVector n) :
    x∈sliceCode p ↔ ∃t : BinaryVector r,sliceWord p t=x := Iff.rfl

 theorem sliceCode_finrank (p : (Fin r × Bool) ≃ Remaining i j) :
    Module.finrank (ZMod 2) (sliceCode p)=r := by
  have he := (LinearEquiv.ofInjective (sliceLinear p) (sliceLinear_injective p)).finrank_eq
  simpa [sliceCode] using he.symm

 theorem sliceCode_equal (p : (Fin r × Bool) ≃ Remaining i j) (x : BinaryVector n)
    (hx : x∈sliceCode p) : x i=x j := by
  obtain ⟨t,rfl⟩ := hx
  simp [sliceLinear]

 theorem sliceCode_matching (p : (Fin r × Bool) ≃ Remaining i j) (x : BinaryVector n)
    (hx : x∈sliceCode p) : ∀e,x (p (e,false)).val=x (p (e,true)).val := by
  obtain ⟨t,rfl⟩ := hx
  intro e
  simp [sliceLinear]

 theorem slice_port_count (p : (Fin r × Bool) ≃ Remaining i j) (hij : i≠j) : 2*r+2=n := by
  have hp := Fintype.card_congr p
  have hn := remaining_card_add_two i j hij
  simp only [Fintype.card_prod,Fintype.card_fin,Fintype.card_bool] at hp hn
  omega

end Holant.ReedMuller.SupportReconstruction
