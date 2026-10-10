import Holant.ReedMuller.FlatNetwork.Parity

/-! Literal binary orthogonal transvections, with exact involution and
self-dual-code transport. These are the maps implemented by RM boxes. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

theorem dot_comm (x y : BinaryVector n) : dot x y=dot y x := by
  unfold dot
  apply Finset.sum_congr rfl
  intro i _
  ring

theorem dot_smul_left (c : ZMod 2) (x y : BinaryVector n) : dot (c • x) y=c*dot x y := by
  simp [dot,Finset.mul_sum,mul_assoc]

theorem dot_smul_right (c : ZMod 2) (x y : BinaryVector n) : dot x (c • y)=c*dot x y := by
  rw [dot_comm,dot_smul_left,dot_comm x y]

def transvection (s x : BinaryVector n) : BinaryVector n := x+dot x s • s

theorem transvection_involutive (s : BinaryVector n) (hs : dot s s=0) :
    Function.Involutive (transvection s) := by
  intro x
  simp only [transvection,dot_add_left,dot_smul_left,hs,mul_zero,add_zero]
  rw [add_assoc,←add_smul,add_self_zero,zero_smul,add_zero]

theorem transvection_selfAdjoint (s x y : BinaryVector n) :
    dot (transvection s x) y=dot x (transvection s y) := by
  simp only [transvection,dot_add_left,dot_add_right,dot_smul_left,dot_smul_right]
  rw [dot_comm s y]
  ring

theorem transvection_isometry (s : BinaryVector n) (hs : dot s s=0) (x y : BinaryVector n) :
    dot (transvection s x) (transvection s y)=dot x y := by
  rw [transvection_selfAdjoint,transvection_involutive s hs]

def transvectionLinear (s : BinaryVector n) : BinaryVector n →ₗ[ZMod 2] BinaryVector n where
  toFun := transvection s
  map_add' := by
    intro x y
    funext i
    simp [transvection,dot_add_left,add_mul,add_assoc,add_comm,add_left_comm]
  map_smul' := by
    intro c x
    funext i
    simp [transvection,dot_smul_left,mul_add,mul_assoc]

def transvectionCode (s : BinaryVector n) (D : BinaryCode n) : BinaryCode n :=
  D.map (transvectionLinear s)

theorem mem_transvectionCode (s : BinaryVector n) (hs : dot s s=0) (D : BinaryCode n)
    (x : BinaryVector n) : x∈transvectionCode s D ↔ transvection s x∈D := by
  constructor
  · rintro ⟨y,hy,rfl⟩
    change transvection s (transvection s y)∈D
    rw [transvection_involutive s hs]
    exact hy
  · intro hx
    exact ⟨transvection s x,hx,transvection_involutive s hs x⟩

theorem transvectionCode_selfDual (s : BinaryVector n) (hs : dot s s=0)
    (D : BinaryCode n) (hD : SelfDual D) : SelfDual (transvectionCode s D) := by
  intro x
  rw [mem_transvectionCode s hs D]
  constructor
  · intro hx y hy
    have hy' := (mem_transvectionCode s hs D y).mp hy
    have H := (hD (transvection s x)).mp hx (transvection s y) hy'
    simpa only [transvection_isometry s hs] using H
  · intro hx
    apply (hD _).mpr
    intro y hy
    have hm : transvection s y∈transvectionCode s D := ⟨y,hy,rfl⟩
    have H := hx (transvection s y) hm
    rwa [←transvection_selfAdjoint] at H

end
end Holant.ReedMuller.FlatNetwork
