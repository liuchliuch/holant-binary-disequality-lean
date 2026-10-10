import Holant.ReedMuller.FlatNetwork.OrdinaryNetwork
import Holant.ReedMuller.CoefficientAtlas.Code
import Holant.ReedMuller.FlatNetwork.Transvection

/-! Literal repetition/RM primitives and the exact weight-four transvection
input-output table of one RM vertex, in the manuscript's specified port order. -/
namespace Holant.ReedMuller.FlatNetwork
open Holant Holant.ReedMuller.LowArity
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000
attribute [local instance] Classical.propDecidable

def repetitionCode : BinaryCode 2 where
  carrier := {x | x 0=x 1}
  zero_mem' := rfl
  add_mem' := by intro x y hx hy;change x 0+y 0=x 1+y 1;rw [hx,hy]
  smul_mem' := by intro c x hx;change c*x 0=c*x 1;rw [hx]

@[simp] theorem mem_repetitionCode (x : BinaryVector 2) : x∈repetitionCode ↔ x 0=x 1 := Iff.rfl

theorem repetitionCode_selfDual : SelfDual repetitionCode := by
  change ∀ x : BinaryVector 2,(x 0=x 1) ↔ ∀ y : BinaryVector 2,y 0=y 1 → dot x y=0
  decide

theorem parityKernel_flat (eta : ZMod 2) : Flat (fun x : Fin 2 → Bool => parityKernel eta (x 0) (x 1)) := by
  refine ⟨1,![0,eta],repetitionCode,repetitionCode_selfDual,?_⟩
  funext x
  have hc : ∀ eta : ZMod 2,∀ a b : Bool,
      (boolEquiv a+boolEquiv b=eta) ↔ (bit a-0=bit b-eta) := by decide
  simp only [parityKernel,flatSignature,mem_repetitionCode,Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Units.val_one]
  simp only [hc]

def rmCore : Signature ℂ 8 := flatSignature 1 0 CoefficientAtlas.code

theorem rmCore_flat : Flat rmCore := ⟨1,0,CoefficientAtlas.code,CoefficientAtlas.code_selfDual,rfl⟩

def rmBoxPorts : Fin 8 ≃ Fin 8 where
  toFun := ![0,1,2,4,7,6,5,3]
  invFun := ![0,1,2,7,3,6,5,4]
  left_inv := by decide
  right_inv := by decide

def rmBoxWord (x y : BinaryVector 4) : BinaryVector 8 :=
  fun p => Fin.addCases x y (rmBoxPorts.symm p)

theorem rmBoxWord_mem_iff : ∀ x y : BinaryVector 4,
    rmBoxWord x y∈CoefficientAtlas.code ↔ y=transvection (ones 4) x := by
  change ∀ x y : BinaryVector 4,
    (∃ a : CoefficientAtlas.Param,CoefficientAtlas.evaluate a=rmBoxWord x y) ↔
      y=transvection (ones 4) x
  decide

/-- The displayed RM box has one lift for each input and implements exactly
x ↦ x+(sum x)·1; there is no freely supplied basis-change vertex. -/
theorem rmBox_unique_output (x : BinaryVector 4) :
    ∃! y,rmBoxWord x y∈CoefficientAtlas.code := by
  exact ⟨transvection (ones 4) x,(rmBoxWord_mem_iff x _).mpr rfl,
    fun y hy => (rmBoxWord_mem_iff x y).mp hy⟩

end
end Holant.ReedMuller.FlatNetwork
