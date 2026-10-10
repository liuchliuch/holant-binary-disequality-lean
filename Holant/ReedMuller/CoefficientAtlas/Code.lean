import Holant.ReedMuller.LowArity.Basic
import Mathlib.Tactic.FunProp

/-! The actual RM(1,3) evaluation code on the eight ordered points F₂³. -/
namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

abbrev Param := BinaryVector 4
abbrev Point := Fin 8

def pointBit (p : Point) (j : Fin 3) : ZMod 2 := if p.val.testBit j.val then 1 else 0

def evaluate (a : Param) (p : Point) : ZMod 2 :=
  a 0 + ∑ j : Fin 3, a j.succ * pointBit p j

def evaluation : Param →ₗ[ZMod 2] BinaryVector 8 where
  toFun := evaluate
  map_add' := by
    intro a b
    funext p
    simp [evaluate,add_mul,Finset.sum_add_distrib]
    ring
  map_smul' := by
    intro c a
    funext p
    simp [evaluate,Finset.mul_sum,mul_add,mul_assoc]

/-- RM(1,3), as the range of its actual affine evaluation map. -/
def code : BinaryCode 8 := LinearMap.range evaluation

def oneParam : Param := ![1,0,0,0]

def word (a : Param) : Point → Bool := fun p => decide (evaluate a p = 1)

theorem bit_word : ∀ a p, (if word a p then (1:ZMod 2) else 0) = evaluate a p := by decide

theorem evaluate_injective : Function.Injective evaluate := by decide

theorem word_injective : Function.Injective word := by decide

theorem evaluate_one : evaluate oneParam = fun _ => 1 := by decide

theorem evaluate_zero : evaluate 0 = 0 := by decide

/-- This is the actual orthogonality definition on the original eight ports. -/
theorem code_selfDual : SelfDual code := by
  intro x
  change (∃ a : Param, evaluate a = x) ↔
    ∀ y : BinaryVector 8, (∃ a : Param, evaluate a = y) → dot x y = 0
  constructor
  · rintro ⟨a,rfl⟩ y ⟨b,rfl⟩
    have h : ∀ a b : Param, dot (evaluate a) (evaluate b)=0 := by decide
    exact h a b
  · intro h
    have hh : ∀ a : Param, dot x (evaluate a)=0 := fun a => h _ ⟨a,rfl⟩
    have hc : ∀ x : BinaryVector 8,
        (∀ a : Param, dot x (evaluate a)=0) → ∃ a : Param, evaluate a=x := by decide
    exact hc x hh

theorem word_mem_code (a : Param) : (fun p => if word a p then (1:ZMod 2) else 0) ∈ code := by
  simp only [bit_word]
  exact ⟨a,rfl⟩

end Holant.ReedMuller.CoefficientAtlas
