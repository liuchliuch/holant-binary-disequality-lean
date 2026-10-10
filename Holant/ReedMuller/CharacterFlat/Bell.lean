import Holant.ReedMuller.CharacterFlat.OrdinaryNetwork

/-! The source's ordered Bell convention, including its literal first-port
sign and the genuine shifted repetition support. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable

def bellKernel (d l : ZMod 2) : Kernel ℂ :=
  fun a b => sign (l*bit a)*parityKernel d a b

def bellSignature (d l : ZMod 2) : Signature ℂ 2 := fun x => bellKernel d l (x 0) (x 1)

def firstCharacter (l : ZMod 2) : Character 2 where
  toFun x := l*x 0
  map_add' := by intros;simp [mul_add]
  map_smul' := by intros;simp;ring

@[simp] theorem firstCharacter_apply (l : ZMod 2) (x : BinaryVector 2) : firstCharacter l x=l*x 0 := rfl

theorem bellSignature_nonzeroFlat (d l : ZMod 2) : NonzeroFlat (bellSignature d l) := by
  refine ⟨1,![0,d],repetitionCode,firstCharacter l,repetitionCode_selfDual,?_⟩
  funext x
  have hc : ∀ d : ZMod 2,∀ a b : Bool,
      (boolEquiv a+boolEquiv b=d) ↔ (bit a-0=bit b-d) := by decide
  simp only [bellSignature,bellKernel,signature,value,parityKernel,mem_repetitionCode,
    Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_fin_one,Units.val_one,
    firstCharacter_apply,Pi.sub_apply,vectorWord,one_mul]
  simp only [hc]
  change sign (l*bit (x 0))*(if bit (x 0)-0=bit (x 1)-d then 1 else 0)=
    if bit (x 0)-0=bit (x 1)-d then sign (l*bit (x 0)) else 0
  split_ifs <;> simp

inductive SourcePrimitive : {n : ℕ} → Signature ℂ n → Prop
  | rm : SourcePrimitive rmCore
  | bell (c : ℂ) (d l : ZMod 2) : SourcePrimitive (c • bellSignature d l)

theorem SourcePrimitive.isCFlat {n : ℕ} {f : Signature ℂ n} (hf : SourcePrimitive f) : CFlat f := by
  cases hf with
  | rm => exact Or.inr (flat_is_nonzeroFlat _ rmCore_flat)
  | bell c d l => exact CharacterFlat.CFlat.smul _ (Or.inr (bellSignature_nonzeroFlat d l)) c

/-- Item 1 of the character-flat calculus on the manuscript's ordinary
boundary networks. The binary representatives may carry arbitrary scalars. -/
theorem source_character_network_forward {n : ℕ} (N : Network ℂ n)
    (hv : ∀ v,SourcePrimitive (N.vertex v))
    (he : ∀ e,N.edge e=Signature.disequality) : CFlat N.denote :=
  ordinary_network_CFlat N (fun v => (hv v).isCFlat) (fun _ => .disequality) he

end
end Holant.ReedMuller.CharacterFlat
