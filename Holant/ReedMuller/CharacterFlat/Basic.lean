import Holant.ReedMuller.FlatNetwork.Source

/-! Literal linear sign characters on affine self-dual supports. Integer
character identities are kernel-computed and then embedded faithfully in C. -/
namespace Holant.ReedMuller.CharacterFlat
open Holant Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open scoped BigOperators
set_option backward.isDefEq.respectTransparency false
variable {n : ℕ}

def intSign (x : ZMod 2) : ℤ := if x=0 then 1 else -1

theorem intSign_add : ∀ x y : ZMod 2,intSign (x+y)=intSign x*intSign y := by decide
theorem intSign_square : ∀ x : ZMod 2,intSign x*intSign x=1 := by decide
theorem intSign_sum : ∀ x y : ZMod 2,
    (∑ b : ZMod 2,intSign (x+b*y))=if y=0 then 2*intSign x else 0 := by decide

def sign (x : ZMod 2) : ℂ := (intSign x : ℂ)

@[simp] theorem sign_zero : sign 0=1 := by norm_num [sign,intSign]
@[simp] theorem sign_one : sign 1 = -1 := by norm_num [sign,intSign]
theorem sign_add (x y : ZMod 2) : sign (x+y)=sign x*sign y := by
  simp only [sign,intSign_add,Int.cast_mul]
@[simp] theorem sign_square (x : ZMod 2) : sign x*sign x=1 := by
  change (intSign x : ℂ)*(intSign x : ℂ)=1
  rw [←Int.cast_mul,intSign_square,Int.cast_one]
theorem sign_nonzero (x : ZMod 2) : sign x≠0 := by
  intro h
  have H := sign_square x
  rw [h,zero_mul] at H
  exact zero_ne_one H

theorem sign_sum (x y : ZMod 2) :
    (∑ b : ZMod 2,sign (x+b*y))=if y=0 then 2*sign x else 0 := by
  simp only [sign,←Int.cast_sum,intSign_sum]
  split_ifs <;> simp

noncomputable section
attribute [local instance] Classical.propDecidable

abbrev Character (n : ℕ) := BinaryVector n →ₗ[ZMod 2] ZMod 2

def value (c : ℂ) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n) : BinaryVector n → ℂ :=
  fun x => if x-a∈D then c*sign (ell x) else 0

def signature (c : ℂ) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n) : Signature ℂ n :=
  fun x => value c a D ell (vectorWord x)

def NonzeroFlat (f : Signature ℂ n) : Prop :=
  ∃ (c : ℂˣ) (a : BinaryVector n) (D : BinaryCode n) (ell : Character n),
    SelfDual D ∧ f=signature c a D ell

def CFlat (f : Signature ℂ n) : Prop := f=0 ∨ NonzeroFlat f

theorem value_nonzero_iff (c : ℂ) (hc : c≠0) (a : BinaryVector n) (D : BinaryCode n)
    (ell : Character n) (x : BinaryVector n) : value c a D ell x≠0 ↔ x-a∈D := by
  unfold value
  split_ifs with h
  · simp [h,mul_ne_zero hc (sign_nonzero _)]
  · simp [h]

theorem nonzeroFlat_nonzero (f : Signature ℂ n) (hf : NonzeroFlat f) : f≠0 := by
  obtain ⟨c,a,D,ell,hD,rfl⟩ := hf
  intro hz
  have H := congrFun hz (wordVector a)
  have hn := (value_nonzero_iff c c.ne_zero a D ell a).mpr (by simp)
  apply hn
  simpa only [signature,vector_word,Pi.zero_apply] using H

theorem flat_is_nonzeroFlat (f : Signature ℂ n) (hf : Flat f) : NonzeroFlat f := by
  obtain ⟨c,a,D,hD,rfl⟩ := hf
  refine ⟨c,a,D,0,hD,?_⟩
  funext x
  simp only [signature,value,LinearMap.zero_apply,sign_zero,mul_one,flatSignature]
  rfl

theorem flatOrZero_is_CFlat (f : Signature ℂ n) (hf : FlatOrZero f) : CFlat f := by
  rcases hf with hz | hf
  · exact Or.inl hz
  · exact Or.inr (flat_is_nonzeroFlat f hf)

end
end Holant.ReedMuller.CharacterFlat
