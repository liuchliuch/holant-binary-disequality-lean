import Holant.Signature
import Mathlib.Algebra.Field.Defs
import Mathlib.Tactic.LinearCombination

/-! Literal I/X Walsh card pencils on original named ports. The zero-card
condition is derived by the two actual equations, retaining the factor2. -/
namespace Holant.ReedMuller.ZeroCardGraph
open Holant
variable {ι K : Type*} [DecidableEq ι] [Field K]

 abbrev Remaining (i j : ι) := {k : ι // k ≠ i ∧ k ≠ j}

 def sameLift (i j : ι) (b : Bool) (y : Remaining i j → Bool) : ι → Bool := fun k =>
  if hi : k=i then b else if hj : k=j then b else y ⟨k,hi,hj⟩

 @[simp] theorem sameLift_left (i j : ι) (b : Bool) (y : Remaining i j → Bool) : sameLift i j b y i=b := by
  simp [sameLift]
 @[simp] theorem sameLift_right (i j : ι) (b : Bool) (y : Remaining i j → Bool) : sameLift i j b y j=b := by
  by_cases h : j=i <;> simp [sameLift,h]
 @[simp] theorem sameLift_remaining (i j : ι) (b : Bool) (y : Remaining i j → Bool) (k : Remaining i j) :
    sameLift i j b y k.val=y k := by simp [sameLift,k.property.1,k.property.2]

 theorem sameLift_reconstruct (i j : ι) (x : ι → Bool) (hij : x i=x j) :
    sameLift i j (x i) (fun k => x k.val)=x := by
  funext k
  by_cases hi : k=i
  · subst k; simp
  · by_cases hj : k=j
    · subst k; simpa using hij
    · simp [sameLift,hi,hj]

 def card (f : Tensor K ι) (i j : ι) (minus : Bool) : Tensor K (Remaining i j) :=
  fun y => 2*(f (sameLift i j false y)+(if minus then -1 else 1)*f (sameLift i j true y))

 theorem zero_cards_iff_slices (htwo : (2:K) ≠ 0) (f : Tensor K ι) (i j : ι) :
    card f i j false=0 ∧ card f i j true=0 ↔
      ∀ y,f (sameLift i j false y)=0 ∧ f (sameLift i j true y)=0 := by
  constructor
  · rintro ⟨hp,hm⟩ y
    have hp' := congrFun hp y
    have hm' := congrFun hm y
    simp only [card,Bool.false_eq_true,ite_false,ite_true,one_mul,neg_one_mul,Pi.zero_apply] at hp' hm'
    have hp0 := (mul_eq_zero.mp hp').resolve_left htwo
    have hm0 := (mul_eq_zero.mp hm').resolve_left htwo
    have h0 : 2*f (sameLift i j false y)=0 := by linear_combination hp0+hm0
    have ha := (mul_eq_zero.mp h0).resolve_left htwo
    refine ⟨ha,?_⟩
    simpa only [ha,zero_add] using hp0
  · intro h
    constructor <;> funext y <;> simp [card,(h y).1,(h y).2]

 theorem zero_cards_iff_opposite (htwo : (2:K) ≠ 0) (f : Tensor K ι) (i j : ι) :
    card f i j false=0 ∧ card f i j true=0 ↔
      ∀ x : ι → Bool,f x ≠ 0 → x i ≠ x j := by
  rw [zero_cards_iff_slices htwo]
  constructor
  · intro h x hx he
    have hh := h (fun k : Remaining i j => x k.val)
    have hzero : f (sameLift i j (x i) (fun k : Remaining i j => x k.val))=0 := by
      cases hb : x i
      · exact hh.1
      · exact hh.2
    rw [sameLift_reconstruct i j x he] at hzero
    exact hx hzero
  · intro h y
    constructor
    · by_contra hn
      have hh := h (sameLift i j false y) hn
      simp at hh
    · by_contra hn
      have hh := h (sameLift i j true y) hn
      simp at hh

end Holant.ReedMuller.ZeroCardGraph
