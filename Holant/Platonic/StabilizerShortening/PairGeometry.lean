import Holant.Platonic.StabilizerShortening.TensorExtension
import Holant.ReedMuller.AffinePatching.BooleanLinear

/-! Literal port bijections and affine sampling through untouched ports. -/
namespace Holant.Platonic.StabilizerShortening
open Holant Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open Holant.ReedMuller.LowArity Holant.ReedMuller.FlatNetwork
open Holant.ReedMuller.AffinePatching
open Holant.Platonic.StabilizerErasure
noncomputable section
set_option backward.isDefEq.respectTransparency false
attribute [local instance] Classical.propDecidable
variable {k m n : ℕ}

def boolSumOption : (Bool ⊕ Fin n) ≃ Option (Option (Fin n)) where
  toFun := Sum.elim (fun b=>if b then some none else none) (fun j=>some (some j))
  invFun := fun x=>match x with
    | none => .inl false
    | some none => .inl true
    | some (some j) => .inr j
  left_inv x := by cases x with | inl b => cases b <;> rfl | inr j => rfl
  right_inv x := by cases x with | none => rfl | some x => cases x <;> rfl

def twoPorts (r : Fin (n+2)) (s : Fin (n+1)) : (Bool ⊕ Fin n) ≃ Fin (n+2) :=
  (boolSumOption.trans (Equiv.optionCongr (finSuccEquiv' s).symm)).trans
    (finSuccEquiv' r).symm

@[simp] theorem twoPorts_first (r : Fin (n+2)) (s : Fin (n+1)) :
    twoPorts r s (.inl false)=r := rfl
@[simp] theorem twoPorts_second (r : Fin (n+2)) (s : Fin (n+1)) :
    twoPorts r s (.inl true)=r.succAbove s := rfl
@[simp] theorem twoPorts_remaining (r : Fin (n+2)) (s : Fin (n+1)) (j : Fin n) :
    twoPorts r s (.inr j)=r.succAbove (s.succAbove j) := rfl

theorem exists_twoPorts (r s : Fin (n+2)) (h : r≠s) :
    ∃p : (Bool ⊕ Fin n) ≃ Fin (n+2),p (.inl false)=r ∧ p (.inl true)=s := by
  let s' := (finSuccAboveEquiv r).symm ⟨s,Ne.symm h⟩
  refine ⟨twoPorts r s',rfl,?_⟩
  exact congrArg Subtype.val ((finSuccAboveEquiv r).apply_symm_apply ⟨s,Ne.symm h⟩)

def tailWord : (t : ℕ) → Word (k+t) → Word k
  | 0,x => x
  | t+1,x => tailWord t (Fin.tail x)

def extendWordMap (t : ℕ) (p : Word k → Word n) : Word (k+t) → Word (n+t) :=
  match t with
  | 0 => p
  | t+1 => fun x=>Fin.cons (x 0) (extendWordMap t p (Fin.tail x))

theorem tailWord_affine (t : ℕ) : IsAffineMap (tailWord (k:=k) t) := by
  intro x y
  induction t with
  | zero => ext i;simp [tailWord,Holant.Tractable.AffinePhase.xor,origin]
  | succ t ih => exact ih (Fin.tail x) (Fin.tail y)

theorem extendWordMap_affine (t : ℕ) (p : Word k → Word n) (hp : IsAffineMap p) :
    IsAffineMap (extendWordMap t p) := by
  induction t with
  | zero => exact hp
  | succ t ih =>
    intro x y
    ext j
    cases j using Fin.cases with
    | zero => simp [extendWordMap,Holant.Tractable.AffinePhase.xor,origin]
    | succ j => exact congrFun (ih (Fin.tail x) (Fin.tail y)) j

theorem tensorMap_sampling (t : ℕ) (U : Signature ℂ k →ₗ[ℂ] Signature ℂ n)
    (p : Word k → Word n) (a : Word k → ℂ)
    (he : ∀f x,U f (p x)=a x*f x) (f : Signature ℂ (k+t)) (x : Word (k+t)) :
    tensorMap t U f (extendWordMap t p x)=a (tailWord t x)*f x := by
  induction t with
  | zero => exact he f x
  | succ t ih =>
    change tensorMap t U (column 0 (x 0) f) (extendWordMap t p (Fin.tail x))=_
    rw [ih,column_zero_apply,Fin.cons_self_tail]
    rfl

end
end Holant.Platonic.StabilizerShortening
