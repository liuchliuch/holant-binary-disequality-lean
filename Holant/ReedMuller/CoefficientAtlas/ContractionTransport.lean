import Holant.BoundaryAction
import Holant.TwoPorts
import Mathlib.Tactic.Ring

/-! General ordered contraction transport, for the actual bilinear kernel and
arbitrary remaining arity. No physical basis gadget is inferred. -/
namespace Holant.ReedMuller.CoefficientAtlas
open scoped BigOperators
set_option maxHeartbeats 5000000
set_option maxRecDepth 100000
variable {K : Type*} [CommSemiring K]

def headTailEquiv (n : ℕ) : (Fin (n+1) → Bool) ≃ Bool × (Fin n → Bool) where
  toFun := fun x => (x 0,Fin.tail x)
  invFun := fun p => Fin.cons p.1 p.2
  left_inv := by
    intro x
    funext i
    refine Fin.cases rfl (fun j => ?_) i
    rfl
  right_inv := by intro p; cases p; rfl

theorem sum_words_succ {n : ℕ} (f : (Fin (n+1) → Bool) → K) :
    (∑ x, f x)=∑ a : Bool, ∑ y : Fin n → Bool, f (Fin.cons a y) := by
  rw [←(headTailEquiv n).symm.sum_comp f,Fintype.sum_prod_type]
  rfl

theorem coordinateAction_head {n : ℕ} (M : Kernel K) (f : Signature K (n+1))
    (a : Bool) (x : Fin n → Bool) :
    Signature.coordinateAction (fun _ => M) f (Fin.cons a x)=
      ∑ b : Bool, M a b * Signature.coordinateAction (fun _ => M) (Signature.pin f b) x := by
  simp [Signature.coordinateAction,sum_words_succ,Fin.prod_univ_succ,Signature.pin,
    Finset.mul_sum,mul_assoc]

theorem coordinateAction_contract {n : ℕ} (M E : Kernel K) (f : Signature K (n+2)) :
    Signature.contract E (Signature.coordinateAction (fun _ => M) f)=
      Signature.coordinateAction (fun _ => M) (Signature.contract (Kernel.pullback E M) f) := by
  funext x
  simp only [Signature.contract,coordinateAction_head]
  dsimp only [Signature.coordinateAction,Signature.pin,Signature.contract,Kernel.pullback,Kernel.mul,Kernel.transpose]
  simp only [Fintype.sum_bool,mul_add,add_mul,Finset.mul_sum,Finset.sum_mul,Finset.sum_add_distrib]
  simp only [←Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro y _
  ring


def assignmentEquiv {n : ℕ} (e : Equiv.Perm (Fin n)) : (Fin n → Bool) ≃ (Fin n → Bool) where
  toFun := fun x i => x (e i)
  invFun := fun x i => x (e.symm i)
  left_inv := by intro x; funext i; simp
  right_inv := by intro x; funext i; simp

theorem coordinateAction_reindex {n : ℕ} (M : Kernel K) (e : Equiv.Perm (Fin n))
    (f : Signature K n) :
    Signature.coordinateAction (fun _ => M) (Tensor.reindex e f)=
      Tensor.reindex e (Signature.coordinateAction (fun _ => M) f) := by
  funext x
  simp only [Signature.coordinateAction,Tensor.reindex]
  rw [←(assignmentEquiv e).sum_comp (fun y => (∏ j, M (x (e j)) (y j))*f y)]
  apply Finset.sum_congr rfl
  intro y _
  congr 1
  exact (Equiv.prod_comp e (fun j => M (x j) (y j))).symm

end Holant.ReedMuller.CoefficientAtlas
