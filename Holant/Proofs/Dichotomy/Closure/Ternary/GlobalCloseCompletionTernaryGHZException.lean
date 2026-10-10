import Holant.Proofs.Dichotomy.Closure.Ternary.GlobalCloseCompletionTernaryGHZCore

/-! If all three GHZ triangle cores vanish, the original tensor is already
symmetric. This uses only exact two-dimensional orthogonality, retaining the
original coefficients and requiring no free local matrix gadgets. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZException
open Holant
open scoped BigOperators
namespace T
export GlobalCloseCompletionTernaryGHZCore (ghz cyclic)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 300000
set_option Elab.async false
variable {K : Type} [Field K]

theorem orthogonal_cross (u v w : Bool→K) (nz : ∃t,w t≠0)
    (uw : u false*w false+u true*w true=0)
    (vw : v false*w false+v true*w true=0) :
    u false*v true-u true*v false=0 := by
  obtain ⟨t,ht⟩:=nz
  cases t
  · have he : (u false*v true-u true*v false)*w false=0 := by
      linear_combination (v true)*uw-(u true)*vw
    exact (mul_eq_zero.mp he).resolve_right ht
  · have he : (u false*v true-u true*v false)*w true=0 := by
      linear_combination (u false)*vw-(v false)*uw
    exact (mul_eq_zero.mp he).resolve_right ht

theorem column_nonzero (A : Matrix Bool Bool K) (det : A.det≠0) (t : Bool) : ∃u,A u t≠0 := by
  by_contra bad
  push_neg at bad
  apply det
  exact Matrix.det_eq_zero_of_column_eq_zero t bad

theorem column_swap (A B C : Matrix Bool Bool K) (det : C.det≠0)
    (ca : ∀t,(C.transpose*A) t t=0) (cb : ∀t,(C.transpose*B) t t=0)
    (t i j : Bool) : A i t*B j t=A j t*B i t := by
  have h:=orthogonal_cross (fun u=>A u t) (fun u=>B u t) (fun u=>C u t)
    (column_nonzero C det t)
    (by simpa [Matrix.mul_apply,Fintype.sum_bool,mul_comm,add_comm] using ca t)
    (by simpa [Matrix.mul_apply,Fintype.sum_bool,mul_comm,add_comm] using cb t)
  cases i <;> cases j <;> first | rfl | exact sub_eq_zero.mp h | exact (sub_eq_zero.mp h).symm

variable (A B C : Matrix Bool Bool K) (ha : A.det≠0) (hb : B.det≠0) (hc : C.det≠0)
variable (ab : ∀t,(A.transpose*B) t t=0)
variable (bc : ∀t,(B.transpose*C) t t=0)
variable (ca : ∀t,(C.transpose*A) t t=0)

theorem transpose_diagonal (U V : Matrix Bool Bool K) (t : Bool) :
    (U.transpose*V) t t=(V.transpose*U) t t := by
  simp only [Matrix.mul_apply,Matrix.transpose_apply,Fintype.sum_bool]
  ring

include hb hc ab bc ca in
theorem swap01 (x : Fin 3→Bool) : T.ghz A B C ![x 1,x 0,x 2]=T.ghz A B C x := by
  unfold T.ghz
  apply Finset.sum_congr rfl
  intro t _
  simp only [Matrix.cons_val_zero,Matrix.cons_val_one,Matrix.cons_val_two]
  have h:=column_swap A B C hc ca (fun t=>(transpose_diagonal C B t).trans (bc t)) t (x 1) (x 0)
  simpa using congrArg (fun z=>z*C (x 2) t) h

include ha hb ab bc ca in
theorem swap12 (x : Fin 3→Bool) : T.ghz A B C ![x 0,x 2,x 1]=T.ghz A B C x := by
  unfold T.ghz
  apply Finset.sum_congr rfl
  intro t _
  have h:=column_swap B C A ha ab (fun t=>(transpose_diagonal A C t).trans (ca t)) t (x 2) (x 1)
  simpa [mul_assoc] using congrArg (fun z=>A (x 0) t*z) h


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionTernaryGHZException
end
