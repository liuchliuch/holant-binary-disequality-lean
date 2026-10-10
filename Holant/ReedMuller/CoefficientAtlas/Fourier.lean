import Holant.ReedMuller.CoefficientAtlas.FourierSum
import Holant.BoundaryAction

namespace Holant.ReedMuller.CoefficientAtlas
open Holant.ReedMuller.LowArity
open scoped BigOperators
noncomputable section
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 100000
set_option maxHeartbeats 30000000

theorem supported_sum (q : Signature ℂ 8) (hq : SupportRM q) (F : (Point → Bool) → ℂ) :
    (∑ x, F x*q x)=∑ a : Param, F (word a)*q (word a) := by
  classical
  have hi : (∑ x ∈ Finset.univ.image word, F x*q x)=
      ∑ a : Param, F (word a)*q (word a) := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact word_injective hab
  rw [←hi]
  symm
  apply Finset.sum_subset (Finset.subset_univ _)
  intro x _ hx
  have hz : q x=0 := by
    apply outside_zero hq
    intro a ha
    apply hx
    exact Finset.mem_image.mpr ⟨a,Finset.mem_univ _,ha.symm⟩
  simp [hz]

theorem dot_add_left (x y z : BinaryVector 8) : dot (x+y) z=dot x z+dot y z := by
  simp [dot,add_mul,Finset.sum_add_distrib]

/-- Exact Walsh inversion of the sign-character table. The physical output
scalar is 16*c, and the original shift vector stays explicit. -/
theorem character_fourier (q : Signature ℂ 8) (hq : SupportRM q) (c : ℂˣ) (v : BinaryVector 8)
    (hchar : ∀ x, q x=if ∃ a : Param, word a=x then
      (c:ℂ)*(sign (G := ℂˣ) (-1) (dot v (vector x)):ℂ) else 0) :
    Signature.coordinateAction (fun _ => walshKernel) q =
      fun x => if ∃ a : Param, evaluate a=vector x+v then 16*(c:ℂ) else 0 := by
  classical
  funext x
  rw [Signature.coordinateAction,supported_sum q hq]
  have ht (a : Param) :
      (∏ p,walshKernel (x p) (word a p))*q (word a)=
        (c:ℂ)*(sign (G := ℂˣ) (-1) (dot (vector x+v) (evaluate a)):ℂ) := by
    rw [hchar]
    simp only [show (∃ a' : Param,word a'=word a) from ⟨a,rfl⟩,ite_true,vector_word,
      prod_walshKernel,vector_word,dot_add_left,sign_add (G := ℂˣ) (-1) (by simp),Units.val_mul]
    ring
  simp_rw [ht]
  rw [←Finset.mul_sum,complex_fourier_sum]
  split_ifs <;> ring

end
end Holant.ReedMuller.CoefficientAtlas
