import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationBlockSource
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4ClassificationPaired
import Holant.Proofs.Dichotomy.Closure.Complement.GlobalCloseCompletionComplementQ4RankThreeHard

/-! Exhaustively consume both concrete circuit branches. The remaining
positive resources are actual pure Eq4 or an actual complete diagonal product,
never a singleton tractability claim about the selected row. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationResources
open Holant Holant.Algebraic Holant.Complexity
namespace S
export GlobalCloseCompletionComplementQ4Series (row)
end S
namespace T
export GlobalCloseCompletionComplementQ4Templates (connect connect_network)
end T
namespace B
export GlobalCloseCompletionComplementQ4ClassificationBlocks (swap swap_value)
end B
namespace R
export GlobalCloseCompletionComplementQ4ClassificationReduction (RedundantOutput swap_bc)
end R
namespace C
export GlobalCloseCompletionComplementQ4ClassificationBlockSource (Outcome nonzero_left classified)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 500000
set_option Elab.async false
variable {K : Type} [Field K] [Algebra ℚ K] [CharZero K]
variable {size degree : ℕ} {arity : ℕ→ℕ}
variable (H : (i : Fin size)→Signature K (arity i.val)) (F : FixedField K degree)
variable (phi : K→+*ℂ)

include phi in
theorem imaginary (N : NativeAntiTargetSource.Output H 4) (a r s t : K)
    (form : N.network.denote=a • S.row 1 r t (s*r*t))
    (ha : a≠0) (hr : r^2= -1) (hs : s^2=1) : C.Outcome H F := by
  have rn : r≠0 := by intro h;norm_num [h] at hr
  let Q:=B.swap H (T.connect H N N)
  have value : Q.network.denote=S.row (2*a^2*r) (2*a^2*s*r*t^2) 0 0 := by
    dsimp only [Q]
    rw [B.swap_value,T.connect_network,
      GlobalCloseCompletionComplementQ4ClassificationPaired.imaginary_square N.network a r s t form hr hs,R.swap_bc]
  exact C.nonzero_left H F phi Q _ _ value
    (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero _ ha)) rn)

include phi in
theorem redundant (N : NativeAntiTargetSource.Output H 4) (a b c d : K)
    (form : N.network.denote=S.row a b c d) (ha : a≠0) (O : R.RedundantOutput H) : C.Outcome H F := by
  classical
  by_cases live : O.c=0
  · have nonzero : O.a≠0 ∨ O.b≠0 := by
      by_cases h : O.a=0
      · right
        intro z
        apply O.determinant
        simp [h,z]
      · exact Or.inl h
    exact C.classified H F phi O.graph N O.a O.b a b c d
      (by simpa only [live] using O.value) nonzero form ha
  · exact Or.inr (Or.inr (GlobalCloseCompletionComplementQ4RankThreeHard.controlledHard H F O live))


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionComplementQ4ClassificationResources
end
