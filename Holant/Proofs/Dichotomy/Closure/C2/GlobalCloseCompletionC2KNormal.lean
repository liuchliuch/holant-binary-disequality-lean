import Holant.Proofs.Dichotomy.Closure.Klein.GlobalCloseCompletionKleinHadamardAlgebra
import Holant.Tractable.KPresentation

/-! Exact source-K coordinates of the original complementary-even C2 table.
The normalization uses the fixed manuscript K, including its square-root
factor; no independently chosen basis or uncharged physical gate appears. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2KNormal
open Holant Holant.Tractable
namespace T
export GlobalCloseCompletionKleinTwistedAlgebra (normal)
end T
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option maxRecDepth 32768
set_option Elab.async false

private theorem inverse_four : sqrtTwo⁻¹ ^ 4 = (1/4 : AlgebraicComplex) := by
  calc
    _ = (sqrtTwo^4)⁻¹ := by simp only [inv_pow]
    _ = (4 : AlgebraicComplex)⁻¹ := by
      congr 1
      calc
        sqrtTwo^4=(sqrtTwo^2)^2 := by ring
        _=4 := by rw [sqrtTwo_sq]; norm_num
    _ = _ := by simp [one_div]

theorem sourceK_normal (a b c d : AlgebraicComplex) :
    sourceKBasis.action (T.normal a b c d)=
      T.normal ((a+b+c+d)/2) ((-a-b+c+d)/2) ((-a+b-c+d)/2) ((-a+b+c-d)/2) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [sourceKBasis,KMatrix,InvertibleKernel.action,Signature.coordinateAction,
    Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,
    T.normal,Holant.LocalDrafts.Hardness.EightVertexNonexception.table,h0,h1,h2,h3]
  all_goals ring_nf
  all_goals norm_num [imaginaryUnit_sq,imaginaryUnit_pow_four,inv_pow,sqrtTwo_sq,inverse_four]
  all_goals ring_nf
  all_goals simp only [inverse_four]
  all_goals ring

/-- The fixed inverse source-K coefficients, obtained from the checked forward
formula and its genuine inverse identity. -/
theorem sourceK_inverse_normal (a b c d : AlgebraicComplex) :
    sourceKBasis.symm.action (T.normal a b c d)=
      T.normal ((a-b-c-d)/2) ((a-b+c+d)/2) ((a+b-c+d)/2) ((a+b+c-d)/2) := by
  have h := sourceK_normal ((a-b-c-d)/2) ((a-b+c+d)/2) ((a+b-c+d)/2) ((a+b+c-d)/2)
  have rhs : T.normal
      ((((a-b-c-d)/2)+((a-b+c+d)/2)+((a+b-c+d)/2)+((a+b+c-d)/2))/2)
      ((-((a-b-c-d)/2)-((a-b+c+d)/2)+((a+b-c+d)/2)+((a+b+c-d)/2))/2)
      ((-((a-b-c-d)/2)+((a-b+c+d)/2)-((a+b-c+d)/2)+((a+b+c-d)/2))/2)
      ((-((a-b-c-d)/2)+((a-b+c+d)/2)+((a+b-c+d)/2)-((a+b+c-d)/2))/2)=T.normal a b c d := by
    congr 1 <;> ring
  rw [rhs] at h
  have hi := congrArg sourceKBasis.symm.action h
  rw [InvertibleKernel.symm_action_action] at hi
  exact hi.symm

theorem inverse_opposite (a c : AlgebraicComplex) :
    sourceKBasis.symm.action (T.normal a a c (-c))=T.normal 0 0 (a-c) (a+c) := by
  rw [sourceK_inverse_normal]
  congr 1 <;> ring


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2KNormal
end
