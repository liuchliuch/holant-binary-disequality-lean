import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2Q4UnionCurrent
import Holant.Proofs.Dichotomy.Closure.C2.GlobalCloseCompletionC2KNormal

/-! Fixed source-K image of all eight complementary coefficient pairs,
including mixed parity. All sixteen sums and the exact sqrt-two factor remain. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4KTensor
open Holant Holant.Tractable
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace C
export GlobalCloseCompletionC2Q4UnionCurrent (tensor)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 3000000
set_option maxRecDepth 32768
set_option Elab.async false

def entries (v : Fin 8→AlgebraicComplex) : Entries AlgebraicComplex := ⟨(v 0+v 1+v 2+v 3+v 4+v 5+v 6+v 7)/2,(-v 0-v 1-v 2-v 3+v 4+v 5+v 6+v 7)/2,(-v 0-v 1+v 2+v 3-v 4-v 5+v 6+v 7)/2,(-v 0-v 1+v 2+v 3+v 4+v 5-v 6-v 7)/2,(-v 0+v 1-v 2+v 3-v 4+v 5-v 6+v 7)/2,(-v 0+v 1-v 2+v 3+v 4-v 5+v 6-v 7)/2,(-v 0+v 1+v 2-v 3-v 4+v 5+v 6-v 7)/2,(v 0-v 1-v 2+v 3-v 4+v 5+v 6-v 7)/2⟩

private theorem inverse_four : sqrtTwo⁻¹ ^ 4 = (1/4 : AlgebraicComplex) := by
  calc
    _ = (sqrtTwo^4)⁻¹ := by simp only [inv_pow]
    _ = (4 : AlgebraicComplex)⁻¹ := by
      congr 1
      calc
        sqrtTwo^4=(sqrtTwo^2)^2 := by ring
        _=4 := by rw [sqrtTwo_sq]; norm_num
    _ = _ := by simp [one_div]

theorem sourceK_tensor (v : Fin 8→AlgebraicComplex) : sourceKBasis.action (C.tensor v)=table (entries v) := by
  funext x
  cases h0 : x 0 <;> cases h1 : x 1 <;> cases h2 : x 2 <;> cases h3 : x 3
  all_goals simp [sourceKBasis,KMatrix,InvertibleKernel.action,Signature.coordinateAction,
    Holant.Projective.CyclicQuaternary.Physical.sum_words4,Fin.prod_univ_succ,C.tensor,entries,table,h0,h1,h2,h3]
  all_goals ring_nf
  all_goals norm_num [imaginaryUnit_sq,imaginaryUnit_pow_four,inv_pow,sqrtTwo_sq,inverse_four]
  all_goals ring_nf
  all_goals simp only [inverse_four]
  all_goals ring

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionC2Q4KTensor
end
