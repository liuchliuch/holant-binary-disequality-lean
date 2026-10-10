import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXWeightedAntiSigned
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineSupportTensorRecipe

/-! Actual disjoint-private tensor followed by the weighted-antidiagonal
paired sign guard. The exact scalar is retained. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiTensor
open Holant Holant.Tractable
namespace D
export OrdinaryNegativeMixedBlockData (Recipe EvenRecipe)
export OrdinaryNegativeMixedBlockSource (trace)
end D
namespace T
export OrdinaryNegativeAffineSupportTensorRecipe (recipe even_recipe trace_eq signs)
end T
namespace S
export NoXWeightedAntiSigned (recipe even_recipe trace_value anti)
end S
namespace E
export OrdinaryNegativeAffineSupportExtraction (combined shift)
end E
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {s m n k l : ℕ} {b : ℕ→ℕ}
variable (first : D.Recipe (u:=1) (s:=s) (a:=fun _=>m+k) (b:=b))
variable (second : D.Recipe (u:=1) (s:=s) (a:=fun _=>n+l) (b:=b))
variable (left : Fin m→Bool) (right : Fin n→Bool) (antiLabel : Fin s) (ha : b antiLabel.val=2)

def shiftedRecipe : D.Recipe (u:=1) (s:=s)
    (a:=fun _=>(m+n)+((m+n)+(k+l))) (b:=b) :=
  S.recipe (T.recipe first second) (T.signs left right) antiLabel ha

theorem shifted_even (hf : D.EvenRecipe first) (hg : D.EvenRecipe second) :
    D.EvenRecipe (shiftedRecipe first second left right antiLabel ha) :=
  S.even_recipe (T.recipe first second) (T.signs left right) antiLabel ha
    (T.even_recipe first second hf hg)

variable {K : Type} [Field K] (H : (i : Fin s)→Signature K (b i.val))
variable (v w : K)
variable (a_lit : (⟨b antiLabel.val,H antiLabel⟩ : AnySignature K)=⟨2,S.anti v w⟩)

include a_lit in
theorem shifted_trace (z : Fin (m+n)→Bool) :
    D.trace H ((m+n)+(k+l)) (shiftedRecipe first second left right antiLabel
      (congrArg Sigma.fst a_lit)) 0 z=
      (v*w)^(m+n)*E.combined (D.trace H k first 0)
        (D.trace H l second 0) left right z := by
  rw [shiftedRecipe,S.trace_value (T.recipe first second) (T.signs left right) antiLabel H v w a_lit,
    T.trace_eq]
  unfold E.combined E.shift OrdinaryNegativeNonproductBundleSupport.flip
  simp only [T.signs,Fin.addCases_left,Fin.addCases_right]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXWeightedAntiTensor
end
