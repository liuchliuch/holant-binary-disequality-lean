import Holant.Tractable.SymmetricBinaryPullback.Product
import Holant.Complexity.BinaryInterpolation.BinaryFactors

/-! Full binary Product membership is exactly its cross-product identity,
proved from literal unary factors and the original Product factor list. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
open Holant Holant.Tractable
namespace B
export Holant.Tractable.SymmetricBinaryPullback (table ProductShape product_shape)
end B
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

def Full (f : Signature AlgebraicComplex 2) : Prop := ∀x,f x≠0

def Cross (f : Signature AlgebraicComplex 2) : Prop :=
  f ![false,false]*f ![true,true]=f ![false,true]*f ![true,false]


theorem kernel_table (f : Signature AlgebraicComplex 2) : kernelSignature (B.table f)=f := by
  funext x
  change f ![x 0,x 1]=f x
  congr 1
  funext i
  fin_cases i <;> rfl

theorem full_product_iff (f : Signature AlgebraicComplex 2) (hf : Full f) : Product f ↔ Cross f := by
  constructor
  · intro h
    have hh := B.product_shape (E:=B.table f) (by simpa only [kernel_table] using h)
    rcases hh with hh|hh|hh
    · exact False.elim (hf ![false,true] hh.1)
    · exact False.elim (hf ![false,false] hh.1)
    · exact hh
  · intro h
    have nz : B.table f≠0:=by
      intro hz
      exact hf ![false,false] (congrFun₂ hz false false)
    have det : Matrix.det (B.table f)=0:=by
      rw [Holant.Complexity.BinaryInterpolation.det_entries]
      exact sub_eq_zero.mpr h
    obtain ⟨u,v,_,_,huv⟩:=Holant.Complexity.BinaryInterpolation.singular_binary_factors (B.table f) nz det
    have form : f=fun z=>u (z 0)*v (z 1) := by
      rw [←kernel_table f]
      funext z
      change B.table f (z 0) (z 1)=_
      rw [huv]
      rfl
    rw [form]
    exact (product_unary (0 : Fin 2) u).mul (product_unary (1 : Fin 2) v)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
end
