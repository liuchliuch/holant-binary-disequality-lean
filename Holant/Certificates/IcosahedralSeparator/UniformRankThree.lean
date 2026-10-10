import Holant.Certificates.MatchingProductBridge.Flattenings
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-! A literal complex rank-three certificate: zero four-by-four determinant
and one specified nonzero three-by-three minor. -/
namespace Holant.Certificates.IcosahedralSeparator
open Holant.Certificates.MatchingProductBridge
noncomputable section

 theorem rank_three_of_minor (M : PairMatrix) (r c : Fin 3→Bool×Bool)
    (hd : Matrix.det M=0) (hm : Matrix.det (M.submatrix r c)≠0) : M.rank=3 := by
  have hl:=(Matrix.rank_submatrix_le M r c)
  rw [Matrix.rank_of_det_ne_zero hm] at hl
  norm_num at hl
  obtain ⟨v,hv,hz⟩:=(Matrix.exists_mulVec_eq_zero_iff).mpr hd
  have hk : v∈LinearMap.ker M.mulVecLin := hz
  letI : Nontrivial (LinearMap.ker M.mulVecLin) :=
    ⟨⟨⟨v,hk⟩,0,fun h=>hv (congrArg Subtype.val h)⟩⟩
  have hp : 0<Module.finrank ℂ (LinearMap.ker M.mulVecLin) :=
    Module.finrank_pos_iff.mpr inferInstance
  have hr:=M.mulVecLin.finrank_range_add_finrank_ker
  change M.rank+Module.finrank ℂ (LinearMap.ker M.mulVecLin)=_ at hr
  norm_num at hr
  omega

end
end Holant.Certificates.IcosahedralSeparator
