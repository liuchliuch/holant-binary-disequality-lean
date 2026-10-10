import Holant.Certificates.OctahedralSeparator.RankCertificates
import Holant.Certificates.OctahedralSeparator.TensorSemantics
import Holant.Certificates.TetrahedralOrientation.RankCertificate

namespace Holant.Certificates.OctahedralSeparator
open Holant Holant.Certificates.MatchingProductBridge
noncomputable section
set_option maxHeartbeats 1000000

theorem scalarFlatten_embed (k : Fin 3) (t : Signature Scalar 4) :
    (fun a b => embed (scalarFlatten k t a b))=flatten k (complexTensor t) := by
  fin_cases k <;> rfl

theorem rank_of_certificate (M : Matrix PairIndex PairIndex Scalar) (r c : Bool → PairIndex)
    (h : RankCertificate M r c) : Matrix.rank ((fun a b => embed (M a b)) : Matrix PairIndex PairIndex ℂ)=2 := by
  let N : Matrix PairIndex PairIndex ℂ := fun a b => embed (M a b)
  have hminor : TetrahedralOrientation.pivotMinor N r c=embed (scalarMinor M r c) := by
    simp [TetrahedralOrientation.pivotMinor,scalarMinor,N,embed_mul]
  have hn : TetrahedralOrientation.pivotMinor N r c ≠ 0 := by
    rw [hminor]
    exact embed_ne_zero h.1
  apply TetrahedralOrientation.rank_two_of_certificate N r c hn
  ext a b
  have hpoly := congrArg embed (h.2 a b)
  simp only [embed_mul,embed_add,embed_sub] at hpoly
  change embed (scalarMinor M r c)*N a b=
    (N a (c false)*N (r true) (c true)-N a (c true)*N (r true) (c false))*N (r false) b+
    (N (r false) (c false)*N a (c true)-N (r false) (c true)*N a (c false))*N (r true) b at hpoly
  rw [← hminor] at hpoly
  simp only [Matrix.mul_apply,Fintype.sum_bool,TetrahedralOrientation.rankLeft,
    TetrahedralOrientation.rankRight,Bool.false_eq_true,ite_true,ite_false]
  field_simp [hn]
  linear_combination hpoly

theorem base_rank_two (r : Fin 9) (k : Fin 3) :
    (flatten k (complexTensor (regularCard r))).rank=2 := by
  have h := rank_of_certificate _ _ _ (rankCertificates r k)
  rw [scalarFlatten_embed,base_exact] at h
  simpa only [baseCard,Fin.addCases_left] using h

end
end Holant.Certificates.OctahedralSeparator
