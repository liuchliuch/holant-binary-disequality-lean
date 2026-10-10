import Holant.Proofs.Hardness.EOBinaryPlaneConjugateNetwork
import Holant.Proofs.Hardness.EOBinaryPlanePowerQueries

/-! Mixed-label conjugation is a polynomial-size linear combination of the
existing physical variable-chain queries. Original answers remain in K and
are embedded into the named common field L only for the final arithmetic. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePhysicalConjugate
open Holant Holant.Complexity
open scoped BigOperators
namespace N
export EOBinaryPlaneConjugateNetwork (value network_moments)
end N
namespace P
export EOBinaryPlanePowerQueries (query_value queryComputes)
end P
namespace Q
export ExactTwoChainQueries (Input TargetInput value computes)
end Q
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace I
export EOBinaryPlaneConjugate (polynomial degree_bound)
end I
set_option backward.isDefEq.respectTransparency false

variable {K : Type} {L : Type*} [Field K] [Field L] [StarRing L]

theorem physical_queries (into : K→+*L) (f : Signature K 2) (r : Q.Input) :
    N.value (fun z=>into (f z)) (fun z=>star (into (f z))) r=
      ∑k ∈ Finset.range (I.polynomial into (EOBinaryPlaneConjugateQueries.coefficients f)
        r.val.vertices.length).natDegree,
        (I.polynomial into (EOBinaryPlaneConjugateQueries.coefficients f) r.val.vertices.length).coeff (k+1)*
          into (V.value (EOBinaryPlaneCore.lift f) (Q.value (k,r))) := by
  rw [N.network_moments]
  apply Finset.sum_congr rfl
  intro k _
  rw [P.query_value]
  rfl

theorem positive_power_and_budget (into : K→+*L) (f : Signature K 2) (r : Q.Input) (k : ℕ)
    (hk : k∈Finset.range (I.polynomial into (EOBinaryPlaneConjugateQueries.coefficients f)
      r.val.vertices.length).natDegree) :
    0<k+1 ∧ k+1≤(r.val.vertices.length+1)^4 := by
  have hd := I.degree_bound into (EOBinaryPlaneConjugateQueries.coefficients f) r.val.vertices.length
  have hk := Finset.mem_range.mp hk
  omega

/-- The emitted queries use the actual variable-unary-length physical machine. -/
abbrev queryComputes := Q.computes

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlanePhysicalConjugate
