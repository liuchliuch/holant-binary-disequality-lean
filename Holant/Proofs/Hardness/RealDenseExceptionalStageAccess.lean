import Holant.Proofs.Hardness.RealDensePortStageAccess
import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess
import Holant.Proofs.Platonic.PhysicalCostComposition

/-! Composition of the literal port normalization and two-M cap attachment.
The original dictionary and field are retained. Reindexing adds no vertices or
edges, so total query counts remain exactly 2V and E+2V. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseExceptionalStageAccess
open Computability Holant Holant.Algebraic Holant.Complexity
open BinaryCompose FixedFieldMachines FixedGadgetSubstitution
namespace P
export RealDensePortNormalize (normalized)
end P
namespace A
export RealDensePortStageAccess (source query query_value query_counts value)
end A
namespace T
export RealDenseSignTwistStageAccess (Applicable value source query query_value query_counts)
end T
namespace Q
export ExactTwoChainQueries (TargetInput targetEncoding)
end Q
namespace Compose
export Holant.LocalDrafts.RemoteWork.PlatonicExits.PhysicalCost (composeControlled)
end Compose
set_option backward.isDefEq.respectTransparency false
variable {K : Type} [Field K] [Algebra ℚ K] {d : ℕ}
variable (F : FixedField K d) (M : Signature K 4) (i : Fin 3) (p : K)

def normalized : Signature K 4 := AntiselfdualNormalize.normalized (P.normalized M i)

def query (r : Q.TargetInput) : Q.TargetInput :=
  A.query M i (T.query (P.normalized M i) 3 r)

theorem query_counts (r : Q.TargetInput) :
    (query M i r).val.vertices.length=2*r.val.vertices.length ∧
    (query M i r).val.edges.length=r.val.edges.length+2*r.val.vertices.length := by
  have hp := A.query_counts M i (T.query (P.normalized M i) 3 r)
  have ht := T.query_counts (P.normalized M i) 3 r
  exact ⟨hp.1.trans ht.1,hp.2.trans ht.2⟩

theorem query_value (h : T.Applicable (P.normalized M i) 3 p) (r : Q.TargetInput) :
    T.value M (query M i r)=p^occurrences 0 r.val*T.value (normalized M i) r := by
  change A.value M (A.query M i (T.query (P.normalized M i) 3 r))=_
  rw [A.query_value]
  simp only [one_pow,one_mul]
  exact T.query_value (P.normalized M i) 3 p h r

def source (h : T.Applicable (P.normalized M i) 3 p) :
    LengthControlledOracleReduction Q.targetEncoding F.encoding Q.targetEncoding F.encoding
      (T.value (normalized M i)) (T.value M) :=
  Compose.composeControlled (T.source F (P.normalized M i) 3 p h) (A.source F M i)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseExceptionalStageAccess
