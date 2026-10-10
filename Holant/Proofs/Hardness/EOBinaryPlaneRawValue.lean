import Holant.Proofs.Hardness.EOBinaryPlaneRaw
import Holant.Proofs.Hardness.GeneralCSPUnusedNat

/-! Exact original-field answer for the physical raw binary-CSP tape, including
all unused declared variables. The only correction is their explicit power of 2. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRawValue
open Holant Holant.Complexity
namespace R
export EOBinaryPlaneRaw (scope value value_scope query)
end R
namespace U
export GeneralCSPUnused (unusedCount scan_cycle_value unusedVariables unusedCount_list)
end U
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source (field targetValue)
end O
set_option backward.isDefEq.respectTransparency false

def unused (r : BinaryCSPProgrammeCore.Raw) (hw : r.WellFormed) : ℕ := U.unusedCount (R.scope r hw)

theorem unused_list (r : BinaryCSPProgrammeCore.Raw) (hw : r.WellFormed) :
    unused r hw=(U.unusedVariables (R.scope r hw)).length := U.unusedCount_list _

/-- Direct natural-address correction used by the physical programme. -/
theorem unused_natural (r : BinaryCSPProgrammeCore.Raw) (hw : r.WellFormed) :
    unused r hw=(GeneralCSPUnusedNat.unused r.variables (EOBinaryPlaneRaw.addresses r)).length := by
  rw [unused,GeneralCSPUnusedNat.unusedCount_filter,EOBinaryPlaneRaw.addresses_scope]

theorem query_value {K : Type*} [CommSemiring K] (f : Signature K 2)
    (r : BinaryCSPProgrammeCore.Raw) (hw : r.WellFormed) :
    R.value f r=(2 : K)^unused r hw*
      ((R.query r hw).val.realize (R.query r hw).property (fun _=>EOBinaryPlaneCore.lift f)
        (fun _=>Signature.disequality)).denote Fin.elim0 := by
  rw [R.value_scope f r hw,U.scan_cycle_value]
  rw [R.query,EOBinaryPlaneRecords.query_denote,EOBinaryPlaneCycles.denote_lift]
  rfl

/-- The final oracle is the unchanged original signature, with its own exact
coefficient-field codec. Empty graphs retain all declared-variable factors. -/
theorem original_value {L : Type} [Field L] [Algebra ℚ L]
    (M : Signature L 4) (halg : ∀x,IsAlgebraic ℚ (M x))
    (he : DenseEOUnitLocal.EOSupport M)
    (hb : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries M).b=0)
    (hy : (Holant.LocalDrafts.Hardness.EightVertexNonexception.entries M).y=0)
    (r : BinaryCSPProgrammeCore.Raw) (hw : r.WellFormed) :
    R.value (EOBinaryPlaneCore.compress M) r=(2 : L)^unused r hw*
      ((O.targetValue M halg (R.query r hw) : O.field M) : L) := by
  rw [R.value_scope _ r hw,U.scan_cycle_value]
  rw [R.query,EOBinaryPlaneRecords.original_value M halg he hb hy]
  rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneRawValue
