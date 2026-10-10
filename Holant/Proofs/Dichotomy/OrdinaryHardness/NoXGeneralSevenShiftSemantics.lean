import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralSevenShiftPlan
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXGeneralOddTernaryAnti

/-! The checked three-pin/equal-pair plan has exactly one surviving
internal assignment at each off-diagonal input and none on the diagonal.
The two actual old-row values are retained as nonzero anti weights. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftSemantics
open Holant Holant.Tractable
namespace P
export NoXGeneralSevenShiftPlan (classIndex representative pin order input wire NonDual nonDual_iff_index same_support support)
end P
namespace C
export NoXReciprocalMixedProjectionCore (logical)
export OrdinaryNegativeSparseMixingAlpha (codeSeven)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 900000
set_option Elab.async false
variable {K : IntermediateField ℚ AlgebraicComplex} {s : ℕ} {b : ℕ→ℕ}
variable (H : (j : Fin s)→Signature K (b j.val))
variable (row : OrdinaryNegativeXUniversalResource.OddResource (s:=s) b 7)
variable (sign : Fin 7→Bool)
variable (support : ∀z,row.ambient H z≠0 ↔ ∃x : Fin 3→Bool,C.logical sign z=C.codeSeven x)
variable (nondual : P.NonDual sign)

include support nondual in
theorem wire_support (t : Bool) (x : Fin 2→Bool) :
    row.signature H (P.wire (P.classIndex sign) t x)≠0 ↔ x 0≠x 1 ∧ t=x 0:=by
  have nonzero : row.signature H (P.wire (P.classIndex sign) t x)≠0 ↔
      row.ambient H (P.wire (P.classIndex sign) t x)≠0:=Subtype.coe_ne_coe.symm
  rw [nonzero,support,P.same_support]
  have guards:=(P.nonDual_iff_index sign).mp nondual
  exact P.support (P.classIndex sign) guards.1 guards.2 t x

def left : K:=row.signature H (P.wire (P.classIndex sign) false ![false,true])
def right : K:=row.signature H (P.wire (P.classIndex sign) true ![true,false])
def binary : Signature K 2:=fun x=>row.signature H (P.wire (P.classIndex sign) false x)+
  row.signature H (P.wire (P.classIndex sign) true x)

include support nondual in
theorem left_nonzero : left H row sign≠0:=
  (wire_support H row sign support nondual false ![false,true]).mpr (by decide)

include support nondual in
theorem right_nonzero : right H row sign≠0:=
  (wire_support H row sign support nondual true ![true,false]).mpr (by decide)

include support nondual in
theorem zero (t : Bool) (x : Fin 2→Bool) (off : ¬(x 0≠x 1 ∧ t=x 0)) :
    row.signature H (P.wire (P.classIndex sign) t x)=0:=
  not_ne_iff.mp ((wire_support H row sign support nondual t x).not.mpr off)

include support nondual in
theorem anti : binary H row sign=NoXWeightedAntiSigned.anti (left H row sign) (right H row sign):=by
  funext x
  have hx : x=![x 0,x 1]:=by funext i;fin_cases i <;> rfl
  rw [hx]
  cases h0 : x 0 <;> cases h1 : x 1
  · rw [binary,zero H row sign support nondual false ![false,false] (by decide),
      zero H row sign support nondual true ![false,false] (by decide)]
    simp [NoXWeightedAntiSigned.anti]
  · rw [binary,zero H row sign support nondual true ![false,true] (by decide),add_zero]
    rfl
  · rw [binary,zero H row sign support nondual false ![true,false] (by decide),zero_add]
    rfl
  · rw [binary,zero H row sign support nondual false ![true,true] (by decide),
      zero H row sign support nondual true ![true,true] (by decide)]
    simp [NoXWeightedAntiSigned.anti]

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralSevenShiftSemantics
end
