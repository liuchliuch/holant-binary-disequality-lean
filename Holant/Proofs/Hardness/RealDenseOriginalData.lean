import Holant.Proofs.Hardness.RealDenseSignTwistStageAccess
import Holant.Proofs.Hardness.DenseEOPairedSource

/-! The exceptional sign twist stays in the original coefficient-generated
field. The physical scale is b+c in that same field; there is no adjunction or
new signature dictionary supplied to the oracle. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseOriginalData
open Holant Holant.Algebraic Holant.Complexity
open Holant.LocalDrafts.Hardness.EightVertexNonexception
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_value fieldSignature_eq_zero presentation
   TargetInput targetEncoding targetValue target_value_exact)
end O
namespace N
export AntiselfdualNormalize (normalized)
end N
namespace A
export RealDenseSignTwistStageAccess (Applicable value source signatures kernels)
end A
set_option backward.isDefEq.respectTransparency false
variable (M : Signature ℝ 4)
local instance fieldAlgebra : Algebra ℚ (O.field M) := (O.field M).algebra'
local instance fieldCharZero : CharZero (O.field M) := algebraRat.charZero (O.field M)

def scale : O.field M := (entries (O.fieldSignature M)).b+(entries (O.fieldSignature M)).c

theorem scale_nonzero (h : RealDenseSignTwist.Exceptional M) : scale M≠0 := by
  intro hz
  apply RealDenseSignTwist.exceptional_scale_nonzero M h
  exact congrArg (fun x : O.field M=>(x : ℝ)) hz

theorem field_cap (h : RealDenseSignTwist.Exceptional M) :
    RealDenseSignTwist.AntisymmetricCap (O.fieldSignature M) 3 (scale M) := by
  constructor
  · rfl
  · apply Subtype.ext
    exact (RealDenseSignTwist.exceptional_cap M h).2

theorem field_applicable (he : DenseEOUnitLocal.EOSupport M)
    (h : RealDenseSignTwist.Exceptional M) :
    A.Applicable (O.fieldSignature M) 3 (scale M) where
  even := DenseEOUnitLocal.even _ (DenseEOPairedSource.field_eo M he)
  cap := field_cap M h
  nonzero := scale_nonzero M h

theorem target_value (halg : ∀x,IsAlgebraic ℚ (M x)) (r : O.TargetInput) :
    A.value (O.fieldSignature M) r=O.targetValue M halg r := by
  apply Subtype.ext
  rw [O.target_value_exact]
  change ((O.field M).subtype
    ((r.val.realize r.property (A.signatures (O.fieldSignature M)) A.kernels).denote Fin.elim0))=_
  rw [←Network.denote_map (O.field M).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    exact O.fieldSignature_value M x
  · intro e x y
    cases x <;> cases y <;> rfl

def source (halg : ∀x,IsAlgebraic ℚ (M x)) (he : DenseEOUnitLocal.EOSupport M)
    (h : RealDenseSignTwist.Exceptional M) :=
  A.source (O.presentation M halg) (O.fieldSignature M) 3 (scale M) (field_applicable M he h)

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.RealDenseOriginalData
