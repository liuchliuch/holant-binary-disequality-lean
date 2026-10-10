import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportData
import Holant.Proofs.Hardness.EOBinaryPlaneFullSupportKernelSource

/-! Internally generated original and conjugate-common presentations for the
selected full-support plane. The original normalized signature is exactly the
lift of the four original compressed field elements. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportField
open Holant Holant.Tractable Holant.Algebraic Holant.Complexity
namespace D
export EOBinaryPlaneFullSupportData
  (ExactlyFour signature binary binary_full signature_algebraic algebraic coefficient_obstructions)
end D
namespace P
export ComplexPlaneThreeSupportData (Plane planeIndex plane_zero)
end P
namespace C
export EOBinaryPlaneCore (compress lift lift_compress normalized_eo normalized_corners)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_value fieldSignature_eq_zero presentation targetEncoding targetValue TargetInput target_value_exact)
end O
namespace Common
export EOBinaryPlaneOriginalCommon (field presentation into)
end Common
namespace Images
export EOBinaryPlaneFullSupportImages (commonAmbient original_common_star)
end Images
namespace V
export RealDenseSignTwistStageAccess (value)
end V
namespace S
export EOBinaryPlaneFullSupportKernelSource (a b c dval)
end S
set_option backward.isDefEq.respectTransparency false
variable (M : Signature ℂ 4) (hp : P.Plane M)

abbrev signature := D.signature M hp
abbrev field := O.field (signature M hp)
local instance fieldAlgebra : Algebra ℚ (field M hp) := (field M hp).algebra'
abbrev fieldSignature := O.fieldSignature (signature M hp)
def binary : Signature (field M hp) 2 := C.compress (fieldSignature M hp)
abbrev common := Common.field (signature M hp)
local instance commonAlgebra : Algebra ℚ (common M hp) := (common M hp).algebra'
def into : field M hp→ₐ[ℚ]common M hp := Common.into (signature M hp)
def ambient : common M hp→+*ℂ := Images.commonAmbient (signature M hp)

theorem ambient_star : ∀x,ambient M hp (star x)=star (ambient M hp x) :=
  Images.original_common_star (signature M hp)

theorem binary_value (z : Fin 2→Bool) : (binary M hp z : ℂ)=D.binary M hp z := rfl

theorem image_binary (z : Fin 2→Bool) : ambient M hp (into M hp (binary M hp z))=D.binary M hp z := rfl

variable (he : DenseEOUnitLocal.EOSupport M) (hf : D.ExactlyFour M)
include he hf in
theorem binary_full : ∀z,binary M hp z≠0 := by
  intro z hz
  exact D.binary_full M hp he hf z (congrArg Subtype.val hz)

include he in
theorem field_lift : fieldSignature M hp=C.lift (binary M hp) := by
  apply Eq.symm
  apply C.lift_compress
  · intro x hx
    apply (O.fieldSignature_eq_zero _ _).mpr
    exact C.normalized_eo M he (P.planeIndex M hp) x hx
  · apply (O.fieldSignature_eq_zero _ _).mpr
    exact (C.normalized_corners M (P.planeIndex M hp) (P.plane_zero M hp).1 (P.plane_zero M hp).2).1
  · apply (O.fieldSignature_eq_zero _ _).mpr
    exact (C.normalized_corners M (P.planeIndex M hp) (P.plane_zero M hp).1 (P.plane_zero M hp).2).2

variable (halg : ∀x,IsAlgebraic ℚ (M x))
abbrev presentation := O.presentation (signature M hp) (D.signature_algebraic M hp halg)
abbrev commonPresentation := Common.presentation (signature M hp) (D.signature_algebraic M hp halg)

include he in
theorem target_value (r : O.TargetInput) :
    V.value (C.lift (binary M hp)) r=O.targetValue (signature M hp) (D.signature_algebraic M hp halg) r := by
  rw [←field_lift M hp he]
  apply Subtype.ext
  rw [O.target_value_exact]
  change (field M hp).subtype ((r.val.realize r.property
    (fun _=>fieldSignature M hp) (fun _=>Signature.disequality)).denote Fin.elim0)=_
  rw [←Network.denote_map (field M hp).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    exact O.fieldSignature_value (signature M hp) x
  · intro e x y
    cases x <;> cases y <;> rfl

variable (hn : ¬EOTract {⟨4,D.algebraic M halg⟩})
include he hf hn in
theorem obstructions :
    EOBinaryPlaneGram.determinant (S.a (into M hp) (ambient M hp) (binary M hp))
      (S.b (into M hp) (ambient M hp) (binary M hp)) (S.c (into M hp) (ambient M hp) (binary M hp))
      (S.dval (into M hp) (ambient M hp) (binary M hp))≠0 ∧
    ¬EOBinaryPlanePositive.exceptional (S.a (into M hp) (ambient M hp) (binary M hp))
      (S.b (into M hp) (ambient M hp) (binary M hp)) (S.c (into M hp) (ambient M hp) (binary M hp))
      (S.dval (into M hp) (ambient M hp) (binary M hp)) :=
  D.coefficient_obstructions M hp he hf halg hn

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneFullSupportField
