import Holant.Proofs.Hardness.ComplexPlaneThreeSupportData
import Holant.Proofs.Hardness.BinaryCSPProgrammeNative
import Holant.Proofs.Hardness.BinaryThreeSupportProgrammeSupport

/-! The internally normalized three-support tensor is evaluated in its actual
original generated field. Its Boolean kernel is canonical NAND support; all
three retained weights and the final target presentation are explicit. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportField
open Computability Holant Holant.Algebraic Holant.Complexity
namespace D
export ComplexPlaneThreeSupportData
  (Plane ExactlyThree output output_algebraic output_lift output_eo output_corners normalizedBinary normalized_entries)
end D
namespace C
export EOBinaryPlaneCore (compress lift word compress_lift lift_compress)
end C
namespace O
export Holant.LocalDrafts.Hardness.EightVertexNonexception.Source
  (field fieldSignature fieldSignature_value presentation targetEncoding targetValue TargetInput target_value_exact)
end O
set_option backward.isDefEq.respectTransparency false
variable {L : Type} [Field L] [Algebra ℚ L]
variable (M : Signature L 4) (hp : D.Plane M) (he : DenseEOUnitLocal.EOSupport M) (ht : D.ExactlyThree M)

abbrev signature := D.output M hp he ht
abbrev field := O.field (signature M hp he ht)
local instance fieldAlgebra : Algebra ℚ (field M hp he ht) := (field M hp he ht).algebra'
abbrev fieldSignature := O.fieldSignature (signature M hp he ht)

def binary : Signature (field M hp he ht) 2 := C.compress (fieldSignature M hp he ht)
def kernel (x y : Bool) : field M hp he ht := binary M hp he ht ![x,y]

theorem coe_binary (z : Fin 2→Bool) :
    (binary M hp he ht z : L)=D.normalizedBinary M hp he ht z := by
  change C.compress (signature M hp he ht) z=_
  rw [signature,D.output_lift,C.compress_lift]

theorem binary_zero (z : Fin 2→Bool) : binary M hp he ht z=0 ↔ D.normalizedBinary M hp he ht z=0 := by
  constructor
  · intro h
    rw [←coe_binary M hp he ht z,h]
    rfl
  · intro h
    apply Subtype.ext
    change (binary M hp he ht z : L)=0
    rw [coe_binary,h]

theorem canonical : BinaryThreeSupportWeights.Canonical (binary M hp he ht) := by
  have hh := D.normalized_entries M hp he ht
  exact ⟨fun h=>hh.1 ((binary_zero M hp he ht _).mp h),
    fun h=>hh.2.1 ((binary_zero M hp he ht _).mp h),
    fun h=>hh.2.2.1 ((binary_zero M hp he ht _).mp h),
    (binary_zero M hp he ht _).mpr hh.2.2.2⟩

def weightA : field M hp he ht := kernel M hp he ht false false
def weightB : field M hp he ht := kernel M hp he ht false true
def weightC : field M hp he ht := kernel M hp he ht true false

theorem weights_nonzero : weightA M hp he ht≠0 ∧ weightB M hp he ht≠0 ∧ weightC M hp he ht≠0 :=
  ⟨(canonical M hp he ht).1,(canonical M hp he ht).2.1,(canonical M hp he ht).2.2.1⟩

theorem spectrum (x y : Bool) : kernel M hp he ht x y=0 ∨
    kernel M hp he ht x y=weightA M hp he ht ∨ kernel M hp he ht x y=weightB M hp he ht ∨
    kernel M hp he ht x y=weightC M hp he ht := by
  cases x <;> cases y
  · exact .inr (.inl rfl)
  · exact .inr (.inr (.inl rfl))
  · exact .inr (.inr (.inr rfl))
  · exact .inl (canonical M hp he ht).2.2.2

theorem signature_kernel : BinaryCSPProgrammeNative.signature (kernel M hp he ht)=binary M hp he ht := by
  funext z
  change binary M hp he ht ![z 0,z 1]=binary M hp he ht z
  congr 1
  funext i
  fin_cases i <;> rfl

theorem field_lift : fieldSignature M hp he ht=C.lift (BinaryCSPProgrammeNative.signature (kernel M hp he ht)) := by
  rw [signature_kernel]
  apply Eq.symm
  apply C.lift_compress
  · intro x hx
    apply (Holant.LocalDrafts.Hardness.EightVertexNonexception.Source.fieldSignature_eq_zero _ _).mpr
    exact D.output_eo M hp he ht x hx
  · apply (Holant.LocalDrafts.Hardness.EightVertexNonexception.Source.fieldSignature_eq_zero _ _).mpr
    exact (D.output_corners M hp he ht).1
  · apply (Holant.LocalDrafts.Hardness.EightVertexNonexception.Source.fieldSignature_eq_zero _ _).mpr
    exact (D.output_corners M hp he ht).2

theorem support_eq_nand (r : BinaryCSPProgrammeCore.Raw) :
    BinaryCSPProgrammeMachine.support (kernel M hp he ht) r=
      BinaryThreeSupportStarMachine.targetValue (K:=field M hp he ht) r :=
  BinaryThreeSupportProgrammeSupport.support_eq_nand (binary M hp he ht) (canonical M hp he ht) r

variable (halg : ∀x,IsAlgebraic ℚ (M x))
abbrev presentation := O.presentation (signature M hp he ht) (D.output_algebraic M halg hp he ht)

theorem target_value (r : O.TargetInput) :
    BinaryCSPProgrammeNative.targetValue (presentation M hp he ht halg) (fieldSignature M hp he ht) r=
      O.targetValue (signature M hp he ht) (D.output_algebraic M halg hp he ht) r := by
  rw [BinaryCSPProgrammeNative.target_semantics]
  apply Subtype.ext
  rw [O.target_value_exact]
  change ((field M hp he ht).subtype ((r.val.realize r.property
    (fun _=>fieldSignature M hp he ht) (fun _=>Signature.disequality)).denote Fin.elim0))=_
  rw [←Network.denote_map (field M hp he ht).subtype]
  apply congrFun (Network.denote_congr (r.val.shape r.property) _ _ _ _ ?_ ?_) Fin.elim0
  · intro v x
    exact O.fieldSignature_value (signature M hp he ht) x
  · intro e x y
    cases x <;> cases y <;> rfl

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.ComplexPlaneThreeSupportField
