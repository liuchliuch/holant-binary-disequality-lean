import Holant.Proofs.Hardness.EOQuaternarySupportCases

/-! Zero-reflecting transport of original algebraic-complex support predicates.
The original signature itself, not a chosen transformed field, is transported. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryComplexTransport
open Holant Holant.Tractable Holant.Algebraic
namespace S
export EOQuaternarySparseDispatch (complex complex_algebraic)
end S
set_option backward.isDefEq.respectTransparency false

theorem zero_iff (M : Signature AlgebraicComplex 4) (x : Fin 4→Bool) :
    M x=0 ↔ S.complex M x=0 := by
  simp [EOQuaternarySparseDispatch.complex]

theorem dense (M : Signature AlgebraicComplex 4) (h : DenseEOUnitLocal.NonzeroMiddle M) :
    DenseEOUnitLocal.NonzeroMiddle (S.complex M) := by
  rcases h with ⟨hb,hc,hd,hw,hz,hy⟩
  exact ⟨fun h=>hb (Subtype.ext h),fun h=>hc (Subtype.ext h),
    fun h=>hd (Subtype.ext h),fun h=>hw (Subtype.ext h),
    fun h=>hz (Subtype.ext h),fun h=>hy (Subtype.ext h)⟩

theorem five (M : Signature AlgebraicComplex 4) (h : FiveSupportEOOrdering.ExactlyFive M) :
    FiveSupportEOOrdering.ExactlyFive (S.complex M) :=
  (FiveSupportEOOrdering.exactlyFive_congr (zero_iff M)).mp h

theorem three (M : Signature AlgebraicComplex 4)
    (h : (EOQuaternarySparseTract.support M).card=3) :
    ComplexPlaneThreeSupportData.ExactlyThree (S.complex M) := by
  change (ComplexPlaneThreeSupportData.support (S.complex M)).card=3
  rw [EOQuaternarySupportCases.complex_support_card]
  exact h

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOQuaternaryComplexTransport
