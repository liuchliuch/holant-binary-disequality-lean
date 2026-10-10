import Holant.Complexity.EncodedHolantOutputSize

/-! Exact coefficient tables for a literal native-X alphabet, independent
of interpolation and source extension. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
open Holant Holant.Algebraic Holant.Complexity
variable {K : Type} [Field K] [Algebra ℚ K] {s degree : ℕ} {a : ℕ→ℕ}
variable (H : (i : Fin s)→Signature K (a i.val)) (F : FixedField K degree)
def base : ExactSignatureTables degree s 1 a where
  vertex i x:=F.decode.symm (H i x)
  edge _ x y:=F.decode.symm (Signature.disequality x y)
end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NativeAntiTargetSource
end
