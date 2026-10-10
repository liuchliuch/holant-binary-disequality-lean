import Holant.Tractable.Conformal
import Holant.Tractable.Downward

/-! The complete seven-clause criterion returns through one common native
basis and whole-family inclusion. No matching or EO exception is discarded. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIConformalReturn
open Holant Holant.Tractable

theorem criterion (F H : SignatureFamily AlgebraicComplex) (B : InvertibleKernel)
    (native : Kernel.pullback Signature.disequality B.matrix=Signature.disequality)
    (included : familyAction B.symm F⊆H)
    (positive : Tract (familyAction sourceKBasis H)) : Tract (familyAction sourceKBasis F) := by
  have conformal : XConformal B:=⟨1,one_ne_zero,by simpa using native⟩
  apply (xConformal_tract_iff conformal.symm F).mpr
  exact positive.mono_family (Set.image_mono included)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIConformalReturn
end
