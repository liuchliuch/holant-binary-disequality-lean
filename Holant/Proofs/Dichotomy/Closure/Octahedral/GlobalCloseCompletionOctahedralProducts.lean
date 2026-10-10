import Holant.Proofs.Dichotomy.Closure.Octahedral.GlobalCloseCompletionOctahedralModels

/-! Reuse the already kernel-checked literal O multiplication dictionary.
The standard matrices have the same ordered representatives and exact scalar,
so the scalar-field product theorem follows by the faithful complex embedding. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Products
open Holant.Certificates Holant.Certificates.OctahedralSeparator

def productIndex (i j : Fin 24) : Fin 24 := RainbowOrbit.productIndex .octahedral i j
def productScale (i j : Fin 24) : Scalar := (RainbowOrbit.productScale .octahedral i j : ℤ)

theorem productScale_nonzero (i j : Fin 24) : productScale i j≠0 :=
  Int.cast_ne_zero.mpr (RainbowOrbit.raw_certificate .octahedral i j).1

theorem standard_product (i j : Fin 24) :
    mm (standard i) (standard j)=ms (productScale i j) (standard (productIndex i j)) := by
  apply complexMatrix_injective
  have representative (k : Fin 24) :
      RainbowOrbit.representative .octahedral k=complexMatrix (standard k) :=
    RainbowOrbit.octahedralRaw_standard k
  have scale : embed (productScale i j)=(RainbowOrbit.productScale .octahedral i j : ℂ) := by
    change embedding (RainbowOrbit.productScale .octahedral i j : ℤ)=_
    exact map_intCast embedding _
  rw [complexMatrix_mm,complexMatrix_ms,scale,←representative,←representative,←representative]
  exact RainbowOrbit.mul_exact .octahedral i j

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.GlobalCloseCompletionOctahedralGeometry.Products
end
