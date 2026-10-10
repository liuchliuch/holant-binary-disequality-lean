import Holant.Certificates.EqualityQuaternary.KleinFiniteModel

noncomputable section
namespace Holant.Certificates.EqualityQuaternary.Klein.Finite
open Holant Holant.Marked Holant.Tractable
def planeTensor (kind : Kind) (j : Fin (planeCount kind)) (r : Fin 4) : Signature Scalar 4 :=
  fun w => ∑ col : Fin 16,embed (planes kind j r col)*basisTensor kind (firstLabel col) (secondLabel col) w

def planeTensorQ (kind : Kind) (j : Fin (planeCount kind)) (r : Fin 4) (w : Fin 4 → Bool) : Q :=
  ∑ col : Fin 16,planes kind j r col*basisTensorQ kind (firstLabel col) (secondLabel col) w

theorem planeTensor_embed (kind : Kind) (j : Fin (planeCount kind)) (r : Fin 4) (w : Fin 4 → Bool) :
    planeTensor kind j r w=embed (planeTensorQ kind j r w) := by
  simp [planeTensor,planeTensorQ,basisTensor,basisTensorQ,E]


end Holant.Certificates.EqualityQuaternary.Klein.Finite
