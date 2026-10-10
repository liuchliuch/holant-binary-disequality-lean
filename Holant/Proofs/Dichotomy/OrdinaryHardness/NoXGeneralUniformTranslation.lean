import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSignedRowsUniformOdd
import Holant.Proofs.Dichotomy.OrdinaryHardness.NoXReciprocalMixedProjectionCore

/-! Coordinate translation preserves the octic Affine class. The proof is
only a semantic gauge identity; it never supplies a physical sign gate. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralUniformTranslation
open Holant Holant.Tractable Holant.Tractable.AffinePhase Holant.Tractable.TwoTranslate
open OrdinaryNegativeSignedPortsCore (Port word)
open scoped BigOperators
namespace U
export OrdinaryNegativeAffineRankOne (uniform)
export OrdinaryNegativeSignedRowsUniform (product)
end U
namespace C
export NoXReciprocalMixedProjectionCore (logical)
end C
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 700000
set_option Elab.async false
variable {n : ℕ} (sign : Fin n→Bool)

def ports : Fin n→Port n := fun j=>.inr (j,sign j)

theorem affine_map : IsAffineMap (C.logical sign) := by
  intro x y
  funext j
  cases hs : sign j <;> cases hx : x j <;> cases hy : y j <;>
    simp [C.logical,AffinePhase.xor,AffinePhase.origin,hs,hx,hy]

theorem involution (z : Fin n→Bool) : C.logical sign (C.logical sign z)=z := by
  funext j
  simp [C.logical]

theorem word_value (z : Fin n→Bool) : word (ports sign) z=C.logical sign z := rfl

theorem count (j : Fin n) : OrdinaryNegativeSignedPortsIncidence.bundleSize (ports sign) j=1 := by
  simp [OrdinaryNegativeSignedPortsIncidence.bundleSize,ports]

theorem uniform_affine (f : Signature AlgebraicComplex n) (ha : Affine (U.uniform f)) :
    Affine (U.uniform (fun z=>f (C.logical sign z))) := by
  have odd : ∀j,Odd (∑_i : Fin 1,OrdinaryNegativeSignedPortsIncidence.bundleSize (ports sign) j) := by
    intro j
    simp only [Fin.sum_univ_one,count]
    decide
  have one (g : Signature AlgebraicComplex n) :
      OrdinaryNegativeSignedRowsUniform.product (fun _i : Fin 1=>g) (fun _i=>ports sign)=
        (fun z=>g (C.logical sign z)) := by
    funext z
    change (∏_i : Fin 1,g (word (ports sign) z))=_
    rw [Fin.prod_univ_one,word_value]
  have h:= OrdinaryNegativeSignedRowsUniformOdd.affine_iff
    (fun _i : Fin 1=>f) (fun _i=>ports sign) odd
  rw [one,one] at h
  exact h.mp (ha.precompose (C.logical sign) (affine_map sign))

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoXGeneralUniformTranslation
end
