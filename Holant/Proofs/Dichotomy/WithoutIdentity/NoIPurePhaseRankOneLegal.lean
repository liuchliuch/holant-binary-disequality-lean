import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankOneCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseLegalPins

/-! Rank one has one signed incidence. Uniform weight modulo four forces
that actual column to be legal, so every root-sixteen correction is Affine.
The argument also transfers through an actual pure pinning of the original
row and excludes a bad rank-one minimum witness. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankOneLegal
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport
open NoIPurePhaseRecipeFactor (Port word incidence)
open NoIPurePhaseLegalAffine (LegalAffine)
open scoped BigOperators
namespace P
export NoIPurePhaseRankOneCore (one one_value)
end P
namespace U
export NoIPureClosedUniformMinimal (twist twistChart UniformPinWitness)
end U
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n}

theorem column_zero (D : SystematicSupport f 1)
    (uniform : NoIPureChargeTwoFamily.UniformFour f) :
    ∀j,incidence (P.one D) j%4=0 :=
  NoIPurePhaseRankOneCore.column_zero D (P.one D) (P.one_value D) uniform

theorem affine (D : SystematicSupport f 1)
    (uniform : NoIPureChargeTwoFamily.UniformFour f) (legal : LegalAffine f)
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1) : Affine (U.twist r f) :=
  NoIPurePhaseRankOneCore.affine D (P.one D) (P.one_value D) uniform legal r rn root

/-- All hypotheses refer to the original row; the actual pin map is retained
in the minimum-rank witness and never replaced by a supplied logical gate. -/
theorem pin_impossible {K : IntermediateField ℚ AlgebraicComplex}
    (f : Signature K n)
    (uniform : NoIPureChargeTwoFamily.UniformFour (fun x=>(f x : AlgebraicComplex)))
    (legal : LegalAffine (fun x=>(f x : AlgebraicComplex)))
    (r : AlgebraicComplex) (rn : r≠0) (root : r^16=1)
    (W : U.UniformPinWitness r f 1) : False := by
  have lp : LegalAffine (OrdinaryNegativeSparseMinimalRank.row f W.pins):=
    NoIPurePhaseLegalPins.pin (fun x=>(f x : AlgebraicComplex)) legal W.pins W.pure
  have up : NoIPureChargeTwoFamily.UniformFour (OrdinaryNegativeSparseMinimalRank.row f W.pins):=
    NoIPurePhasePinCompose.uniform_four (fun x=>(f x : AlgebraicComplex)) uniform W.pins W.pure
  exact W.bad (affine W.chart up lp r rn root)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankOneLegal
end
