import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoScalar
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankTwoCore
import Holant.Proofs.Dichotomy.WithoutIdentity.NoIPurePhaseRankThreeCore

/-! Three unchanged binary rows upgrade the non-Affine interaction to a
nontrivial cubic sign on their actual semantic three-coordinate pullback. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoCubic
open Holant Holant.Tractable Holant.Tractable.AffinePhase
namespace B
export Holant.LocalDrafts.RemoteWork.HardnessChainV1.EOBinaryPlaneClassification
  (Full CommonFourth)
end B
namespace A
export NoIPurePhaseRankThreeCore (cubicRatio origin_cube_ratio)
end A
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1000000
set_option Elab.async false

def upgrade (h : Signature AlgebraicComplex 2) : Signature AlgebraicComplex 3:=
  fun x=>h ![x 0,x 1^^x 2]*h ![x 0,x 1]*h ![x 0,x 2]

theorem upgrade_full (h : Signature AlgebraicComplex 2) (full : B.Full h) :
    ∀x,upgrade h x≠0:=fun x=>mul_ne_zero (mul_ne_zero (full _) (full _)) (full _)

theorem cubic_formula (h : Signature AlgebraicComplex 2) (full : B.Full h) :
    A.cubicRatio (upgrade h)=
      (h ![false,true]*h ![true,false])^2/(h ![false,false]*h ![true,true])^2 := by
  norm_num [A.cubicRatio,upgrade]
  field_simp [full ![false,false],full ![false,true],full ![true,false],full ![true,true]]

theorem cubic_negative (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬Affine h) : A.cubicRatio (upgrade h)= -1 := by
  rw [cubic_formula h full,NoIPurePhaseRankTwoScalar.negative_cross h full fourth bad]
  have hn:(h ![false,true]*h ![true,false])^2≠0:=
    pow_ne_zero 2 (mul_ne_zero (full _) (full _))
  rw [div_neg,div_self hn]

theorem not_affine (h : Signature AlgebraicComplex 2) (full : B.Full h)
    (fourth : B.CommonFourth h) (bad : ¬Affine h) : ¬Affine (upgrade h) := by
  intro affine
  have cube:=thirdTrivial_of_affine (upgrade_full h full) affine
    (origin 3) (basis 0) (basis 1) (basis 2)
  rw [A.origin_cube_ratio,cubic_negative h full fourth bad] at cube
  norm_num at cube

theorem of_minimal {n : ℕ} {f : Signature AlgebraicComplex n}
    (D : OrdinaryNegativeAffineSystematicSupport.SystematicSupport f 2)
    (bad : ¬Affine f)
    (faces : ∀i : Fin 2,∀z : Word 2,Affine (OrdinaryNegativeSparseRankDescent.minor D {i} z)) :
    ¬Affine (upgrade D.reduced) :=
  not_affine D.reduced D.reduced_full (NoIPurePhaseRankTwoSource.faces_fourth D faces)
    (NoIPureClosedMinimal.nonAffine_reduced D bad)


end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.NoIPurePhaseRankTwoCubic
end
