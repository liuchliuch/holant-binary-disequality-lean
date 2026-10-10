import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoSupport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankTwoAlphaCore

/-! Transfer the exact reduced rank-two octic class to the actual ternary
signed-port restriction. The original third bundle enforces codeThree and
all coefficients, including the original scale, stay unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoAlphaLift
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeRankTwoSupport
namespace A
export OrdinaryNegativeSparseMixingAlpha (phaseThree twist twist_action codeThree)
end A
namespace U
export OrdinaryNegativeAffineRankOne (uniform uniform_support uniform_square)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 2)
variable (present : 0<OrdinaryNegativeSignedPortsIncidence.bundleSize (OrdinaryNegativeRankTwoPorts.port D) 2)

/-- Uniform twisting leaves the computed ternary support chart unchanged. -/
def chart : SystematicSupport (U.uniform (essential D)) 2 where
  ports := (OrdinaryNegativeRankTwoSupport.chart D present).ports
  injective := (OrdinaryNegativeRankTwoSupport.chart D present).injective
  encode := (OrdinaryNegativeRankTwoSupport.chart D present).encode
  affine := (OrdinaryNegativeRankTwoSupport.chart D present).affine
  free := (OrdinaryNegativeRankTwoSupport.chart D present).free
  supported z := (U.uniform_support (essential D) _).mpr
    ((OrdinaryNegativeRankTwoSupport.chart D present).supported z)
  covers z hz := (OrdinaryNegativeRankTwoSupport.chart D present).covers z
    ((U.uniform_support (essential D) z).mp hz)

theorem reduced_value (z : Fin 2→Bool) :
    (chart D present).reduced z=A.phaseThree z*D.reduced z := by
  unfold SystematicSupport.reduced chart OrdinaryNegativeRankTwoSupport.chart
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,essential]
  rw [OrdinaryNegativeRankTwoPorts.word_code]
  rfl

include present in
/-- Reduced alpha classification suffices because the actual ternary row
has exactly the proved affine code support, including all off-support zeros. -/
theorem alpha (squareF : Affine (fun z=>f z^2))
    (reducedAlpha : Affine (fun z=>A.phaseThree z*D.reduced z)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (essential D)) := by
  have sq := U.uniform_square (essential D) (square D squareF)
  have nonzero : U.uniform (essential D)≠0 := by
    intro hz
    exact (chart D present).supported (fun _=>false) (congrFun hz _)
  obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system _ sq nonzero
  have reducedGood : Affine (chart D present).reduced := by
    have he : (chart D present).reduced=(fun z=>A.phaseThree z*D.reduced z) := funext (reduced_value D present)
    rwa [he]
  have good := (chart D present).affine_of_reduced S hS reducedGood
  rw [A.twist_action]
  convert good using 1
  funext z
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,A.twist]

include present in
/-- On the genuine minimal rank-two branch, the ternary alpha class is
proved internally; it is not a premise supplied by a classifier backend. -/
theorem alpha_of_minimal (squareF : Affine (fun z=>f z^2)) (nonzero : f≠0) (bad : ¬Affine f)
    (minimal : ∀S : Finset (Fin 2),S.card<2→∀z : Fin 2→Bool,
      Affine (OrdinaryNegativeSparseRankDescent.minor D S z)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (essential D)) :=
  alpha D present squareF
    (OrdinaryNegativeRankTwoAlphaCore.minimal_phaseThree_affine D squareF nonzero bad minimal)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeRankTwoAlphaLift
end
