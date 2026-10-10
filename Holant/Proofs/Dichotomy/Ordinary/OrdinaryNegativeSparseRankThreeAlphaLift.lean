import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeSparseRankThreeSupport
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeAffineRankOne
import Holant.Proofs.Dichotomy.Ordinary.OrdinaryNegativeRankThreeAlphaCore

/-! Transfer the exact reduced rank-three octic class to the actual seven-variable
signed-port restriction. The original seven bundles enforces codeSeven and
all coefficients, including the original scale, stay unchanged. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeAlphaLift
open Holant Holant.Tractable
open OrdinaryNegativeAffineSystematicSupport OrdinaryNegativeSparseRankThreeSupport
namespace A
export OrdinaryNegativeSparseMixingAlpha (phaseSeven twist twist_action codeSeven)
end A
namespace U
export OrdinaryNegativeAffineRankOne (uniform uniform_support uniform_square)
end U
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1200000
set_option maxRecDepth 32768
set_option Elab.async false
variable {n : ℕ} {f : Signature AlgebraicComplex n} (D : SystematicSupport f 3)
variable (present : ∀j,0<OrdinaryNegativeSignedPortsIncidence.bundleSize (OrdinaryNegativeSparseRankThreePorts.port D) j)

/-- Uniform twisting leaves the computed seven-variable support chart unchanged. -/
def chart : SystematicSupport (U.uniform (essential D)) 3 where
  ports := (OrdinaryNegativeSparseRankThreeSupport.chart D present).ports
  injective := (OrdinaryNegativeSparseRankThreeSupport.chart D present).injective
  encode := (OrdinaryNegativeSparseRankThreeSupport.chart D present).encode
  affine := (OrdinaryNegativeSparseRankThreeSupport.chart D present).affine
  free := (OrdinaryNegativeSparseRankThreeSupport.chart D present).free
  supported z := (U.uniform_support (essential D) _).mpr
    ((OrdinaryNegativeSparseRankThreeSupport.chart D present).supported z)
  covers z hz := (OrdinaryNegativeSparseRankThreeSupport.chart D present).covers z
    ((U.uniform_support (essential D) z).mp hz)

theorem reduced_value (z : Fin 3→Bool) :
    (chart D present).reduced z=A.phaseSeven z*D.reduced z := by
  unfold SystematicSupport.reduced chart OrdinaryNegativeSparseRankThreeSupport.chart
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,essential]
  rw [OrdinaryNegativeSparseRankThreePorts.word_code]
  rfl

include present in
/-- Reduced alpha classification suffices because the actual seven-variable row
has exactly the proved affine code support, including all off-support zeros. -/
theorem alpha (squareF : Affine (fun z=>f z^2))
    (reducedAlpha : Affine (fun z=>A.phaseSeven z*D.reduced z)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (essential D)) := by
  have sq := U.uniform_square (essential D) (square D squareF)
  have nonzero : U.uniform (essential D)≠0 := by
    intro hz
    exact (chart D present).supported (fun _=>false) (congrFun hz _)
  obtain ⟨S,hS⟩ := OrdinaryNegativeAffineSquareSupport.exists_support_system _ sq nonzero
  have reducedGood : Affine (chart D present).reduced := by
    have he : (chart D present).reduced=(fun z=>A.phaseSeven z*D.reduced z) := funext (reduced_value D present)
    rwa [he]
  have good := (chart D present).affine_of_reduced S hS reducedGood
  rw [A.twist_action]
  convert good using 1
  funext z
  simp only [U.uniform,SymmetricBinaryPullback.localTwist_apply,Bool.true_and,A.twist]

include present in
/-- On the genuine minimal rank-three branch, the seven-variable alpha class is
proved internally; it is not a premise supplied by a classifier backend. -/
theorem alpha_of_minimal (squareF : Affine (fun z=>f z^2)) (nonzero : f≠0) (bad : ¬Affine f)
    (minimal : ∀S : Finset (Fin 3),S.card<3→∀z : Fin 3→Bool,
      Affine (OrdinaryNegativeSparseRankDescent.minor D S z)) :
    Affine ((OrdinaryNegativeOcticCommonBasis.basis true).symm.action (essential D)) :=
  alpha D present squareF
    (OrdinaryNegativeRankThreeAlphaCore.minimal_phaseSeven_affine D minimal squareF nonzero bad)

end Holant.LocalDrafts.RemoteWork.RootIntegrationV1.OrdinaryNegativeSparseRankThreeAlphaLift
end
