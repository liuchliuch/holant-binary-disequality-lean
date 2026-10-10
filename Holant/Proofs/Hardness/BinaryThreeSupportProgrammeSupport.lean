import Holant.Proofs.Hardness.BinaryThreeSupportStarProgrammeCorrectness
import Holant.Proofs.Hardness.BinaryCSPProgrammeCorrectness

/-! The physical positive-power support extractor recovers the unsigned
NAND2 oracle used by the signed-star machine. No unary signature is queried. -/
noncomputable section
namespace Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportProgrammeSupport
open Holant
open scoped BigOperators
variable {K : Type} [Field K] [Algebra ℚ K]

theorem support_eq_nand (f : Signature K 2) (hf : BinaryThreeSupportWeights.Canonical f)
    (r : BinaryCSPProgrammeCore.Raw) :
    BinaryCSPProgrammeMachine.support (fun x y=>f ![x,y]) r=
      BinaryThreeSupportStarMachine.targetValue (K:=K) r := by
  classical
  unfold BinaryCSPProgrammeMachine.support BinaryThreeSupportStarMachine.targetValue
    BinaryCSPProgrammeValue.value
  apply Finset.sum_congr rfl
  intro x _
  rw [BinaryCSPProgrammeMachine.weight_product,BinaryThreeSupportWeights.support_product]
  simp only [BinaryThreeSupportWeights.support_entry f hf]
  exact (BinaryCSPProgrammeMachine.weight_product BinaryThreeSupportGates.nand r x).symm

end Holant.LocalDrafts.RemoteWork.HardnessChainV1.BinaryThreeSupportProgrammeSupport
